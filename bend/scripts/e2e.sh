#!/bin/sh
# End to end: the Bend vegeta against a Go test server (scripts/e2e-server),
# checked against Go Vegeta built from this repo. Each check prints ok or
# FAIL with what differed; the exit code is the number of failures.
#
#   sh scripts/e2e.sh            all checks
#   sh scripts/e2e.sh <pattern>  checks whose name contains pattern
set -u
here=$(cd "$(dirname "$0")/.." && pwd)
repo=$(cd "$here/.." && pwd)
sh "$here/scripts/install-bend.sh"
export PATH="$here/.build/bendhome/bin:$PATH" BEND_NO_TELEMETRY=1
b="$here/.build"
w="$b/e2e"
mkdir -p "$w"
pat=${1:-}
printf 'hello bend' > "$w/body.txt"

bend "$here/main.bend" -o "$b/vegeta" > "$w/build.out" 2>&1 || { echo "FAIL build"; cat "$w/build.out"; exit 1; }
(cd "$repo" && go build -o "$b/vegeta-go" . && go build -o "$b/e2e-server" ./bend/scripts/e2e-server) || { echo "FAIL go build"; exit 1; }

port=18321
PORT=$port "$b/e2e-server" & srv=$!
trap 'kill $srv 2>/dev/null' EXIT INT TERM
for _ in 1 2 3 4 5 6 7 8 9 10; do curl -s "http://127.0.0.1:$port/stats" > /dev/null && break; sleep 0.2; done
url="http://127.0.0.1:$port"
B="$b/vegeta"; G="$b/vegeta-go"
fail=0

run() { case "$1" in *"$pat"*) return 0;; esac; return 1; }
ok() { echo "ok   $1"; }
bad() { echo "FAIL $1: $2"; fail=$((fail+1)); }

# the outcome columns of a CSV results file, one line per result, sorted:
# code, bytes out, bytes in, error, method, url (and the body unless
# nobody is given)
outcomes() {
  python3 - "$1" "${2:-}" <<'EOF'
import csv, sys, base64
csv.field_size_limit(sys.maxsize)
rows = []
for r in csv.reader(open(sys.argv[1], newline='')):
    ts, code, lat, bout, bin_, err, body, attack, seq, method, url = r[:11]
    b = '' if sys.argv[2] == 'nobody' else base64.b64decode(body).decode('latin-1')
    # Go's dial errors name the local address where the OS gives one
    # ("dial tcp 0.0.0.0:0->IP:PORT"); the port's never do
    err = err.replace('dial tcp 0.0.0.0:0->', 'dial tcp ')
    rows.append('|'.join([code, bout, bin_, err, method, url, b]))
for x in sorted(rows):
    print(x)
EOF
}

# ---------------------------------------------------------------------
# pacing and interop
# ---------------------------------------------------------------------

if run pacing; then
  echo "GET $url/ok" | "$B" attack -rate=50 -duration=2s > "$w/pace.csv" 2> "$w/pace.err"
  n=$(wc -l < "$w/pace.csv" | tr -d ' ')
  codes=$(cut -d, -f2 "$w/pace.csv" | sort -u | tr '\n' ' ')
  if [ "$n" = 100 ] && [ "$codes" = "200 " ]; then ok "pacing: 50/s for 2s is 100 hits, all 200"
  else bad pacing "$n hits, codes $codes; $(cat "$w/pace.err")"; fi
fi

if run go-reads-csv; then
  "$G" report -type=json "$w/pace.csv" > "$w/pace.json" 2>&1
  if python3 -c "import json,sys; d=json.load(open('$w/pace.json')); sys.exit(0 if d['requests']==100 and d['success']==1 else 1)"; then
    ok "go-reads-csv: Go's report reads the Bend CSV (100 requests, all ok)"
  else bad go-reads-csv "$(head -c 400 "$w/pace.json")"; fi
fi

if run go-reads-json; then
  echo "GET $url/ok" | "$B" attack -rate=20 -duration=1s -encoding=json > "$w/j.json"
  "$G" report -type=json "$w/j.json" > "$w/j.rep" 2>&1
  if python3 -c "import json,sys; d=json.load(open('$w/j.rep')); sys.exit(0 if d['requests']==20 else 1)"; then
    ok "go-reads-json: Go's report reads the Bend JSON results"
  else bad go-reads-json "$(head -c 400 "$w/j.rep")"; fi
fi

# report on the same Go-made results: every line but the latencies (Go's
# are t-digest estimates) and the error set's order match
if run bend-reads-go; then
  echo "GET $url/ok
GET $url/500
GET $url/redirect" | "$G" attack -rate=60 -duration=1s | "$G" encode -to=csv > "$w/g.csv"
  "$G" report "$w/g.csv" | grep -v '^Latencies' > "$w/g.txt"
  "$B" report "$w/g.csv" > "$w/b.full" 2> "$w/b.err"
  grep -v '^Latencies' "$w/b.full" > "$w/b.txt"
  if diff -u "$w/g.txt" "$w/b.txt" > "$w/rep.diff"; then ok "bend-reads-go: text report on Go's results matches Go's (latencies aside)"
  else bad bend-reads-go "$(cat "$w/rep.diff" "$w/b.err")"; fi
  "$B" report -type=json "$w/g.csv" > "$w/b.json" 2>> "$w/b.err"
  "$G" report -type=json "$w/g.csv" > "$w/g.json"
  if python3 - "$w/g.json" "$w/b.json" <<'EOF'
import json, sys
g, b = json.load(open(sys.argv[1])), json.load(open(sys.argv[2]))
keys = ['requests', 'rate', 'throughput', 'success', 'status_codes', 'bytes_in', 'bytes_out', 'duration', 'wait', 'earliest', 'latest', 'end']
diff = [k for k in keys if g[k] != b[k]]
g['errors'].sort(); b['errors'].sort()
if g['errors'] != b['errors']: diff.append('errors')
for k in ['total', 'mean', 'min', 'max']:
    if g['latencies'][k] != b['latencies'][k]: diff.append('latencies.' + k)
print(diff) if diff else None
sys.exit(1 if diff else 0)
EOF
  then ok "bend-reads-go: JSON report fields match Go's (percentiles aside)"
  else bad bend-reads-go-json "fields differ"; fi
fi

# ---------------------------------------------------------------------
# the client, endpoint by endpoint: the same outcomes as Go's client
# ---------------------------------------------------------------------

same() { # name, extra flags, targets text, [nobody]
  name=$1; flags=$2; targets=$3; nb=${4:-}
  run "$name" || return 0
  printf '%s\n' "$targets" > "$w/$name.t"
  # shellcheck disable=SC2086
  "$G" attack -targets="$w/$name.t" $flags | "$G" encode -to=csv > "$w/$name.g.csv"
  # shellcheck disable=SC2086
  "$B" attack -targets="$w/$name.t" $flags > "$w/$name.b.csv" 2> "$w/$name.b.err"
  outcomes "$w/$name.g.csv" "$nb" | sort -u > "$w/$name.g"
  outcomes "$w/$name.b.csv" "$nb" | sort -u > "$w/$name.b"
  if diff -u "$w/$name.g" "$w/$name.b" > "$w/$name.diff"; then ok "$name: outcomes match Go's ($(wc -l < "$w/$name.g" | tr -d ' ') distinct)"
  else bad "$name" "$(head -20 "$w/$name.diff") $(cat "$w/$name.b.err")"; fi
}

same client-ok "-rate=20 -duration=1s" "GET $url/ok"
same client-500 "-rate=20 -duration=1s" "GET $url/500"
same client-chunked "-rate=20 -duration=1s" "GET $url/chunked"
same client-big "-rate=10 -duration=1s" "GET $url/big" nobody
same client-max-body "-rate=10 -duration=1s -max-body=1000" "GET $url/big"
same client-close "-rate=20 -duration=1s" "GET $url/close"
same client-redirect "-rate=20 -duration=1s" "GET $url/redirect"
same client-no-redirect "-rate=20 -duration=1s -redirects=-1" "GET $url/redirect"
same client-redirect-0 "-rate=20 -duration=1s -redirects=0" "GET $url/redirect"
same client-no-keepalive "-rate=20 -duration=1s -keepalive=false" "GET $url/ok"
same client-stale "-rate=5 -duration=2s -workers=1" "GET $url/ok"
same client-timeout "-rate=4 -duration=1s -timeout=300ms" "GET $url/slow"
same client-refused "-rate=10 -duration=1s" "GET http://127.0.0.1:1/ok"
same client-header-body "-rate=10 -duration=1s -header=X-T:flag" "POST $url/echo
X-T: target
@$w/body.txt" nobody

# ---------------------------------------------------------------------
# unbounded rate and the report types
# ---------------------------------------------------------------------

if run unbounded; then
  echo "GET $url/ok" | "$B" attack -rate=0 -max-workers=4 -duration=1s > "$w/u.csv" 2> "$w/u.err"
  n=$(wc -l < "$w/u.csv" | tr -d ' ')
  codes=$(cut -d, -f2 "$w/u.csv" | sort -u | tr '\n' ' ')
  if [ "$n" -gt 100 ] && [ "$codes" = "200 " ]; then ok "unbounded: -rate=0 -max-workers=4 sent $n hits in 1s, all 200"
  else bad unbounded "$n hits, codes $codes; $(cat "$w/u.err")"; fi
fi

if run report-types; then
  r=0
  for t in text json 'hist[0,1ms,5ms,10ms]'; do "$B" report -type="$t" "$w/pace.csv" > /dev/null 2> "$w/t.err" || r=1; done
  "$B" report -output="$w/out.txt" "$w/pace.csv" && grep -q '^Requests' "$w/out.txt" || r=1
  if [ $r = 0 ]; then ok "report-types: text, json, hist and -output"
  else bad report-types "$(cat "$w/t.err")"; fi
fi

[ "$fail" -eq 0 ] && echo "all passed" || echo "$fail failed"
exit "$fail"
