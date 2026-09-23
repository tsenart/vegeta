#!/bin/sh
# Benchmarks, Bend vegeta against Go vegeta on this machine:
#   1. attack throughput at an unbounded rate (-rate=0) against the e2e
#      test server, for a few worker counts;
#   2. attack at a fixed rate: the achieved rate and the latency spread;
#   3. report speed on N results (CSV and JSON).
#
#   sh scripts/bench.sh [seconds] [results]   (defaults: 5, 1000000)
set -u
here=$(cd "$(dirname "$0")/.." && pwd)
repo=$(cd "$here/.." && pwd)
sh "$here/scripts/install-bend.sh"
export PATH="$here/.build/bendhome/bin:$PATH" BEND_NO_TELEMETRY=1
b="$here/.build"; w="$b/bench"; mkdir -p "$w"
secs=${1:-5}; nres=${2:-1000000}

bend "$here/main.bend" -o "$b/vegeta" > "$w/build.out" 2>&1 || { cat "$w/build.out"; exit 1; }
(cd "$repo" && go build -o "$b/vegeta-go" . && go build -o "$b/e2e-server" ./bend/scripts/e2e-server) || exit 1
port=18322
PORT=$port "$b/e2e-server" & srv=$!
trap 'kill $srv 2>/dev/null' EXIT INT TERM
for _ in 1 2 3 4 5 6 7 8 9 10; do curl -s "http://127.0.0.1:$port/stats" > /dev/null && break; sleep 0.2; done
echo "GET http://127.0.0.1:$port/ok" > "$w/t.txt"
B="$b/vegeta"; G="$b/vegeta-go"

# requests per second and success, from a CSV results file, via Go's report
summary() {
  "$G" report -type=json "$1" | python3 -c '
import json, sys
d = json.load(sys.stdin)
l = d["latencies"]
print("%9.0f req/s  success %5.1f%%  p50 %8.1fus  p99 %8.1fus  n=%d" % (d["throughput"], 100 * d["success"], l["50th"] / 1e3, l["99th"] / 1e3, d["requests"]))'
}

echo "== attack, unbounded rate, ${secs}s"
for mw in 1 10 50; do
  "$G" attack -targets="$w/t.txt" -rate=0 -max-workers=$mw -duration=${secs}s | "$G" encode -to=csv > "$w/g.csv"
  "$B" attack -targets="$w/t.txt" -rate=0 -max-workers=$mw -duration=${secs}s > "$w/b.csv"
  printf 'go   %3d workers  %s\n' "$mw" "$(summary "$w/g.csv")"
  printf 'bend %3d workers  %s\n' "$mw" "$(summary "$w/b.csv")"
done

echo "== attack, 5000/s, ${secs}s"
"$G" attack -targets="$w/t.txt" -rate=5000 -duration=${secs}s | "$G" encode -to=csv > "$w/g.csv"
"$B" attack -targets="$w/t.txt" -rate=5000 -duration=${secs}s > "$w/b.csv"
printf 'go    %s\n' "$(summary "$w/g.csv")"
printf 'bend  %s\n' "$(summary "$w/b.csv")"

echo "== report, $nres results"
python3 - "$w/b.csv" "$nres" "$w/big.csv" <<'EOF'
import sys
rows = open(sys.argv[1]).read().splitlines()
n = int(sys.argv[2])
with open(sys.argv[3], "w") as f:
    for i in range(n):
        f.write(rows[i % len(rows)] + "\n")
EOF
"$G" encode -to=json "$w/big.csv" > "$w/big.json"
for f in big.csv big.json; do
  for v in go bend; do
    [ $v = go ] && bin=$G || bin=$B
    t0=$(python3 -c 'import time; print(time.time())')
    "$bin" report "$w/$f" > /dev/null
    t1=$(python3 -c 'import time; print(time.time())')
    printf '%-4s %-8s %6.2fs\n' "$v" "$f" "$(python3 -c "print($t1 - $t0)")"
  done
done
