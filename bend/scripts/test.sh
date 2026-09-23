#!/bin/sh
# The gate: LAWS.bend states every law in time, each tests/*.bend prints its
# `#|` lines, and PROOF.bend proves every law in time.
set -eu
here=$(cd "$(dirname "$0")/.." && pwd)
sh "$here/scripts/install-bend.sh"
export PATH="$here/.build/bendhome/bin:$PATH" BEND_NO_TELEMETRY=1
cd "$here"
mkdir -p .build/tests
python3 scripts/laws-helpers.py
pat=${1:-}
fail=0; n=0

# budget in seconds for a check; fast to check is part of the spec
budget() {
  start=$(date +%s)
  "$@" > .build/check.out 2>&1 || true
  echo $(( $(date +%s) - start ))
}

secs=$(budget bend LAWS.bend)
if grep -q '^Error: [0-9]* TODOs found\|All terms check' .build/check.out && [ "$secs" -le 10 ]; then
  echo "ok   LAWS.bend states $(grep -c '^law ' LAWS.bend) laws (${secs}s)"
else
  echo "FAIL LAWS.bend (${secs}s, budget 10s)"; sed 's/^/  /' .build/check.out; fail=$((fail+1))
fi

for t in tests/*"$pat"*.bend; do
  name=$(basename "$t" .bend); n=$((n+1))
  grep '^#|' "$t" | sed 's/^#|//' > ".build/tests/$name.want"
  if ! bend "$t" -o ".build/tests/$name" > ".build/tests/$name.cc" 2>&1; then
    echo "FAIL $name (compile)"; sed 's/^/  /' ".build/tests/$name.cc"; fail=$((fail+1)); continue
  fi
  ( cd .build/tests && ./"$name" ) < /dev/null > ".build/tests/$name.got" 2>&1 || true
  case "$name" in
    laws_helpers*)
      # pure helper tests also run on bend's default lane: Bend 2.0.25's
      # compiler has been seen to miscompile a Bool expression
      bend "$t" > ".build/tests/$name.lane2" 2>&1 || true
      if ! diff -q ".build/tests/$name.want" ".build/tests/$name.lane2" > /dev/null; then
        echo "FAIL $name (default lane)"; diff -u ".build/tests/$name.want" ".build/tests/$name.lane2" | sed 's/^/  /'; fail=$((fail+1))
      fi;;
  esac
  if diff -u ".build/tests/$name.want" ".build/tests/$name.got" > ".build/tests/$name.diff"; then
    echo "ok   $name"
  else
    echo "FAIL $name"; sed 's/^/  /' ".build/tests/$name.diff"; fail=$((fail+1))
  fi
done

if [ -z "$pat" ]; then
  secs=$(budget bend PROOF.bend)
  if grep -q 'All terms check' .build/check.out && [ "$secs" -le 60 ]; then
    echo "ok   PROOF.bend (${secs}s)"
  else
    echo "FAIL PROOF.bend (${secs}s, budget 60s): $(tail -1 .build/check.out)"; fail=$((fail+1))
  fi
fi
[ "$fail" -eq 0 ] && echo "all passed" || { echo "$fail failed"; exit 1; }
