#!/bin/sh
# Installs the pinned Bend into bend/.build/bendhome (no ~ writes, no telemetry).
set -eu
here=$(cd "$(dirname "$0")/.." && pwd)
want=$(cat "$here/.bend-version")
home="$here/.build/bendhome"
if [ -x "$home/bin/bend" ] && [ "$(cat "$home/.ver" 2>/dev/null)" = "$want" ]; then exit 0; fi
mkdir -p "$home"
curl -fsSL https://bend-lang.com/install.sh > "$here/.build/install.sh"
grep -q "VER=\"$want\"" "$here/.build/install.sh" || {
  echo "bend-lang.com now serves a newer Bend than $want; install $want by hand (see README)" >&2; exit 1; }
BEND_HOME="$home" BEND_NO_TELEMETRY=1 sh "$here/.build/install.sh" >/dev/null
echo "$want" > "$home/.ver"
