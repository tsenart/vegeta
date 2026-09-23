#!/usr/bin/env python3
"""Flags a recursive call inside a strict pick: pick evaluates both
branches, so `pick(A, c, x, f(rest))` in def f always recurses to the end
(copying and freeing as it goes). Give the choice a def that matches a
Bool instead. Usage: python3 scripts/lint-pick.py [files...] (default
lib/*.bend); exit status is the number of findings."""
import glob, re, sys

files = sys.argv[1:] or sorted(glob.glob('lib/*.bend'))
found = 0
for f in files:
    cur = None
    for i, l in enumerate(open(f).read().split('\n'), 1):
        m = re.match(r'(?:@unsafe )?def ([\w.]+)\(', l)
        if m:
            cur = m.group(1)
            continue
        if cur and 'pick(' in l and re.search(r'(?<![\w.])' + re.escape(cur) + r'\(', l):
            print(f"{f}:{i}: {cur}: {l.strip()[:100]}")
            found += 1
sys.exit(min(found, 255))
