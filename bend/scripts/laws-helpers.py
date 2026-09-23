#!/usr/bin/env python3
# Writes .build/laws_helpers.bend: LAWS.bend without its law blocks, so tests
# can evaluate the helpers the laws are stated with (a file with open laws
# does not compile). Imports are rebased from bend/ to bend/.build/.
import re, pathlib
here = pathlib.Path(__file__).resolve().parent.parent
src = (here / "LAWS.bend").read_text()
out, skip = [], False
for line in src.splitlines():
    if line.startswith("law "):
        skip = True
        continue
    if skip and (line.startswith(" ") or line == ""):
        if line == "":
            skip = False
            out.append(line)
        continue
    skip = False
    out.append(re.sub(r"^import \./", "import ../", line))
(here / ".build").mkdir(exist_ok=True)
(here / ".build" / "laws_helpers.bend").write_text("\n".join(out) + "\n")
