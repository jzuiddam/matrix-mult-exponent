#!/usr/bin/env python3
"""Add a scheduling-only import to the level-3 incidence bridge, hash-guarded.

    apply_gate_import.py REPO [--check]

Adds `import OmegaBound.ADVXXZGeneralCExact38InputReserve` to the generated module
`ADVXXZGeneralRowsBridgeIncidence30` directly after its first import.  The dependency has no mathematical meaning: it only makes
Lake release the level-3 bridge bulk after the serial `CExact37 -> CExact38InputReserve` links, so
that those links stop waiting behind it (measured: about 5 minutes less wall time on a cold build).  The tool refuses to
write unless the import-stripped body is byte-identical before and after, and unless the imported
module exists and does not itself (transitively, by source imports) import Incidence30.
--check only reports whether the gate is present.
"""

from __future__ import annotations

import argparse
import hashlib
import pathlib
import re
import sys

TARGET = "ADVXXZGeneralRowsBridgeIncidence30"
GATE = "ADVXXZGeneralCExact38InputReserve"


def stripped(text: str) -> str:
    return hashlib.sha256("\n".join(l for l in text.split("\n")
                                    if not l.startswith("import ")).encode()).hexdigest()


def imports_of(root: pathlib.Path, mod: str) -> list[str]:
    p = root / (mod.replace(".", "/") + ".lean")
    if not p.exists():
        return []
    return re.findall(r"^import (\S+)", p.read_text(), re.M)


def reaches(root: pathlib.Path, start: str, goal: str) -> bool:
    seen, stack = set(), [start]
    while stack:
        m = stack.pop()
        if m == goal:
            return True
        if m in seen or not m.startswith("OmegaBound."):
            continue
        seen.add(m)
        stack += imports_of(root, m)
    return False


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("repo")
    ap.add_argument("--check", action="store_true")
    a = ap.parse_args()
    root = pathlib.Path(a.repo).resolve()
    p = root / "OmegaBound" / f"{TARGET}.lean"
    text = p.read_text()
    line = f"import OmegaBound.{GATE}\n"
    if a.check:
        print("gate present" if line in text else "gate absent")
        return 0 if line in text else 1
    if line in text:
        print("gate already present")
        return 0
    assert (root / "OmegaBound" / f"{GATE}.lean").exists()
    if reaches(root, f"OmegaBound.{GATE}", f"OmegaBound.{TARGET}"):
        print("REFUSED: the gate module imports the target (cycle)", file=sys.stderr)
        return 1
    lines = text.split("\n")
    first = next(i for i, l in enumerate(lines) if l.startswith("import "))
    new = "\n".join(lines[: first + 1] + [line.rstrip("\n")] + lines[first + 1:])
    if stripped(text) != stripped(new):
        print("REFUSED: import-stripped body changed", file=sys.stderr)
        return 1
    p.write_text(new)
    print(f"gate applied to {TARGET}; import-stripped SHA-256 {stripped(new)} (unchanged)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
