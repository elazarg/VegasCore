#!/usr/bin/env python3
"""Replay the isolated Lean experiments in the proof-review appendix.

Requires the ordinary project build. Uses its central Lake setup and checks
temporary modules without writing production source or compiled artifacts.
"""

import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
APPENDIX = ROOT / "docs/proof-review/checked-probes.md"
SETUP = ROOT / ".lake/build-stable/ir/GameTheoryExtensions/Analysis/Protocol/PublicScheduling.setup.json"
PATTERN = re.compile(r"<!-- probe: ([A-Za-z0-9_]+) -->\s*```lean\n(.*?)\n```", re.S)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--probe", help="Check only this named experiment")
    parser.add_argument("--list", action="store_true", help="List available experiments")
    args = parser.parse_args()
    probes = PATTERN.findall(APPENDIX.read_text(encoding="utf-8"))
    if not probes or len({name for name, _ in probes}) != len(probes):
        parser.error("the appendix must contain uniquely named Lean experiments")
    if args.list:
        print("\n".join(name for name, _ in probes))
        return 0
    if args.probe:
        probes = [(name, text) for name, text in probes if name == args.probe]
        if not probes:
            parser.error("unknown experiment")
    setup = json.loads(SETUP.read_text(encoding="utf-8"))
    with tempfile.TemporaryDirectory(prefix="vegas-proof-review-") as directory:
        destination = Path(directory)
        for name, text in probes:
            source = destination / (name + ".lean")
            configuration = destination / (name + ".setup.json")
            source.write_text(text + "\n", encoding="utf-8")
            configuration.write_text(json.dumps({**setup, "name": "ProofReview." + name}),
                                     encoding="utf-8")
            print("Checking " + name, flush=True)
            result = subprocess.run(["lake", "env", "lean", "--setup", str(configuration),
                                     str(source)], cwd=ROOT)
            if result.returncode:
                return result.returncode
            print("PASS " + name, flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
