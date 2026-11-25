#!/usr/bin/env python3
"""Compare the active manuscript's marked results with Paper.lean at its cited revision."""

import argparse
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
RESULT = re.compile(r"^\s*%\s*Lean:\s*(Vegas\.Paper\.[\w']+)\s*$")
INPUT = re.compile(r"\\(?:input|include)\s*\{([^{}]+)\}")
REVISION = re.compile(r"https://github\.com/elazarg/VegasCore/tree/([0-9a-f]{40})\b")
PIN = re.compile(r"^\s*#print axioms (Vegas\.Paper\.[\w']+)\s*$", re.MULTILINE)


def marked_results(manuscript):
    seen = set()
    results = set()
    pending = [manuscript / "main.tex"]
    while pending:
        path = pending.pop().resolve()
        if path in seen:
            continue
        seen.add(path)
        for line in path.read_text(encoding="utf-8").splitlines():
            if match := RESULT.fullmatch(line):
                results.add(match[1])
            elif re.match(r"^\s*%\s*Lean:\s*Vegas\.Paper\.", line):
                raise ValueError(f"Malformed result marker in {path}: {line}")
            code = re.split(r"(?<!\\)%", line, maxsplit=1)[0]
            for name in INPUT.findall(code):
                child = Path(name)
                pending.append(manuscript / (child if child.suffix else child.with_suffix(".tex")))
    return results


def cited_revision(manuscript):
    bibliography = (manuscript / "vegas-paper.bib").read_text(encoding="utf-8")
    entry = re.search(r"^@\w+\{VegasCoreRepo2026\s*,.*?(?=^@|\Z)",
                      bibliography, flags=re.MULTILINE | re.DOTALL)
    revisions = set(REVISION.findall(entry[0])) if entry else set()
    if len(revisions) != 1:
        raise ValueError("Expected one full VegasCore commit in the artifact citation.")
    return revisions.pop()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manuscript", type=Path, help="directory containing main.tex")
    args = parser.parse_args()
    try:
        marked = marked_results(args.manuscript)
        revision = cited_revision(args.manuscript)
        paper = subprocess.run(["git", "show", f"{revision}:Paper.lean"], cwd=ROOT,
                               text=True, capture_output=True, check=True).stdout
        pins = set(PIN.findall(paper))
        if not pins:
            raise ValueError(f"No guarded pin names found in Paper.lean at {revision}.")
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(error, file=sys.stderr)
        return 1
    for result in sorted(marked - pins):
        print(f"Manuscript marker missing from cited Paper.lean: {result}", file=sys.stderr)
    for result in sorted(pins - marked):
        print(f"Cited Paper.lean pin missing from active manuscript: {result}", file=sys.stderr)
    if marked != pins:
        return 1
    print(f"{len(pins)} manuscript result names match Paper.lean at {revision}.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
