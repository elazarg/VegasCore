#!/usr/bin/env python3
"""Report recorded open proof obligations on every run, without failing.

An obligation is a Lean line comment starting with `-- OPEN OBLIGATION:`
followed by its title; directly following `--` lines continue its description.
The report is deliberately noisy so that missing results are not forgotten.
"""

from dataclasses import dataclass
import os
from pathlib import Path
import re
import subprocess
import sys

MARKER = re.compile(r"^\s*-- OPEN OBLIGATION:\s*(.*\S)\s*$")
CONTINUATION = re.compile(r"^\s*--(?: (.*))?$")


@dataclass(frozen=True)
class Obligation:
    path: str
    line: int
    title: str
    details: tuple[str, ...]


def parse(path: str, text: str) -> list[Obligation]:
    """Collect every marked obligation with its continuation lines."""
    lines = text.splitlines()
    found = []
    index = 0
    while index < len(lines):
        marker = MARKER.match(lines[index])
        if not marker:
            index += 1
            continue
        details = []
        following = index + 1
        while following < len(lines):
            continued = CONTINUATION.match(lines[following])
            if not continued or MARKER.match(lines[following]):
                break
            details.append((continued.group(1) or "").rstrip())
            following += 1
        found.append(Obligation(path, index + 1, marker.group(1), tuple(details)))
        index = following
    return found


def annotation(obligation: Obligation) -> str:
    """Format a GitHub Actions warning annotation."""
    def escape(value: str) -> str:
        return value.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")

    message = escape("\n".join((obligation.title, *obligation.details)))
    location = f"file={escape(obligation.path)},line={obligation.line}"
    return f"::warning {location},title=Open proof obligation::{message}"


def report(obligations: list[Obligation]) -> str:
    """Render the terminal report."""
    if not obligations:
        return "No open proof obligations recorded."
    rule = "=" * 78
    lines = [rule, f"OPEN PROOF OBLIGATIONS: {len(obligations)} recorded, not yet proved", rule]
    for obligation in obligations:
        lines.append(f"{obligation.path}:{obligation.line}: {obligation.title}")
        lines.extend(f"    {detail}" for detail in obligation.details)
    lines.append(rule)
    return "\n".join(lines)


def lean_sources(root: Path) -> list[str]:
    """Tracked Lean sources, or every Lean source outside build directories."""
    try:
        listed = subprocess.run(
            ["git", "-C", str(root), "ls-files", "-z", "--", "*.lean"],
            check=True, capture_output=True, text=True,
        ).stdout.split("\0")
        return sorted(name for name in listed if name)
    except (OSError, subprocess.CalledProcessError):
        return sorted(
            path.relative_to(root).as_posix() for path in root.rglob("*.lean")
            if ".lake" not in path.parts
        )


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    obligations = [
        obligation
        for name in lean_sources(root)
        for obligation in parse(name, (root / name).read_text(encoding="utf-8"))
    ]
    print(report(obligations))
    if os.environ.get("GITHUB_ACTIONS") == "true":
        for obligation in obligations:
            print(annotation(obligation))
    return 0


if __name__ == "__main__":
    sys.exit(main())
