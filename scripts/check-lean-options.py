"""Require central Lean options and confine admissions to the paper audit."""

from collections import Counter
from pathlib import Path
import re
import sys
import tomllib


def check_central_options(options: dict) -> list[str]:
    """Require explicit theorem binders and warning-strict compilation."""
    required = {
        "autoImplicit": False,
        "relaxedAutoImplicit": False,
        "warningAsError": True,
    }
    return [
        f"lakefile.toml: leanOptions.{name} must be {str(value).lower()}"
        for name, value in required.items()
        if options.get(name) is not value
    ]


def strip_lean_comments_and_strings(text: str) -> str:
    """Blank nested comments and string contents while preserving line numbers."""
    result = []
    depth = 0
    quoted = False
    pos = 0
    while pos < len(text):
        pair = text[pos:pos + 2]
        char = text[pos]
        if depth:
            if pair == "/-":
                depth += 1
                result.extend("  ")
                pos += 2
            elif pair == "-/":
                depth -= 1
                result.extend("  ")
                pos += 2
            else:
                result.append("\n" if char == "\n" else " ")
                pos += 1
        elif quoted:
            if char == "\\" and pos + 1 < len(text):
                result.extend("  ")
                pos += 2
            else:
                result.append("\n" if char == "\n" else " ")
                pos += 1
                if char == '"':
                    quoted = False
        elif pair == "/-":
            depth = 1
            result.extend("  ")
            pos += 2
        elif pair == "--":
            end = text.find("\n", pos)
            if end < 0:
                result.extend(" " * (len(text) - pos))
                pos = len(text)
            else:
                result.extend(" " * (end - pos))
                pos = end
        elif char == '"':
            quoted = True
            result.append(" ")
            pos += 1
        else:
            result.append(char)
            pos += 1
    return "".join(result)


def admission_tokens(text: str) -> list[tuple[int, str]]:
    """Return proof-admission tokens outside comments and strings."""
    clean = strip_lean_comments_and_strings(text)
    pattern = re.compile(r"\b(?:sorryAx|sorry|admit)\b")
    return [
        (number, match.group(0))
        for number, line in enumerate(clean.splitlines(), 1)
        for match in pattern.finditer(line)
    ]


def check_admissions(relative: Path, text: str) -> list[str]:
    """Permit proof admissions only in the single root paper audit."""
    if relative == Path("Paper.lean"):
        return []
    return [
        f"{relative}:{number}: forbidden proof admission `{token}`"
        for number, token in admission_tokens(text)
    ]


def check_audit_pins(text: str) -> list[str]:
    """Require one guarded dependency print for each flat Vegas.Paper theorem.

    This checks the compact audit's structure; Lean checks each expected axiom
    report against the actual proof dependencies during the build.
    """
    clean = strip_lean_comments_and_strings(text)
    declarations = set(re.findall(r"(?m)^theorem\s+(\w+)\b", clean))
    pins = Counter(re.findall(
        r"#guard_msgs[^\n]*?\s+in\s+#print\s+axioms\s+Vegas\.Paper\.(\w+)\b", clean
    ))
    failures = [f"Paper.lean: missing guarded axiom pin for {name}"
                for name in sorted(declarations - pins.keys())]
    failures.extend(f"Paper.lean: axiom pin names no audit theorem: {name}"
                    for name in sorted(pins.keys() - declarations))
    failures.extend(f"Paper.lean: duplicate axiom pin for {name}"
                    for name, count in sorted(pins.items()) if count != 1)
    return failures


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    local_option = re.compile(r"^\s*set_option\b")
    with (root / "lakefile.toml").open("rb") as config:
        failures = check_central_options(tomllib.load(config).get("leanOptions", {}))
    paths = list(root.glob("*.lean"))
    for directory in ("GameTheoryExtensions", "GameTheoryExtensionsTests", "Interaction", "InteractionTests", "Vegas",
                      "VegasTests", "Paper"):
        paths.extend((root / directory).rglob("*.lean"))
    for path in sorted(paths):
        text = path.read_text(encoding="utf-8")
        for number, line in enumerate(text.splitlines(), 1):
            if local_option.match(line):
                failures.append(f"{path.relative_to(root)}:{number}: {line.strip()}")
        failures.extend(check_admissions(path.relative_to(root), text))
        if path.relative_to(root) == Path("Paper.lean"):
            failures.extend(check_audit_pins(text))
    if failures:
        print("Lean source policy violations:")
        print("\n".join(failures))
        return 1
    print("Explicit binders and warning-strict compilation configured centrally; "
          "no source-local Lean options or proof admissions outside Paper.lean; "
          "capstone axiom pins complete.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
