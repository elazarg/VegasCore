"""Enforce centralized options and reject unchecked Lean escape hatches."""

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
    """Permit Paper admissions only when their warning is explicitly guarded.

    `warningAsError` rejects an ordinary `sorry`.  Paper may state an openly
    prospective theorem only by wrapping that declaration in `#guard_msgs`,
    which both documents and checks the expected diagnostic.
    """
    tokens = admission_tokens(text)
    if relative != Path("Paper.lean"):
        return [
            f"{relative}:{number}: forbidden proof admission `{token}`"
            for number, token in tokens
        ]
    if not tokens:
        return []
    clean = strip_lean_comments_and_strings(text)
    commands = list(re.finditer(r"(?m)^\S[^\n]*", clean))
    guarded_ranges: list[tuple[int, int]] = []
    for index, command in enumerate(commands):
        if not re.match(r"(?:theorem|lemma)\s+\w+\b", command.group()):
            continue
        previous = commands[index - 1].group() if index else ""
        if not re.match(r"#guard_msgs\b[^\n]*\bin\s*$", previous):
            continue
        end = commands[index + 1].start() if index + 1 < len(commands) else len(clean)
        guarded_ranges.append((command.start(), end))
    failures = []
    for number, token in tokens:
        position = sum(len(line) + 1 for line in clean.splitlines()[:number - 1])
        if not any(start <= position < end for start, end in guarded_ranges):
            failures.append(
                f"{relative}:{number}: Paper admission `{token}` must be wrapped "
                "in #guard_msgs under warningAsError"
            )
    return failures


def check_forbidden_constructs(relative: Path, text: str) -> list[str]:
    """Reject local trust and code-generation escape hatches.

    `#print axioms` is deliberately not an axiom declaration and remains the
    dependency audit mechanism in root `Paper.lean`.
    """
    clean = strip_lean_comments_and_strings(text)
    failures: list[str] = []
    patterns = (
        (r"\bset_option\b", "source-local `set_option`"),
        (r"\bnative_decide\b", "`native_decide`"),
        (r"\bunsafe\b", "`unsafe`"),
        (r"\bimplemented_by\b", "`implemented_by`"),
    )
    for pattern, description in patterns:
        for match in re.finditer(pattern, clean):
            number = clean.count("\n", 0, match.start()) + 1
            failures.append(f"{relative}:{number}: forbidden {description}")
    # `axiom` is a command keyword, so any remaining occurrence is a bespoke
    # declaration even when command combinators or attributes precede it on the
    # same line. Remove the one legitimate non-declaration syntax first.
    without_prints = re.sub(
        r"#print\s+axioms\b",
        lambda match: "".join("\n" if char == "\n" else " " for char in match.group()),
        clean,
    )
    for match in re.finditer(r"\baxioms?\b", without_prints):
        number = clean.count("\n", 0, match.start()) + 1
        failures.append(f"{relative}:{number}: forbidden axiom declaration")
    return failures


def check_audit_pins(text: str) -> list[str]:
    """Require a guarded dependency print immediately after each audit theorem.

    The audit uses flat commands and indented direct-delegation bodies. This
    checks that layout, not arbitrary Lean syntax; Lean checks each expected
    axiom report against the actual proof dependencies during the build.
    """
    clean = strip_lean_comments_and_strings(text)
    declarations = set(re.findall(r"(?m)^theorem\s+(\w+)\b", clean))
    pin_matches = list(re.finditer(
        r"#guard_msgs[^\n]*?\s+in\s+#print\s+axioms\s+Vegas\.Paper\.(\w+)\b", clean
    ))
    pins = Counter(match.group(1) for match in pin_matches)
    failures = [f"Paper.lean: missing guarded axiom pin for {name}"
                for name in sorted(declarations - pins.keys())]
    failures.extend(f"Paper.lean: axiom pin names no audit theorem: {name}"
                    for name in sorted(pins.keys() - declarations))
    failures.extend(f"Paper.lean: duplicate axiom pin for {name}"
                    for name, count in sorted(pins.items()) if count != 1)
    pins_at = {match.start(): match.group(1) for match in pin_matches}
    commands = list(re.finditer(r"(?m)^\S[^\n]*", clean))
    for index, command in enumerate(commands):
        if declaration := re.match(r"theorem\s+(\w+)\b", command.group()):
            name = declaration.group(1)
            following = commands[index + 1].start() if index + 1 < len(commands) else None
            if pins[name] == 1 and pins_at.get(following) != name:
                failures.append(f"Paper.lean: axiom pin must immediately follow theorem {name}")
    return failures


def check_axiom_prints(relative: Path, text: str) -> list[str]:
    """Keep axiom-print commands in the single root paper audit."""
    if relative == Path("Paper.lean"):
        return []
    clean = strip_lean_comments_and_strings(text)
    failures = []
    for match in re.finditer(r"#print\s+axioms\b", clean):
        number = clean.count("\n", 0, match.start()) + 1
        failures.append(f"{relative}:{number}: axiom prints belong only in Paper.lean")
    return failures


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    with (root / "lakefile.toml").open("rb") as config:
        failures = check_central_options(tomllib.load(config).get("leanOptions", {}))
    paths = list(root.glob("*.lean"))
    for directory in ("GameTheoryExtensions", "GameTheoryExtensionsTests", "Interaction", "InteractionTests", "Vegas",
                      "VegasTests", "Paper"):
        paths.extend((root / directory).rglob("*.lean"))
    for path in sorted(paths):
        text = path.read_text(encoding="utf-8")
        relative = path.relative_to(root)
        failures.extend(check_forbidden_constructs(relative, text))
        failures.extend(check_admissions(relative, text))
        failures.extend(check_axiom_prints(relative, text))
        if relative == Path("Paper.lean"):
            failures.extend(check_audit_pins(text))
    if failures:
        print("Lean source policy violations:")
        print("\n".join(failures))
        return 1
    print("Explicit binders and warning-strict compilation configured centrally; "
          "no unchecked trust or code-generation escape hatches; guarded Paper "
          "admissions only; axiom prints confined to adjacent Paper capstone pins.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
