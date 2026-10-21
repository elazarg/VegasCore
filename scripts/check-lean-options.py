"""Enforce centralized options and reject unchecked Lean escape hatches."""

from collections import Counter
from pathlib import Path
import re
import sys
import tomllib


# Only the reviewed primitive obligations may contain holes. Assembly results
# must have proof bodies; adding a primitive requires an explicit registry diff.
APPROVED_OPEN_OBLIGATIONS = {
    ("Vegas/Game/PhaseProposalQualifiedBinding.lean", "qualified_annotation_pushforward"):
        "docs/se-concurrent-likelihood-review.md#mathematical-review-boundary",
}


def check_central_options(options: dict) -> list[str]:
    """Require explicit binders and centrally permit tracked proof warnings."""
    required = {
        "autoImplicit": False,
        "relaxedAutoImplicit": False,
        "warningAsError": True,
        "warn.sorry": False,
    }

    def lookup(name: str):
        current = options
        for part in name.split("."):
            if not isinstance(current, dict):
                return None
            current = current.get(part)
        return current

    return [
        f"lakefile.toml: leanOptions.{name} must be {str(value).lower()}"
        for name, value in required.items()
        if lookup(name) is not value
    ]


def strip_lean_comments_and_strings(
    text: str, line_comments: list[tuple[int, str]] | None = None,
) -> str:
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
            if line_comments is not None:
                line_comments.append((pos, text[pos:end if end >= 0 else len(text)]))
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


def obligation_ranges(text: str) -> tuple[list[tuple[int, int, int, str]], list[str]]:
    """Recognize named markers immediately before flat theorem declarations.

    The supported layout is deliberately small, like the audit-pin layout:
    `-- OPEN OBLIGATION: declaration_name - explanation`, followed by a
    theorem/lemma (optionally private/protected), with an indented body.
    Blank lines are allowed; intervening commands or comments are not.
    """
    comments: list[tuple[int, str]] = []
    clean = strip_lean_comments_and_strings(text, comments)
    commands = list(re.finditer(r"(?m)^\S[^\n]*", clean))
    markers = {}
    failures = []
    for offset, comment in comments:
        if not comment.startswith("-- OPEN OBLIGATION:"):
            continue
        line = text.count("\n", 0, offset) + 1
        match = re.fullmatch(r"-- OPEN OBLIGATION: ([\w'.]+) - (\S.*)", comment)
        if not match:
            # Existing prose-only obligation notes grant no admission permission.
            continue
        if text[text.rfind("\n", 0, offset) + 1:offset].strip():
            failures.append(f"{line}: named OPEN OBLIGATION must be on its own line")
            continue
        following = next((command for command in commands if command.start() > offset), None)
        if following is None or text[offset + len(comment):following.start()].strip():
            failures.append(f"{line}: OPEN OBLIGATION must immediately precede its theorem")
            continue
        declaration = re.match(
            r"(?:(?:private|protected)\s+)?(?:theorem|lemma)\s+([\w'.]+)\b",
            following.group(),
        )
        if declaration is None or declaration.group(1) != match.group(1):
            failures.append(f"{line}: OPEN OBLIGATION must name the following theorem")
            continue
        markers[following.start()] = (line, match.group(1))
    ranges = []
    for index, command in enumerate(commands):
        if command.start() in markers:
            line, name = markers[command.start()]
            end = commands[index + 1].start() if index + 1 < len(commands) else len(clean)
            ranges.append((command.start(), end, line, name))
    return ranges, failures


def check_admissions(
    relative: Path, text: str,
    approved: dict[tuple[str, str], str] | None = None,
) -> list[str]:
    """Allow one literal sorry per explicitly named outstanding theorem.

    No file is exempt. `admit` and direct `sorryAx` remain forbidden, including
    inside a marked declaration or a guarded Paper command.
    """
    registry = APPROVED_OPEN_OBLIGATIONS if approved is None else approved
    ranges, marker_errors = obligation_ranges(text)
    failures = [f"{relative}:{error}" for error in marker_errors]
    clean = strip_lean_comments_and_strings(text)
    tokens = list(re.finditer(r"\b(?:sorryAx|sorry|admit)\b", clean))
    for token in tokens:
        number = clean.count("\n", 0, token.start()) + 1
        if token.group() != "sorry" or not any(
            start <= token.start() < end for start, end, _, _ in ranges
        ):
            failures.append(
                f"{relative}:{number}: forbidden proof admission `{token.group()}`; "
                "only literal sorry in a named OPEN OBLIGATION is permitted"
            )
    for start, end, line, name in ranges:
        if not registry.get((relative.as_posix(), name), "").strip():
            failures.append(
                f"{relative}:{line}: unregistered OPEN OBLIGATION {name}; "
                "an explicit approved registry entry with a mathematical review reference is required"
            )
        count = sum(start <= token.start() < end and token.group() == "sorry" for token in tokens)
        if count != 1:
            failures.append(
                f"{relative}:{line}: OPEN OBLIGATION {name} must contain exactly one sorry "
                f"(found {count})"
            )
    return failures


def check_forbidden_constructs(relative: Path, text: str) -> list[str]:
    """Reject local trust and code-generation escape hatches.

    `#print axioms` is deliberately not an axiom declaration and remains the
    dependency audit mechanism in `Paper.lean` and the dedicated test audits.
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
    """Keep dependency prints in the paper or guarded regression audit modules."""
    if relative == Path("Paper.lean"):
        return []
    clean = strip_lean_comments_and_strings(text)
    failures = []
    regression = relative.parts[:2] == ("VegasTests", "AxiomAudit")
    for match in re.finditer(r"#print\s+axioms\b", clean):
        number = clean.count("\n", 0, match.start()) + 1
        if not regression:
            failures.append(
                f"{relative}:{number}: axiom prints belong in Paper.lean or VegasTests/AxiomAudit")
        elif not re.search(r"#guard_msgs[^\n]*\bin\s*$", clean[:match.start()]):
            failures.append(f"{relative}:{number}: dependency regression must use #guard_msgs")
    return failures


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    with (root / "lakefile.toml").open("rb") as config:
        failures = check_central_options(tomllib.load(config).get("leanOptions", {}))
    paths = list(root.glob("*.lean"))
    for directory in ("GameTheoryExtensions", "GameTheoryExtensionsTests", "Interaction", "InteractionTests", "Vegas",
                      "VegasTests", "Paper"):
        paths.extend((root / directory).rglob("*.lean"))
    obligations = []
    for path in sorted(paths):
        text = path.read_text(encoding="utf-8")
        relative = path.relative_to(root)
        failures.extend(check_forbidden_constructs(relative, text))
        failures.extend(check_admissions(relative, text))
        for _, _, line, name in obligation_ranges(text)[0]:
            obligations.append(f"{relative}:{line}: {name}")
        failures.extend(check_axiom_prints(relative, text))
        if relative == Path("Paper.lean"):
            failures.extend(check_audit_pins(text))
    print(f"Tracked OPEN OBLIGATION declarations: {len(obligations)}")
    for obligation in obligations:
        print(f"  {obligation}")
    if failures:
        print("Lean source policy violations:")
        print("\n".join(failures))
        return 1
    print("Explicit binders and warning-strict compilation configured centrally; "
          "sorry diagnostics replaced by the explicit obligation report; "
          "only registered named single-sorry obligations permitted; other trust/code-generation "
          "escape hatches rejected; existing dependency audit guards enforced.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
