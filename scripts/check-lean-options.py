"""Enforce centralized options and reject unchecked Lean escape hatches.

The build rejects `sorry` (warnings are errors). This check adds what the build
cannot see: options overridden outside the central table, bespoke axioms, trust
and code-generation escape hatches, and the exact axiom pins of Paper.lean.
"""

from collections import Counter
from pathlib import Path
import re
import sys
import tomllib


STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def check_central_options(options: dict) -> list[str]:
    """Require explicit binders and warnings as errors, with sorry warnings on."""
    required = {
        "autoImplicit": False,
        "relaxedAutoImplicit": False,
        "warningAsError": True,
    }

    def lookup(name: str):
        current = options
        for part in name.split("."):
            if not isinstance(current, dict):
                return None
            current = current.get(part)
        return current

    failures = [
        f"lakefile.toml: leanOptions.{name} must be {str(value).lower()}"
        for name, value in required.items()
        if lookup(name) is not value
    ]
    if lookup("warn.sorry") is False:
        failures.append("lakefile.toml: leanOptions.warn.sorry must not be false; "
                        "a sorry must fail the build")
    return failures


def check_lakefile(config: dict) -> list[str]:
    """Options live only in the top-level table, never per library or as -D arguments."""
    failures = check_central_options(config.get("leanOptions", {}))
    tables = [("package", config)] + [
        (f"lean_lib {library.get('name', '?')}", library)
        for library in config.get("lean_lib", [])
    ]
    for label, table in tables:
        if table is not config and "leanOptions" in table:
            failures.append(f"lakefile.toml: {label} sets leanOptions outside the central table")
        for key in ("moreLeanArgs", "weakLeanArgs"):
            for argument in table.get(key, []):
                if str(argument).startswith("-D"):
                    failures.append(f"lakefile.toml: {label} sets option {argument} in {key}")
    return failures


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


def check_admissions(relative: Path, text: str) -> list[str]:
    """Reject every proof admission. No file is exempt."""
    return [f"{relative}:{number}: forbidden proof admission `{token}`"
            for number, token in admission_tokens(text)]


ESCAPE_HATCHES = (
    (r"\bset_option\b", "source-local `set_option`"),
    (r"\bnative_decide\b", "`native_decide`"),
    (r"\+native\b", "native evaluation (`+native`)"),
    (r"\bunsafe\b", "`unsafe`"),
    (r"\bimplemented_by\b", "`implemented_by`"),
    (r"\b(?:ofReduceBool|ofReduceNat|trustCompiler)\b", "compiler-trusting reduction"),
    (r"\b(?:addDecl|addAndCompile|mkSorry)\b", "declaration-adding metaprogram"),
    (r"\bskipKernelTC\b", "skipped kernel check"),
    (r"\b(?:run_cmd|run_elab|run_meta|elab_rules|elab)\b|#eval\b", "elaboration-time program"),
)


def check_forbidden_constructs(relative: Path, text: str) -> list[str]:
    """Reject local options, trust and code-generation escape hatches, and axioms.

    `#print axioms` is deliberately not an axiom declaration and remains the
    dependency audit mechanism in `Paper.lean`.
    """
    clean = strip_lean_comments_and_strings(text)
    failures: list[str] = []
    for pattern, description in ESCAPE_HATCHES:
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


THEOREM = re.compile(
    r"(?:@\[[^\]\n]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+([\w'.]+)"
)
EXACT_PIN = re.compile(
    r"/-- info: 'Vegas\.Paper\.([\w'.]+)' depends on axioms:\s*\[([^\]]*)\]\s*-/\s*"
    r"#guard_msgs \(whitespace := lax\) in\s*#print axioms Vegas\.Paper\.([\w'.]+)\b"
)


def check_audit_pins(text: str) -> list[str]:
    """Require an exact guarded axiom pin immediately after each Paper theorem.

    A pin is the expected-output docstring listing exactly the standard axioms,
    then `#guard_msgs (whitespace := lax) in`, then `#print axioms` of the
    theorem. Lean checks the expected output against the proof during the build.
    """
    clean = strip_lean_comments_and_strings(text)
    commands = list(re.finditer(r"(?m)^\S[^\n]*", clean))
    declarations = {match.group(1) for command in commands
                    if (match := THEOREM.match(command.group()))}
    pin_matches = list(re.finditer(
        r"#guard_msgs[^\n]*?\s+in\s+#print\s+axioms\s+Vegas\.Paper\.([\w'.]+)\b", clean
    ))
    pins = Counter(match.group(1) for match in pin_matches)
    failures = [f"Paper.lean: missing guarded axiom pin for {name}"
                for name in sorted(declarations - pins.keys())]
    failures.extend(f"Paper.lean: axiom pin names no audit theorem: {name}"
                    for name in sorted(pins.keys() - declarations))
    failures.extend(f"Paper.lean: duplicate axiom pin for {name}"
                    for name, count in sorted(pins.items()) if count != 1)
    exact = Counter()
    for match in EXACT_PIN.finditer(text):
        expected = {axiom.strip() for axiom in match.group(2).split(",") if axiom.strip()}
        if match.group(1) == match.group(3) and expected == STANDARD_AXIOMS:
            exact[match.group(3)] += 1
    failures.extend(
        f"Paper.lean: axiom pin for {name} must expect exactly "
        "[propext, Classical.choice, Quot.sound] under `#guard_msgs (whitespace := lax)`"
        for name in sorted(pins) if exact[name] != pins[name])
    pins_at = {match.start(): match.group(1) for match in pin_matches}
    for index, command in enumerate(commands):
        if declaration := THEOREM.match(command.group()):
            name = declaration.group(1)
            following = commands[index + 1].start() if index + 1 < len(commands) else None
            if pins[name] == 1 and pins_at.get(following) != name:
                failures.append(f"Paper.lean: axiom pin must immediately follow theorem {name}")
    return failures


def check_axiom_prints(relative: Path, text: str) -> list[str]:
    """Keep dependency prints in Paper.lean, the axiom audit."""
    if relative == Path("Paper.lean"):
        return []
    clean = strip_lean_comments_and_strings(text)
    return [f"{relative}:{clean.count(chr(10), 0, match.start()) + 1}: "
            "axiom prints belong in Paper.lean"
            for match in re.finditer(r"#print\s+axioms\b", clean)]


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    with (root / "lakefile.toml").open("rb") as config:
        failures = check_lakefile(tomllib.load(config))
    paths = list(root.glob("*.lean"))
    for directory in ("GameTheoryExtensions", "GameTheoryExtensionsTests", "Interaction",
                      "InteractionTests", "Vegas", "VegasTests", "Paper"):
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
    print("Central options are strict and sorry warnings fail the build; proof admissions, "
          "axiom declarations and trust escape hatches are absent; every Paper theorem has "
          "an exact standard-axiom pin.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
