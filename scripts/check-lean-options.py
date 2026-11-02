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


IDENTIFIER_CHAR = re.compile(r"[\w'!?.]")
CHAR_LITERAL = re.compile(r"'(?:\\(?:x[0-9A-Fa-f]{2}|u\{[0-9A-Fa-f]+\}|.)|[^\\'\n])'")
RAW_STRING = re.compile(r'r(#*)"')
# Runs that cannot start a comment, string, character literal or guillemet name.
PLAIN_CODE = re.compile(r"[^/\-\"'«r]+")
PLAIN_COMMENT = re.compile(r"[^/\-\n]+")
PLAIN_STRING = re.compile(r"[^\"\\\n]+")


def _blank(segment: str) -> str:
    return "".join("\n" if char == "\n" else " " for char in segment)


def _follows_name(text: str, pos: int) -> bool:
    return pos > 0 and IDENTIFIER_CHAR.match(text[pos - 1]) is not None


def strip_lean_comments_and_strings(
    text: str, line_comments: list[tuple[int, str]] | None = None,
) -> str:
    """Blank nested comments and the contents of string and character literals,
    preserving offsets and line numbers.

    Raw strings (`r"..."`, `r#"..."#`) end only at their own delimiter, and a
    guillemet name (`«...»`) is copied whole, so neither can open a comment or a
    string. A prime after an identifier character is part of the name, not a
    character literal.
    """
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
                result.append("  ")
                pos += 2
            elif pair == "-/":
                depth -= 1
                result.append("  ")
                pos += 2
            elif run := PLAIN_COMMENT.match(text, pos):
                result.append(" " * len(run.group(0)))
                pos = run.end()
            else:
                result.append("\n" if char == "\n" else " ")
                pos += 1
        elif quoted:
            if char == "\\" and pos + 1 < len(text):
                result.append(" " + ("\n" if text[pos + 1] == "\n" else " "))
                pos += 2
            elif run := PLAIN_STRING.match(text, pos):
                result.append(" " * len(run.group(0)))
                pos = run.end()
            else:
                result.append("\n" if char == "\n" else " ")
                pos += 1
                if char == '"':
                    quoted = False
        elif run := PLAIN_CODE.match(text, pos):
            result.append(run.group(0))
            pos = run.end()
        elif pair == "/-":
            depth = 1
            result.append("  ")
            pos += 2
        elif pair == "--":
            end = text.find("\n", pos)
            end = len(text) if end < 0 else end
            if line_comments is not None:
                line_comments.append((pos, text[pos:end]))
            result.append(" " * (end - pos))
            pos = end
        elif char == "r" and not _follows_name(text, pos) and (raw := RAW_STRING.match(text, pos)):
            closing = '"' + raw.group(1)
            end = text.find(closing, raw.end())
            end = len(text) if end < 0 else end + len(closing)
            result.append(_blank(text[pos:end]))
            pos = end
        elif char == "'" and not _follows_name(text, pos) and (
                literal := CHAR_LITERAL.match(text, pos)):
            result.append(" " * len(literal.group(0)))
            pos = literal.end()
        elif char == "«" and (end := text.find("»", pos)) >= 0 and "\n" not in text[pos:end]:
            result.append(text[pos:end + 1])
            pos = end + 1
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


AXIOM_PRINT = re.compile(r"#print\s+axioms\s+([\w'.]+)")
EXACT_PIN = re.compile(
    r"/-- info: '([\w'.]+)' depends on axioms:\s*\[([^\]]*)\]\s*-/\s*"
    r"(?P<guard>#guard_msgs \(whitespace := lax\) in)\s*"
    r"(?P<print>#print\s+axioms\s+([\w'.]+))"
)
PAPER_OTHER_DECLARATION = re.compile(
    r"(?m)^\s*(?:@\[[^\]\n]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*"
    r"(?:def|abbrev|opaque|structure|class|instance)\b"
)

THEOREM = re.compile(
    r"(?:@\[[^\]\n]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*"
    r"(?:theorem|lemma)\s+([\w'.]+)"
)


def has_explicit_statement(header: str) -> bool:
    """Find the result colon outside binders, before the proof assignment."""
    depth = 0
    for index, char in enumerate(header):
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth -= 1
        elif char == ":" and depth == 0:
            return header[index:index + 2] != ":="
    return False


def check_audit_pins(text: str) -> list[str]:
    """Require full local paper statements and adjacent exact axiom pins.

    Theorems use fully qualified names so their identity is explicit locally.
    Proofs may delegate to the library. Match actual command positions so quoted
    or nested-comment imitations cannot supply a missing guard or expected list.
    Lean checks the statements, proofs and expected dependency lists together.
    """
    clean = strip_lean_comments_and_strings(text)
    prints = list(AXIOM_PRINT.finditer(clean))
    failures: list[str] = []
    if not prints:
        failures.append("Paper.lean: must contain fully stated results and guarded axiom pins")
    if PAPER_OTHER_DECLARATION.search(clean):
        failures.append("Paper.lean: model definitions belong in their owning modules")
    commands = list(re.finditer(r"#print\s+axioms\b", clean))
    if len(commands) != len(prints):
        failures.append("Paper.lean: malformed axiom print")
    counts = Counter(match.group(1) for match in prints)
    failures.extend(f"Paper.lean: duplicate axiom pin for {name}"
                    for name, count in sorted(counts.items()) if count != 1)
    exact = {}
    guards_at = {}
    for match in EXACT_PIN.finditer(text):
        name = match.group(5)
        expected = [axiom.strip() for axiom in match.group(2).split(",") if axiom.strip()]
        if (match.group(1) == name and len(expected) == len(STANDARD_AXIOMS)
                and set(expected) == STANDARD_AXIOMS
                and clean[match.start("guard"):match.end("guard")] == match.group("guard")):
            exact[match.start("print")] = name
            guards_at[match.start("guard")] = name
    for match in prints:
        name = match.group(1)
        if not name.startswith("Vegas.Paper."):
            failures.append(f"Paper.lean: axiom pin must name a full local paper statement: {name}")
        if exact.get(match.start()) != name:
            failures.append(
                f"Paper.lean: axiom pin for {name} must expect exactly "
                "[propext, Classical.choice, Quot.sound] under `#guard_msgs (whitespace := lax)`")
    top_commands = list(re.finditer(r"(?m)^\S[^\n]*", clean))
    declarations = {}
    for index, command in enumerate(top_commands):
        declaration = THEOREM.match(command.group())
        if not declaration:
            continue
        name = declaration.group(1)
        declarations[name] = command.start()
        if not name.startswith("Vegas.Paper."):
            failures.append(f"Paper.lean: use a fully qualified paper theorem name: {name}")
        following = top_commands[index + 1].start() if index + 1 < len(top_commands) else len(clean)
        if not has_explicit_statement(clean[command.start() + declaration.end():following]):
            failures.append(f"Paper.lean: theorem {name} needs its full explicit statement")
        if guards_at.get(following) != name:
            failures.append(f"Paper.lean: exact axiom pin must immediately follow theorem {name}")
    failures.extend(f"Paper.lean: missing guarded axiom pin for {name}"
                    for name in sorted(declarations.keys() - counts.keys()))
    failures.extend(f"Paper.lean: axiom pin names no local paper theorem: {name}"
                    for name in sorted(counts.keys() - declarations.keys()))
    return failures


def check_axiom_prints(relative: Path, text: str) -> list[str]:
    """Keep dependency prints in Paper.lean, the axiom audit of the paper's results."""
    if relative == Path("Paper.lean"):
        return []
    clean = strip_lean_comments_and_strings(text)
    return [f"{relative}:{clean.count(chr(10), 0, match.start()) + 1}: "
            "axiom prints belong in Paper.lean, which pins only results the paper states"
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
          "axiom declarations and trust escape hatches are absent; every Paper pin is "
          "guarded and expects exactly the standard axioms.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
