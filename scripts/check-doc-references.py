#!/usr/bin/env python3
"""Check Lean declaration citations and tracked Markdown paths.

This is a deliberately small lexical index, not a Lean parser. Qualified
citations are resolved through the namespace at the citation site and explicit
`open` commands; project-qualified citations fail closed. Unqualified
snake_case and camelCase citations are accepted only when their short name is
unique in the project index.
"""

from __future__ import annotations

from dataclasses import dataclass
import os
from pathlib import Path
import re
import subprocess
import sys


ROOTS_DEFINING = (
    "GameTheoryExtensions", "GameTheoryExtensionsTests", "Interaction",
    "InteractionTests", "Vegas", "Paper", "GameTheory/GameTheory",
)
ROOTS_CITING = (
    "GameTheoryExtensions", "GameTheoryExtensionsTests", "Interaction",
    "InteractionTests", "Vegas", "Paper",
)
PROJECT_PREFIXES = {
    "GameTheory", "GameTheoryExtensions", "GameTheoryExtensionsTests",
    "Interaction", "InteractionTests", "Vegas", "VegasTests", "Paper",
}

# Tactics, options, tooling syntax, and trusted Lean core declarations with
# declaration-like spelling. Keep this list exact and small: it is not a
# namespace exemption.
ALLOWED = {
    "native_decide", "decide_eq_true", "simp_all", "norm_num", "push_neg",
    "omega_nat", "autoImplicit", "relaxedAutoImplicit", "warningAsError",
    "set_option", "implemented_by", "Classical.choice", "Quot.sound",
}

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque)\s+"
    r"([A-Za-z_][A-Za-z0-9_.'!?]*)"
)
FIELD = re.compile(r"^\s+([a-z][A-Za-z0-9_']*)\s*:[^=]")
CONSTRUCTOR = re.compile(
    r"^\s*\|\s*([A-Za-z_][A-Za-z0-9_']*)(?:\s*(?::|\(|\{)|\s*$)"
)
CITED = re.compile(r"`([A-Za-z_][A-Za-z0-9_.'!?]*)`")
DOC_COMMENT = re.compile(r"/-(?:!|-)[\s\S]*?-/")
PROJECT_PATH = re.compile(
    r"`((?:GameTheoryExtensions|GameTheoryExtensionsTests|Interaction|InteractionTests|Vegas|VegasTests|Paper)"
    r"(?:/[A-Za-z0-9_.-]+)*\.lean)(?::\d+)?`"
)
MARKDOWN_LINK = re.compile(r"\[[^\]]*\]\(([^)]+)\)")


def strip_lean_comments_and_strings(text: str) -> str:
    """Blank nested comments and strings while preserving offsets/newlines."""
    result: list[str] = []
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


def lean_files(roots):
    for root in roots:
        root_path = Path(root)
        if root_path.is_file() and root_path.suffix == ".lean":
            yield root_path
            continue
        top_level = root_path.with_suffix(".lean")
        if top_level.is_file():
            yield top_level
        for dirpath, _dirnames, filenames in os.walk(root_path):
            for filename in sorted(filenames):
                if filename.endswith(".lean"):
                    yield Path(dirpath) / filename


def module_name(path: Path) -> str:
    parts = path.with_suffix("").parts
    if len(parts) >= 2 and parts[:2] == ("GameTheory", "GameTheory"):
        parts = ("GameTheory",) + parts[2:]
    return ".".join(parts)


def qualify(namespace: tuple[str, ...], name: str) -> str:
    if name.startswith("_root_."):
        return name[len("_root_."):]
    return ".".join((*namespace, *name.split("."))) if namespace else name


@dataclass
class Context:
    namespace: tuple[str, ...]
    opened: tuple[str, ...]


@dataclass
class NameIndex:
    full: set[str]
    modules: set[str]
    by_short: dict[str, set[str]]
    qualified_suffixes: dict[str, set[str]]

    def add(self, name: str) -> None:
        self.full.add(name)
        self.by_short.setdefault(name.split(".")[-1], set()).add(name)
        parts = name.split(".")
        for start in range(1, len(parts) - 1):
            suffix = ".".join(parts[start:])
            self.qualified_suffixes.setdefault(suffix, set()).add(name)


def source_contexts(clean: str) -> list[Context]:
    """Return namespace/open context at the start of each source line."""
    frames: list[tuple[str, tuple[str, ...]]] = []
    opened: list[str] = []
    contexts: list[Context] = []
    for line in clean.splitlines():
        namespace = tuple(
            part for kind, frame in frames if kind == "namespace" for part in frame
        )
        contexts.append(Context(namespace, tuple(opened)))
        if match := re.match(
                r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_.']*)\s*$", line):
            frames.append(("namespace", tuple(match.group(1).split("."))))
        elif re.match(r"^\s*section(?:\s+[A-Za-z_][A-Za-z0-9_']*)?\s*$", line):
            frames.append(("section", ()))
        elif re.match(r"^\s*end(?:\s+[A-Za-z_][A-Za-z0-9_.']*)?\s*$", line):
            if frames:
                frames.pop()
        elif match := re.match(r"^\s*open\s+(.+)$", line):
            opened.extend(re.findall(r"[A-Za-z_][A-Za-z0-9_.']*", match.group(1)))
    return contexts


def index_declarations() -> NameIndex:
    """Index fully qualified declarations, constructors, fields, and modules."""
    index = NameIndex(set(), set(), {}, {})
    for path in lean_files(ROOTS_DEFINING):
        index.modules.add(module_name(path))
        clean = strip_lean_comments_and_strings(path.read_text(encoding="utf-8"))
        contexts = source_contexts(clean)
        container: tuple[str, str] | None = None
        for number, line in enumerate(clean.splitlines()):
            namespace = contexts[number].namespace
            if match := DECL.match(line):
                kind, local_name = match.groups()
                full_name = qualify(namespace, local_name)
                index.add(full_name)
                container = (
                    (kind, full_name)
                    if kind in {"structure", "class", "inductive"} else None
                )
                continue
            if line and not line[0].isspace() and line.strip():
                container = None
            if not container:
                continue
            kind, parent = container
            if kind in {"structure", "class"} and (match := FIELD.match(line)):
                index.add(f"{parent}.{match.group(1)}")
            if kind == "inductive" and (match := CONSTRUCTOR.match(line)):
                index.add(f"{parent}.{match.group(1)}")
    for module in index.modules:
        index.add(module)
    return index


def namespace_candidates(context: Context, cited: str) -> list[str]:
    candidates = []
    cited_parts = tuple(cited.split("."))
    for length in range(len(context.namespace), -1, -1):
        prefix = context.namespace[:length]
        candidates.append(".".join((*prefix, *cited_parts)) if prefix else cited)
    for opened in context.opened:
        candidates.append(f"{opened}.{cited}")
        for length in range(len(context.namespace), -1, -1):
            prefix = context.namespace[:length]
            if prefix:
                candidates.append(
                    ".".join((*prefix, *opened.split("."), *cited_parts))
                )
    return candidates


def declaration_shaped(cited: str) -> bool:
    if cited in ALLOWED or cited.endswith((".lean", ".md", ".toml", ".py", ".sh")):
        return False
    last = cited.split(".")[-1]
    camel = bool(re.search(r"[a-z][A-Z]", last))
    return last[:1].islower() and (
        "." in cited or "_" in last or camel or last.endswith(("?", "!"))
    )


def resolves(index: NameIndex, cited: str, context: Context | None) -> bool:
    if cited in ALLOWED or cited in index.full or cited in index.modules:
        return True
    first = cited.split(".")[0]
    if first in PROJECT_PREFIXES:
        return False
    if context is not None:
        if any(candidate in index.full for candidate in namespace_candidates(context, cited)):
            return True
    if "." not in cited:
        return len(index.by_short.get(cited, ())) == 1
    parts = cited.split(".")
    # Lowercase-leading dotted names conventionally use a local receiver
    # (`graph.sequentialize`). The receiver has no static project name, so
    # resolve every supplied member component after it. A lone member must be
    # globally unique; a qualified member must be a unique full suffix.
    if parts[0][:1].islower():
        member = ".".join(parts[1:])
        if "." in member:
            return len(index.qualified_suffixes.get(member, ())) == 1
        return len(index.by_short.get(member, ())) == 1
    # Markdown has no Lean namespace. A unique qualified suffix is a
    # principled shorthand there; Lean docstrings must resolve lexically.
    return context is None and len(index.qualified_suffixes.get(cited, ())) == 1


def lean_citations(path: Path, index: NameIndex):
    text = path.read_text(encoding="utf-8")
    contexts = source_contexts(strip_lean_comments_and_strings(text))
    module_parent = tuple(module_name(path).split(".")[:-1])
    for comment in DOC_COMMENT.finditer(text):
        start_line = text.count("\n", 0, comment.start())
        for offset, line in enumerate(comment.group().splitlines()):
            context = contexts[min(start_line + offset, len(contexts) - 1)]
            # Module doc comments commonly precede their namespace command.
            # The module's parent namespace supplies the same principled
            # relative lookup chain without permitting arbitrary suffixes.
            if not context.namespace:
                context = Context(module_parent, context.opened)
            for cited in CITED.findall(line):
                if declaration_shaped(cited) and not resolves(index, cited, context):
                    yield path.as_posix(), start_line + offset + 1, cited


def dangling(index: NameIndex):
    findings = []
    for path in lean_files(ROOTS_CITING):
        findings.extend(lean_citations(path, index))
    return findings


def tracked_markdown(root: Path) -> tuple[list[Path], bool]:
    if not (root / ".git").exists():
        return [], False
    try:
        tracked = subprocess.run(
            ["git", "-C", str(root), "ls-files", "-z", "--", "*.md"],
            check=True, capture_output=True,
        ).stdout.split(b"\0")
    except (OSError, subprocess.CalledProcessError) as error:
        raise RuntimeError(f"Cannot enumerate tracked Markdown: {error}") from error
    return [root / item.decode("utf-8") for item in sorted(filter(None, tracked))], True


def markdown_findings(root: Path, index: NameIndex):
    """Check local paths and declaration-shaped inline-code citations."""
    paths, checked = tracked_markdown(root)
    findings = []
    for source in paths:
        if not source.is_file():
            continue
        relative_source = source.relative_to(root).as_posix()
        for number, line in enumerate(source.read_text(encoding="utf-8").splitlines(), 1):
            for cited in PROJECT_PATH.findall(line):
                if not (root / cited).is_file():
                    findings.append((relative_source, number, cited, "file"))
            for destination in MARKDOWN_LINK.findall(line):
                destination = destination.strip().strip("<>").split("#", 1)[0]
                if not destination or "://" in destination or destination.startswith("/"):
                    continue
                destination = re.sub(r":\d+$", "", destination)
                if Path(destination).suffix.lower() not in (".md", ".lean"):
                    continue
                target = (source.parent / destination).resolve()
                if not target.is_relative_to(root.resolve()) or not target.is_file():
                    findings.append((relative_source, number, destination, "file"))
            for cited in CITED.findall(line):
                if cited.endswith(".lean") or not declaration_shaped(cited):
                    continue
                if not resolves(index, cited, None):
                    findings.append((relative_source, number, cited, "name"))
    return findings, checked


def main() -> int:
    root = Path.cwd()
    index = index_declarations()
    findings = dangling(index)
    for path, number, cited in findings:
        print(f"{path}:{number}: documentation cites unknown name `{cited}`")
    try:
        markdown, markdown_checked = markdown_findings(root, index)
    except RuntimeError as error:
        print(error)
        return 1
    if not markdown_checked:
        print("No local Git metadata: Markdown path inventory was not checked; "
              "Markdown Lean citations were not checked.")
    for path, number, cited, kind in markdown:
        if kind == "file":
            print(f"{path}:{number}: Markdown cites missing local file `{cited}`")
        else:
            print(f"{path}:{number}: Markdown cites unknown Lean name `{cited}`")
    if findings or markdown:
        print(f"\n{len(findings) + len(markdown)} dangling documentation reference(s); "
              f"{len(index.full)} qualified names indexed.")
        return 1
    print(f"No dangling documentation references ({len(index.full)} qualified names indexed).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
