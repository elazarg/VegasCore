#!/usr/bin/env python3
"""Inventory tracked Lean source and locate repeated proof text for human review.

This is a lexical measurement, not an elaborator or proof-equivalence checker.
Body lines include term proofs and tactic-valued definitions; repeated windows
overlap and must never be summed as an estimate of removable lines.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import csv
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent.parent


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


DEFS = load_module("proof_inventory_defs", ROOT / "lean-defs.py")
POLICY = load_module("proof_inventory_policy", ROOT / "scripts/check-lean-options.py")
DECLARATION = re.compile(
    r"\b(theorem|lemma|example|def|abbrev|instance|structure|inductive|class)\s+([^\s(:{\[]+)"
)


def declaration_blocks(text):
    """Keep indented continuations across blank lines skipped by lean-defs."""
    clean = POLICY.strip_lean_comments_and_strings(text)
    pending, start, cursor = [], 1, 1
    for block in DEFS.parse_blocks(clean.splitlines()):
        first = next((line for line in block if line.strip()), "")
        continued = not first or first[0].isspace() or first.startswith(
            ("termination_by", "decreasing_by")
        )
        if pending and not continued:
            yield start, "\n".join(pending)
            pending = []
        if not pending:
            start = cursor
        pending.extend(block)
        cursor += len(block)
    if pending:
        yield start, "\n".join(pending)


def proof_bodies(text):
    for start, block in declaration_blocks(text):
        kind = DEFS.find_keyword(block)
        match = DECLARATION.search(block)
        if not match or kind not in DEFS.PROOF_KEYWORDS | DEFS.DEF_KEYWORDS:
            continue
        assign = DEFS.find_toplevel_assign(block)
        if assign < 0:
            continue
        body = block[assign + 2:]
        if kind not in DEFS.PROOF_KEYWORDS and not body.lstrip().startswith("by"):
            continue
        line = start + block[:assign + 2].count("\n")
        meaningful = [(line + offset, re.sub(r"\s+", " ", code.strip()))
                      for offset, code in enumerate(body.splitlines()) if code.strip()]
        yield {"name": match.group(2), "kind": kind, "line": start,
               "body_lines": len(meaningful), "body": meaningful}


def layer(path):
    parts = Path(path).parts
    if parts[0] == "GameTheory":
        return "GameTheory"
    if parts[0] == "Vegas" and len(parts) > 2:
        return ".".join(parts[:2])
    return parts[0].removesuffix(".lean")


def tracked_sources(root):
    def tracked(directory):
        return subprocess.check_output(
            ["git", "-C", str(directory), "ls-files", "-z", "--", "*.lean"]
        ).decode("utf-8").split("\0")
    paths = [path for path in tracked(root) if path]
    dependency = root / "GameTheory"
    if (dependency / "AGENTS.md").exists():
        paths.extend("GameTheory/" + path for path in tracked(dependency) if path)
    return sorted(set(paths))


def module_name(path):
    if path.startswith("GameTheory/"):
        path = path.removeprefix("GameTheory/")
    return path.removesuffix(".lean").replace("/", ".")


def inventory(root, paths, width):
    modules, declarations, windows = [], [], defaultdict(list)
    for path in paths:
        text = (root / path).read_text(encoding="utf-8-sig")
        clean = POLICY.strip_lean_comments_and_strings(text)
        bodies = list(proof_bodies(text))
        modules.append({"path": path, "module": module_name(path), "layer": layer(path),
                        "lines": len(text.splitlines()),
                        "proof_bodies": len(bodies),
                        "body_lines": sum(item["body_lines"] for item in bodies),
                        "imports": re.findall(r"(?m)^import\s+([\w.]+)", clean)})
        for item in bodies:
            declarations.append({key: value for key, value in
                                 {"path": path, **item}.items() if key != "body"})
            body = item["body"]
            for index in range(len(body) - width + 1):
                sample = "\n".join(code for _, code in body[index:index + width])
                digest = hashlib.sha256(sample.encode()).hexdigest()
                windows[digest].append({"path": path, "line": body[index][0],
                                        "declaration": item["name"]})
    duplicates = [locations for locations in windows.values()
                  if len({item["path"] for item in locations}) > 1]
    duplicates.sort(key=lambda items: (-len({item["path"] for item in items}),
                                       -len(items), items[0]["path"], items[0]["line"]))
    incoming = Counter(dependency for item in modules for dependency in item["imports"])
    for item in modules:
        item["direct_importers"] = incoming[item["module"]]
    return modules, declarations, duplicates


def write_csv(path, rows):
    if not rows:
        return
    with path.open("w", encoding="utf-8", newline="") as output:
        writer = csv.DictWriter(output, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "ephemeral/proof-review")
    parser.add_argument("--window", type=int, default=8)
    args = parser.parse_args()
    if args.window < 2:
        parser.error("--window must be at least two lines")
    modules, declarations, duplicates = inventory(ROOT, tracked_sources(ROOT), args.window)
    args.output.mkdir(parents=True, exist_ok=True)
    write_csv(args.output / "modules.csv", [{**item, "imports": " ".join(item["imports"])}
                                           for item in modules])
    write_csv(args.output / "declarations.csv", sorted(declarations,
              key=lambda item: (-item["body_lines"], item["path"], item["line"])))
    summary = defaultdict(Counter)
    for item in modules:
        for key in ("lines", "proof_bodies", "body_lines"):
            summary[item["layer"]][key] += item[key]
        summary[item["layer"]]["modules"] += 1
    result = {"method": "lexical tracked source; includes dependency opt-in trees",
              "window_lines": args.window, "layers": dict(sorted(summary.items())),
              "cross_file_duplicate_windows": len(duplicates)}
    (args.output / "inventory.json").write_text(json.dumps(result, indent=2) + "\n")
    (args.output / "duplicates.json").write_text(json.dumps(duplicates, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
