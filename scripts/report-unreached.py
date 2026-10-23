#!/usr/bin/env python3
"""Report modules none of whose declarations Paper.lean, a test or an example uses.

From every declaration of Paper.lean, the test libraries and `Vegas.Examples`
(which apply the theorems to concrete programs), follow the constants each
declaration uses through the project libraries. A module with declarations but
none reached is reported with its line count. Generated names, aggregators and
the roots themselves are skipped.

`example` commands leave no declaration behind, so the walk also starts from
every project constant that a distinctive identifier in those sources may name
(outside comments and strings, matched by name suffix). This errs toward
keeping. Uses through notation or tactics in other modules stay invisible.

The script elaborates a small Lean program against the built project with
`lake env lean`, so run it after `lake build`. It reports only; `--strict`
makes a nonempty report fail.
"""

import importlib.util
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
ROOT_SOURCES = ["Paper.lean", "VegasTests", "InteractionTests", "GameTheoryExtensionsTests",
                "Vegas/Examples"]
IDENTIFIER = re.compile(
    r"(?<![A-Za-z0-9_'.!?])[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*")

SPEC = importlib.util.spec_from_file_location(
    "lean_options", pathlib.Path(__file__).with_name("check-lean-options.py"))
OPTIONS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(OPTIONS)

LEAN = r'''
import Paper
import Vegas
import Interaction
import GameTheoryExtensions
import VegasTests
import InteractionTests
import GameTheoryExtensionsTests

open Lean Elab Command

def projectPrefixes : List Name :=
  [`Vegas, `Interaction, `GameTheoryExtensions, `Paper, `VegasTests, `InteractionTests,
    `GameTheoryExtensionsTests]

def rootPrefixes : List Name :=
  [`Paper, `Vegas.Examples, `VegasTests, `InteractionTests, `GameTheoryExtensionsTests]

def mentionsFile : System.FilePath := "MENTIONS_FILE"

/-- The name and every proper suffix of it, by components. -/
def nameSuffixes (name : Name) : List Name :=
  (name.components.tails.filter (!·.isEmpty)).map
    fun parts => parts.foldl (fun acc part => acc ++ part) Name.anonymous

run_cmd liftTermElabM do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let moduleOf (name : Name) : Option Name :=
    (env.getModuleIdxFor? name).map fun index => moduleNames[index.toNat]!
  let within (prefixes : List Name) (name : Name) : Bool :=
    match moduleOf name with
    | some module => prefixes.any (·.isPrefixOf module)
    | none => false
  let mentions : NameSet :=
    (← IO.FS.lines mentionsFile).foldl (fun set text => set.insert text.toName) {}
  let mut stack : List Name := []
  for (name, _) in env.constants.toList do
    if within rootPrefixes name then stack := name :: stack
    else if within projectPrefixes name then
      let user := (privateToUserName? name).getD name
      if (nameSuffixes user).any mentions.contains then stack := name :: stack
  let mut reached : NameSet := {}
  while !stack.isEmpty do
    match stack with
    | [] => pure ()
    | name :: rest =>
      stack := rest
      if reached.contains name then continue
      reached := reached.insert name
      if let some info := env.find? name then
        let mut successors := info.getUsedConstantsAsSet.toList
        if let .inductInfo ind := info then successors := successors ++ ind.ctors
        for next in successors do
          if within projectPrefixes next && !reached.contains next then stack := next :: stack
  let mut declared : Std.HashMap Name Nat := {}
  let mut used : Std.HashMap Name Nat := {}
  for (name, _) in env.constants.toList do
    if ((privateToUserName? name).getD name).isInternal then continue
    if !within projectPrefixes name || within rootPrefixes name then continue
    if let some module := moduleOf name then
      declared := declared.insert module (declared.getD module 0 + 1)
      if reached.contains name then used := used.insert module (used.getD module 0 + 1)
  for (module, count) in declared.toList do
    IO.println s!"{module}\t{used.getD module 0}\t{count}"
'''


def distinctive(identifier: str) -> bool:
    """Long enough or shaped enough that it is unlikely to be a local name or tactic."""
    return "_" in identifier or any(c.isupper() for c in identifier[1:]) or len(identifier) >= 10


def mentions_in(text: str) -> set[str]:
    """Distinctive identifiers outside comments and strings, with their dotted
    suffixes and components. A suffix after a dot counts however short, since
    `terminal.outcome` uses `Config.outcome` through its field notation."""
    names = set()
    for identifier in IDENTIFIER.findall(OPTIONS.strip_lean_comments_and_strings(text)):
        parts = identifier.split(".")
        for start in range(len(parts)):
            suffix = ".".join(parts[start:])
            if start > 0 or distinctive(suffix):
                names.add(suffix)
        names.update(part for part in parts if distinctive(part))
    return names


def mentioned_names() -> list[str]:
    """Mentions across the root sources."""
    paths = []
    for entry in ROOT_SOURCES:
        path = ROOT / entry
        paths += [path] if path.is_file() else sorted(path.rglob("*.lean"))
    names = set()
    for path in paths:
        names |= mentions_in(path.read_text(encoding="utf-8"))
    return sorted(names)


def main() -> int:
    strict = "--strict" in sys.argv[1:]
    with tempfile.TemporaryDirectory() as directory:
        mentions = pathlib.Path(directory) / "mentions.txt"
        mentions.write_text("\n".join(mentioned_names()) + "\n", encoding="utf-8")
        program = pathlib.Path(directory) / "ReportUnreached.lean"
        program.write_text(LEAN.replace("MENTIONS_FILE", mentions.as_posix()), encoding="utf-8")
        result = subprocess.run(["lake", "env", "lean", str(program)], cwd=ROOT,
                                capture_output=True, text=True, encoding="utf-8")
    if result.returncode != 0:
        print(result.stdout + result.stderr, file=sys.stderr)
        return 2
    rows = []
    total_modules = 0
    for line in result.stdout.splitlines():
        module, used, declared = line.split("\t")
        total_modules += 1
        if int(used) == 0:
            path = ROOT / (module.replace(".", "/") + ".lean")
            lines = len(path.read_text(encoding="utf-8").splitlines()) if path.exists() else 0
            rows.append((lines, module, int(declared)))
    rows.sort(reverse=True)
    for lines, module, declared in rows:
        print(f"{lines:>7} lines  {declared:>4} declarations  {module}")
    print(f"{len(rows)} of {total_modules} modules with declarations are unreached from "
          f"Paper, the tests and the examples ({sum(row[0] for row in rows):,} lines).")
    return 1 if strict and rows else 0


if __name__ == "__main__":
    sys.exit(main())
