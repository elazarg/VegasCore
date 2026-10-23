#!/usr/bin/env python3
"""Report modules none of whose declarations Paper.lean or a test uses.

From every declaration of Paper.lean and the test libraries, follow the
constants each declaration uses through the project libraries. A module with
declarations but none reached is reported with its line count. Generated
names, aggregators and the roots themselves are skipped. Declarations used only
inside `example` commands or by elaboration (notation, tactics) do not count.

The script elaborates a small Lean program against the built project with
`lake env lean`, so run it after `lake build`. It reports only; `--strict`
makes a nonempty report fail.
"""

import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent

LEAN = r'''
import Paper
import VegasTests
import InteractionTests
import GameTheoryExtensionsTests

open Lean Elab Command

def projectPrefixes : List Name :=
  [`Vegas, `Interaction, `GameTheoryExtensions, `Paper, `VegasTests, `InteractionTests,
    `GameTheoryExtensionsTests]

def rootPrefixes : List Name :=
  [`Paper, `VegasTests, `InteractionTests, `GameTheoryExtensionsTests]

run_cmd liftTermElabM do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let moduleOf (name : Name) : Option Name :=
    (env.getModuleIdxFor? name).map fun index => moduleNames[index.toNat]!
  let within (prefixes : List Name) (name : Name) : Bool :=
    match moduleOf name with
    | some module => prefixes.any (·.isPrefixOf module)
    | none => false
  let mut stack : List Name := []
  for (name, _) in env.constants.toList do
    if within rootPrefixes name then stack := name :: stack
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


def main() -> int:
    strict = "--strict" in sys.argv[1:]
    with tempfile.TemporaryDirectory() as directory:
        program = pathlib.Path(directory) / "ReportUnreached.lean"
        program.write_text(LEAN, encoding="utf-8")
        result = subprocess.run(["lake", "env", "lean", str(program)], cwd=ROOT,
                                capture_output=True, text=True, encoding="utf-8")
    if result.returncode != 0:
        print(result.stdout + result.stderr, file=sys.stderr)
        return 2
    rows = []
    total_modules = total_used = 0
    for line in result.stdout.splitlines():
        module, used, declared = line.split("\t")
        total_modules += 1
        total_used += int(used) > 0
        if int(used) == 0:
            path = ROOT / (module.replace(".", "/") + ".lean")
            lines = len(path.read_text(encoding="utf-8").splitlines()) if path.exists() else 0
            rows.append((lines, module, int(declared)))
    rows.sort(reverse=True)
    for lines, module, declared in rows:
        print(f"{lines:>7} lines  {declared:>4} declarations  {module}")
    print(f"{len(rows)} of {total_modules} modules with declarations are unreached from "
          f"Paper and the tests ({sum(row[0] for row in rows):,} lines).")
    return 1 if strict and rows else 0


if __name__ == "__main__":
    sys.exit(main())
