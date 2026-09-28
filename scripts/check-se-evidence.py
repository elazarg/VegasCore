#!/usr/bin/env python3
"""Check that the SE checklist's evidence is load-bearing.

Every declaration cited after "Evidence:" in docs/se-proof-checklist.md must be
used by the full-language sequential-equilibrium theorem, its complete-audit
corollary, or the two horizon lemmas pinned beside it in Paper.lean. A cited
theorem that nothing depends on would make a box look closed by a result the
headline never uses. Restatements in Paper.lean (`Vegas.Paper.*`) are skipped;
that file delegates each one to its owning theorem.

The check elaborates a small Lean program against the built project with
`lake env lean`, so run it after `lake --wfail build`. It is a script rather
than a library module because Lake does not rebuild a module when only the
checklist changes.
"""

import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent

LEAN = r'''
import Vegas.Game.SourceServiceCompilation

open Lean Elab Command

/-- The statements whose dependencies count as load-bearing. -/
def evidenceRoots : List Name :=
  [`Vegas.SourceServiceSpec.audited_raw_sequentialEquilibrium_preserved,
    `Vegas.SourceServiceSpec.completeAudit_raw_sequentialEquilibrium_preserved,
    `Vegas.SourceProgram.Setup.protocol_bounded,
    `Interaction.ReactiveApplication.ResponseMenu.bounded]

/-- Backticked tokens in the "Evidence:" paragraphs of the checklist. -/
def evidenceTokens (text : String) : List String := Id.run do
  let mut inside := false
  let mut tokens : List String := []
  for line in text.splitOn "\n" do
    let trimmed := String.ofList (line.toList.dropWhile Char.isWhitespace)
    let mut body := line
    if (line.splitOn "Evidence:").length > 1 then
      inside := true
      body := String.intercalate "Evidence:" ((line.splitOn "Evidence:").drop 1)
    else if trimmed.isEmpty || trimmed.startsWith "- [" || trimmed.startsWith "#" then
      inside := false
    if inside then
      let pieces := body.splitOn "`"
      for index in [0:pieces.length] do
        if index % 2 == 1 then
          let token := pieces[index]!
          unless token.contains ' ' || token.contains '/' || token.endsWith ".lean" ||
              token.endsWith ".md" || token.isEmpty || token.startsWith "Vegas.Paper." do
            tokens := token :: tokens
  return tokens.eraseDups

/-- Local declarations, for the dependency walk. -/
def isLocal (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | none => true
  | some index =>
      let root := (env.header.moduleNames[index.toNat]!).getRoot
      root == `Vegas || root == `Interaction || root == `GameTheoryExtensions

run_cmd do
  let env ← getEnv
  let text ← IO.FS.readFile "docs/se-proof-checklist.md"
  let tokens := evidenceTokens text
  let mut resolved : List (String × Name) := []
  let mut unresolved : List String := []
  for token in tokens do
    let suffix := "." ++ token
    let candidates := env.constants.fold (init := ([] : List Name)) fun found name _ =>
      if name.isInternal then found
      else
        let text := name.toString
        if text == token || text.endsWith suffix then name :: found else found
    match candidates with
    | [name] => resolved := (token, name) :: resolved
    | _ => unresolved := token :: unresolved
  let mut reached : NameSet := {}
  let mut stack : Array Name := evidenceRoots.toArray
  while h : stack.size > 0 do
    let current := stack.back
    stack := stack.pop
    if reached.contains current then continue
    reached := reached.insert current
    let some info := env.find? current | continue
    if isLocal env current then
      for used in info.getUsedConstantsAsSet do
        unless reached.contains used do
          stack := stack.push used
  let unused := resolved.filter fun (_, name) => !reached.contains name
  unless unresolved.isEmpty && unused.isEmpty do
    throwError m!"Checklist evidence problems. Unresolved or ambiguous names: \
      {unresolved}. Cited but not used by the SE statements: {unused.map (·.2)}."
'''


def main() -> int:
    with tempfile.TemporaryDirectory() as directory:
        path = pathlib.Path(directory) / "SEEvidence.lean"
        path.write_text(LEAN, encoding="utf-8")
        result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                capture_output=True, text=True, encoding="utf-8")
    output = (result.stdout + result.stderr).strip()
    if result.returncode != 0 or "error" in output:
        print(output)
        return 1
    print("Every evidence declaration in the SE checklist is used by the SE theorem.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
