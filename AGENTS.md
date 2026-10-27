# Agent Instructions

## Project Purpose

VegasCore is a foundation for a game-theory-oriented programming language. The
core use case is to write executable descriptions of games with partial
information, prove and analyze their game-theoretic properties, and carry those
results through to concrete runtimes. Blockchain runtimes, especially the EVM,
are a major target, but the abstractions should remain runtime-general.

## API Compatibility

This project has zero API compatibility requirements.

Do not preserve old names, wrappers, aliases, deprecation shims, migration
layers, or compatibility documentation unless a human explicitly asks for them.
Prefer clean domain terminology and coherent internal APIs over backwards
compatibility. When renaming or refactoring, update all callers and docs.

# Notes

* Every mathematical result or invariant stated in the maintained paper must
  have an exact guarded axiom pin in Paper.lean, whether or not another theorem
  uses it. A technical import or dependency exception must identify the result,
  explain the obstacle, and document its separate checked audit. Definitions
  used to describe a model do not by themselves require theorem pins.
* Paper.lean pins nothing else. The build rejects `sorry` and the source
  policy rejects axiom declarations and trust escape hatches throughout the
  tree, so research, library and test results need no axiom pin.
* Before adding definitions or general proof machinery, search the owning layers
  with `rg` and inspect their declaration surfaces with `lean-defs.py`. Consult
  `docs/module-architecture.md` for reusable APIs and their scope; instantiate
  existing machinery and identify missing adapter hypotheses before replacing it.
* Commit and push each stable, verified checkpoint.
* The active research scope is checked non-concurrent SE preservation; see
  `docs/sequential-se-open-problems.md`. The broader fixed target and checklist
  are preserved at the checkpoint linked from `docs/archives.md`; their boxes
  and semantics are not changed by pruning. Only checked theorems close proof
  obligations. Read `ephemeral/se-async-log.md` (approvals and work log) when
  present, and append to its work log.
* Plan and checklist labels (box names such as S1 or H, step numbers, question
  or counterexample tags) never appear in Lean declaration or module names or in
  docstrings; describe the mathematics instead.
* Configure required Lean options centrally in lakefile.toml, not with local set_option directives.
* Do not encode history into code or documentation
* Never report work as "completed" when it'd not done - e.g., when there are sorry's left that should not be there.
