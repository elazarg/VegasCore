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

* Before adding definitions or general proof machinery, search the owning layers
  with `rg` and inspect their declaration surfaces with `lean-defs.py`. Consult
  `docs/module-architecture.md` for reusable APIs and their scope; instantiate
  existing machinery and identify missing adapter hypotheses before replacing it.
* Commit and push each stable, verified checkpoint.
* Work on sequential-equilibrium preservation beyond the fixed calendar is
  tracked in `docs/se-async-checklist.md`. Follow its methodology: boxes close
  only on checked theorems, and the target, boxes and semantics change only with
  the owner's explicit approval. Read `ephemeral/se-async-log.md` (approvals and
  work log) when present, and append to its work log.
* Configure required Lean options centrally in lakefile.toml, not with local set_option directives.
* Do not encode history into code or documentation
* Never report work as "completed" when it'd not done - e.g., when there are sorry's left that should not be there.
