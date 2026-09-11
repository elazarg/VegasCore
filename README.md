# VegasCore

VegasCore is a Lean 4 foundation for executable games with partial information.
Its strict compiler path is:

```text
sequential checked source
  -> typed event graph
  -> explicit sealed-message program
  -> native public-message execution
```

The source language gives choices an explicit owner and visible environment.
Compilation retains typed fields, dependencies, guards, probability tables,
and payoff code in an event graph. The native endpoint uses the shared
`Interaction` message pool and explicit commitment service.

The checked results include source execution and event-graph correspondence,
support-level reconstruction of native executions, and focused laws for the
strict sealed-message application. Strategic preservation for the strict
pending-message compiler edge is still open and is exposed as an explicit
`SealedCompilation.StrategicCertificate` obligation.

The former application-plan path is archived under `archive/fused/`. Its
adjacent `commit; reveal` fusion emitted a value-bearing request without a
prior opaque commitment, so it was not a commitment implementation and is not
part of the active compiler or its claims.

The pending-message target is represented by the active message pool and timed
sealed adapter. Prefix refinement and ideal-service hiding are checked, but the
whole-prefix deviation extraction and whole-program strategic composition are
still open. Adaptive public scheduling, censorship resistance, concrete
commitment cryptography, and EVM execution correctness also remain open.

The active libraries are `GameTheoryExtensions`, `Interaction`, `Vegas`,
the retained tests, and the source/native paper audit. See
[the artifact guide](ARTIFACT.md), [module boundaries](docs/module-architecture.md),
and [compilation design](docs/compilation-design.md).

## Build

```text
git submodule update --init --recursive
lake exe cache get
python scripts/check-doc-references.py
python scripts/check-lean-options.py
python scripts/check-module-boundaries.py
python -m unittest discover -s scripts -p "test_*.py"
lake --wfail build
```

GameTheory is a pinned, separately maintained software dependency. General
game-theoretic simulation results live under GameTheory namespaces; Vegas owns
the source language, event-graph compiler, and its native integration.

## Paper target and proof status

The manuscript in the separate `overleaf/` repository still describes the
earlier split and must be revised against the active tower. The single active
`Paper.lean` audit contains only direct delegations to proved repository
theorems; it has no admissions and does not count archived claims. The exact
active layering and the remaining pending-message strategic obligation are
listed in [the active tower](docs/active-tower.md).

A successful Lean build checks the active proof terms. It is not evidence that
the separate manuscript's prose or claim registry has caught up with this
migration.

Readable source material for porting is preserved in the
[proof reference archive](archive/fused/README.md), outside all active libraries.
