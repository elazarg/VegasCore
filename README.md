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
pending-message compiler edge is still open.

The application-plan path remains in the tree only while it is being removed.
Its adjacent `commit; reveal` fusion emits a value-bearing request without a
prior opaque commitment, so it is not a commitment implementation and is
excluded from the strict path and its claims.

The pending-message target adds observable delivery and reaction, first under
the concrete block service and then under adaptive public scheduling.
Local service, checkpoint, prefix,
first-poll, delivery, and reaction lemmas are checked; whole-prefix extraction
and whole-program composition remain open. Censorship resistance, concrete
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

The manuscript in the separate `overleaf/` repository and its full target
registry, `paper-claims.json`, are unchanged. `paper-obligations.json` records
claims without an active proof. The single `Paper.lean` audit delegates proved
statements to repository theorems and records concrete open targets with
explicit `sorry` proofs. These admissions are confined to the audit and are
not dependencies of the libraries. The strict completion gate is:

```text
python scripts/check-paper-claims.py
```

It fails while any registered obligation or admitted audit theorem is open. For development, add
`--allow-open-obligations` to validate the registry and report the remaining
obligations; CI uses this explicitly labeled progress mode. A successful Lean
build or progress audit is not completion of the paper's theorem target.

Readable source material for porting is preserved in the
[proof reference archive](archive/split/README.md), outside all active libraries.
