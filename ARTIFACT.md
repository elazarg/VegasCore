# Artifact and validation guide

## Reproduction

Use the pinned Lean toolchain and dependency revisions:

```text
git submodule update --init --recursive
lake exe cache get
python scripts/check-doc-references.py
python scripts/check-lean-options.py
python scripts/check-module-boundaries.py
python -m unittest discover -s scripts -p "test_*.py"
lake --wfail build
```

Do not run `lake update` when reproducing a revision. The cache only accelerates
the subsequent kernel-checked build.

## What is checked

| Boundary | Owning code |
| --- | --- |
| Source execution and safety | `Vegas/Source/` |
| Source to typed graph | `Vegas/Compile/Graph*.lean`, `Vegas/Game/GraphCompilation.lean` |
| Private setup transport | `Vegas/Game/GraphSetup.lean` |
| Pending-message runtime and service | `Interaction/MessageApplication*.lean`, `Vegas/Pending/` |
| End-to-end completion, honest law, deviations, arbitrary observations, Nash | `Vegas/Game/GraphMessages.lean` |
| Full-source honest law under adaptive public graph scheduling | `Vegas/Compile/EventGraphScheduling.lean` |
| Generic simulation and equilibrium transport | `GameTheoryExtensions/` |
| Paper-visible theorem selection and axiom pins | `Paper.lean` |

The capstones are universally quantified proofs, not conclusions inferred from
tests. `VegasTests/GraphMessages.lean` and the retained source/graph tests are
concrete execution regressions.

## Interpretation

The native theorem concerns decoded terminal source states. Missing native
outcomes remain an explicit `Option` case. Utilities or observations of network
traffic, latency, fees, receipts, or other runtime-only data require an
additional correspondence contract.

The commitment service is ideal. Authentication, canonical phase order,
relative deadlines, reserved inclusion, and bounded reaction slots are part of
the proved target model. The artifact establishes neither computational
cryptography nor an EVM/ledger implementation.

`Vegas.Language` is a surface-syntax prototype with an internal `SurfaceCore`
elaboration target. Its connection to `SourceProgram` is not proved; it is
outside the active strategic tower.

`Paper.lean` is a self-contained capstone audit. Proved statements delegate to
repository results and pin their proof dependencies; supporting lemmas remain
in their owning modules. Its asynchronous graph deviation target is explicitly
admitted and has `sorryAx` in its pin; it is not a checked result.
Read the [active theorem map](docs/active-tower.md) for the
formal boundary and [pending deviation extraction](docs/pending-deviation-extraction.md)
for the central adversarial argument.
