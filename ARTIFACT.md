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
| Source to typed graph and canonical single-policy correspondence | `Vegas/Compile/EventGraphCanonical.lean`, `Vegas/Compile/EventGraphDeviation.lean` |
| Sequential completion by dependency barriers | `Vegas/EventGraph/Sequential.lean` |
| Pending-message runtime and service | `Interaction/MessageApplication*.lean`, `Vegas/Pending/` |
| Full-source honest law under adaptive public graph scheduling | `Vegas/Compile/EventGraphScheduling.lean` |
| Full-source asynchronous deviations and Nash correspondence | `Vegas/Compile/EventGraphDeviation.lean`, `Vegas/Game/EventCompilation.lean` |
| Asynchronous pending-message service and arbitrary-player completion | `Vegas/Pending/EventService.lean`, `Vegas/Pending/EventServiceCompletion.lean` |
| Asynchronous pending-message deviation reduction | `Vegas/Pending/EventDeviationLaw.lean`, `Vegas/Pending/EventStrategicLaw.lean` |
| Full-source pending-message deviations and Nash correspondence | `Vegas/Game/EventMessageStrategic.lean` |
| Generic simulation and equilibrium transport | `GameTheoryExtensions/` |
| Paper-visible theorem selection and axiom pins | `Paper.lean` |

The proved capstones are universally quantified proofs, not conclusions
inferred from tests.
`VegasTests/EventService.lean` and the source/event-graph tests are concrete
execution regressions.

## Interpretation

The native theorem concerns decoded terminal source states. Missing native
outcomes remain an explicit `Option` case. Utilities or observations of network
traffic, latency, fees, receipts, or other runtime-only data require an
additional correspondence contract.

The commitment service is ideal. Authentication, opaque commitment behavior,
relative deadlines, reserved inclusion, and a fixed finite epoch protocol are
part of the proved target model. Every epoch uses a publicly and adaptively
chosen permutation of all events, followed by one clock tick and expiry sweep;
`ServiceFeasible` requires every deadline to be at least two ticks. Wire and
order policies may adapt to public histories. This is not a generalized fair
network theorem, and the artifact establishes neither computational
cryptography nor an EVM/ledger implementation.

`Vegas.Language` is a surface-syntax prototype with an internal `SurfaceCore`
elaboration target. Its connection to `SourceProgram` is not proved; it is
outside the active strategic tower.

`Paper.lean` is a self-contained capstone audit. Its statements delegate to
repository results and pin their proof dependencies; supporting lemmas remain
in their owning modules. The pins contain only `propext`, `Classical.choice`,
and `Quot.sound`. No library module or paper capstone contains a proof
admission.
The asynchronous graph compiler preserves and reflects same-error Nash at
compiled source profiles for utilities of the complete terminal source state.
Its unilateral deviation witness is one source-policy mixture chosen before
private setup. The graph-local scheduling theorem is separately audited.
The asynchronous pending-message game has checked completion, full-source
honest outcome, exact unilateral-deviation mixture, and same-error Nash laws
under the concrete public epoch service. The finite source-policy mixture is
chosen before private setup, leaves every opponent unchanged, and covers any
native unilateral player policy. The public wire and adaptive order response
functions are jointly predrawn in the proof; they are not restricted to fixed
command traces.
Read the [active theorem map](docs/active-tower.md) for the
formal boundary and [event-pending deviation proof](docs/event-pending-deviation.md)
for the central adversarial argument.
