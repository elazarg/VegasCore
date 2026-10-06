# Checked artifact

The active artifact contains the source language, typed graph compiler, pending
runtime, regression tests and the fixed-calendar sequential-equilibrium proof.
The [calendar capstone](Vegas/Game/SourceServiceCompilation.lean) and
[Paper](Paper.lean) state the exact theorem and audit its standard axioms.
The [checklist](docs/se-proof-checklist.md) identifies load-bearing evidence.
[Paper](Paper.lean) also states
[intended-game preservation](Vegas/Game/IntendedPreservation.lean), tracked in
the [arbitrary-builder checklist](docs/se-async-checklist.md).
It states the same-slack correspondence of approximate Nash equilibrium on the
audited calendar runtime, in both directions
([calendar Nash](Vegas/Game/SourceServiceNash.lean)); its forward direction
rests on every permitted-menu deviation having the typed outcome law of a source
deviation ([deviation law](Vegas/Game/SourceServiceDeviationReadout.lean)). It
also states the approximate correspondence of approximate Nash between a source
profile and the turn-counted clients of an arbitrary contract builder, with
slack twice the deferral weight times the payoff range
([asynchronous Nash](Vegas/Game/AsyncServiceNash.lean),
[first-turn bound](Vegas/Game/AsyncServiceDeviationBound.lean)), on every
admitting response menu and in particular on the audited bounded raw ledger,
which admits the clients
([raw-ledger Nash](Vegas/Game/AsyncServiceRawNash.lean),
[client policy](Vegas/Game/SourceServiceClientPolicy.lean)); with the
first-turn timing the slack is zero and the correspondence is exact. Its forward
direction rests on every native policy against the first-turn clients having
the typed outcome law of a source deviation whose bindings may fail
([asynchronous deviation law](Vegas/Game/AsyncDeviationReadout.lean)). Every
profile extending an approximate Nash equilibrium of the intended game is one of
the source game under the forfeit pass
([intended Nash](Vegas/Game/IntendedNash.lean)), and its compiled raw profile is
one of the audited calendar runtime
([intended calendar Nash](Vegas/Game/IntendedServiceNash.lean)); its turn-counted
clients are an approximate Nash equilibrium under every contract builder
([first-turn bound](Vegas/Game/AsyncServiceDeviationBound.lean)), and its
first-turn clients an exact one on the bounded raw ledger, with the intended
joint law ([raw-ledger Nash](Vegas/Game/AsyncServiceRawNash.lean)).

The arbitrary-builder sequential-equilibrium theorem and an operational watcher/reporting refinement
remain open. The [design and plan](docs/se-schedule-generalization.md) describes
them without changing the baseline gameplay semantics. Its proposed finite
experiments must derive information and whole-deviation comparisons as well as
honest outcome laws; they are not additional checked lifting theorems.

Use the build and validation commands in [README](README.md). Reference designs,
experimental examples and unfinished proof routes are available in the
[archive](archive/se-generalization/README.md); they are not built or treated as
proof evidence.
