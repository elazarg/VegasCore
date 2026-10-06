# Checked artifact

The active artifact contains the source language, typed graph compiler, pending
runtime, regression tests and the fixed-calendar sequential-equilibrium proof.
The [calendar capstone](Vegas/Game/SourceServiceCompilation.lean) and
[Paper](Paper.lean) state the exact theorem and audit its standard axioms.
The [checklist](docs/se-proof-checklist.md) identifies load-bearing evidence.
[Paper](Paper.lean) also states
[intended-game preservation](Vegas/Game/IntendedPreservation.lean), box H of the
[arbitrary-builder checklist](docs/se-async-checklist.md).
It states the reflection of approximate Nash equilibrium from the audited
calendar runtime ([calendar Nash](Vegas/Game/SourceServiceNash.lean)) and from
the turn-counted clients of an arbitrary contract builder
([asynchronous Nash](Vegas/Game/AsyncServiceNash.lean)). Preservation of
approximate Nash is reduced to a bound on permitted-menu deviations that is
not yet proved.

The arbitrary-builder theorem and an operational watcher/reporting refinement
remain open. The [design and plan](docs/se-schedule-generalization.md) describes
them without changing the baseline gameplay semantics. Its proposed finite
experiments must derive information and whole-deviation comparisons as well as
honest outcome laws; they are not additional checked lifting theorems.

Use the build and validation commands in [README](README.md). Reference designs,
experimental examples and unfinished proof routes are available in the
[archive](archive/se-generalization/README.md); they are not built or treated as
proof evidence.
