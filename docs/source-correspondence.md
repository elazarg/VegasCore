# Source and event-graph correspondence

The source meaning is the independent written-order semantics of a checked
program. Compilation allocates source bindings to typed graph fields and turns
source operations into dependency-constrained events.

The retained correspondence establishes:

- supported source denotations are genuine small-step source executions;
- source-visible decision environments and compiled graph reads agree under
  the allocation invariant;
- compiled guarded local decisions have the source choice law;
- graph readiness and terminal reconstruction respect source dependencies and
  payoff evaluation.

These statements concern the sequential source and its event graph. Any
game-theoretic interpretation is derived separately and is not an intermediate
runtime architecture.

For the fixed windowed native service, the correspondence continues through a
complete strategic theorem: arbitrary finite-support randomized unilateral
runtime policies yield finite mixtures of legal source deviations, while the
compiled honest profile retains the source public-result law. The pending
message target seeks the same strength, first for the concrete delivery service
and then for adaptive public scheduling: pure whole-prefix extraction first,
randomized linearity second, then guarantees and same-error approximate-Nash
equivalence. The concrete delivery laws are explicit admitted targets in
`Paper.lean`; the stronger scheduler and outcome scope remains part of the
paper target.
