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

The active sealed-message edge does not yet claim a runtime-to-source strategy
translation. `SealedCompilation.StrategicCertificate` states the missing edge
explicitly: a concrete runtime must supply the honest outcome law and represent
each considered unilateral deviation by a finite mixture of source deviations.
The generic GameTheory layer then proves the expected-utility guarantee and
same-error approximate-Nash equivalence. The former fixed-windowed theorem and
its delivery refinements are retained only in `archive/fused/` while this
backtranslation is rebuilt for the strict edge.
