# Source and event-graph correspondence

The source meaning is the independent written-order semantics of a checked
program. Compilation allocates source bindings to typed graph fields and turns
source operations into dependency-constrained events.

The checked correspondence establishes:

- supported source denotations are genuine small-step source executions;
- source-visible decision environments and compiled graph reads agree under
  the allocation invariant;
- compiled guarded local decisions have the source choice law;
- complete compiled declared-read policy executions have exactly the written
  source's terminal-environment law;
- every arbitrary declared-read graph kernel has a uniform playerwise source
  backtranslation, with exact unilateral outcome laws against unchanged
  opponents;
- graph readiness and terminal reconstruction respect source dependencies and
  payoff evaluation.

`Vegas/Compile/SourceCorrespondence.lean` proves the whole-program laws by a
coupling with the actual graph runner. `Vegas/Game/SourceGraph.lean` constructs
`WFProgram.sourceGraphSimulation` and derives Nash and same-error epsilon-Nash
equivalence at compiled profiles. The certificate has no assumed simulation
field. It applies to every checked core program and a finite player set;
samples, nontrivial guards, mixed field types, and initial bindings are allowed.
Each policy decision uses a finite distribution, but the action types need not
be finite. The stronger finite-domain assumptions needed by other strategic
presentations are not imposed on this edge.

The decoded observation returns `some` of the entire terminal source
environment; nonterminal graph states return `none`. The complete execution
law proves that `none` has zero probability. This decoder is for analysis and
does not publish sealed fields to players.

This is a semantic compiler edge within the tower. Its target strategy sees
only a commitment node's declared reads, not a message history or scheduler
signal. The separate behavioral-frontier presentation requires its own
information-locality and single-ready-node correspondence; the concrete
source certificate here does not assume or establish that correspondence.

The active sealed-message edge does not yet claim a runtime-to-source strategy
translation. `SealedCompilation.StrategicCertificate` states the missing edge
explicitly: a concrete runtime must supply the honest outcome law and represent
each considered unilateral deviation by a finite mixture of source deviations.
The generic GameTheory layer then proves the expected-utility guarantee and
same-error approximate-Nash equivalence. When informed quitting changes the
outcome law, `UtilitySimulation` can instead prove Nash preservation through
whole-program utility bounds. The concrete pending-message instance of either
interface remains open.

The resolving message runtime has a checked whole-prefix registration read
bound, `SealedFragment.resolvingBindingLaw_read_bound`. It executes compiled
opponents with assigned source values against an arbitrary randomized native
deviator and full-pool environment. The focal registration law, stopped at the
first timeout, is unchanged when assigned honest values differ only at handles
not disclosed before that source decision. This is an input to the causal
backtranslation. `SealedCompilation.exists_randomized_source_coupling` combines
the extracted written-source policy, exact honest-kernel probabilities, and
trace-preserving focal and environment predrawing. For every randomized unilateral
replacement and randomized environment policy, it constructs a finite
mixture of source/native couplings with the ordinary source-mixture marginal
and the complete native marginal. The joint stopped-prefix/final-native law
is exact, including the actual post-timeout continuation. The environment may
adapt to its pending-pool view. Its predrawn response may be correlated with the
focal response; the mixture may depend on the opponent profile.
For every normally completed supported pair,
`mixtureSourceCoupling_decode_of_complete_clear` proves that native event decoding
returns exactly the retained source realization, including its terminal store.
This uses binding and registration agreement, not only marginal equalities.
Fair-service completion, the all-compiled honest law, post-timeout settlement,
and the informed-quitting utility bound remain separate obligations.
