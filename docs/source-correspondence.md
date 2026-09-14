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

The sealed pending-message round driver supplies a concrete utility-preservation
instance in `SealedCompilation.RoundModel.utilitySimulation`. Under timely
service, normal source/native utility agreement, and a uniform cap on each
player's own timeout settlement below every source utility, it preserves and
reflects Nash and same-error epsilon-Nash at compiled profiles. Its player
policies remain unrestricted. This utility-specific theorem does not claim exact
outcome-law simulation after selective quitting. The weaker informed-continuation
condition remains open; ordinary source quit dominance does not imply the cap.

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
and the complete native trace marginal. The joint stopped-prefix/full-trace law
is exact, including the actual post-timeout continuation. The environment may
adapt to its pending-pool view. Its predrawn response may be correlated with the
focal response; the mixture may depend on the opponent profile.
For every normally completed supported pair,
`mixtureSourceCoupling_decode_of_complete_clear` proves that native event decoding
returns exactly the retained source realization, including its terminal store.
This uses binding and registration agreement, not only marginal equalities.
`SealedCompilation.resolvingRuntime_runRounds_complete` separately proves a
finite termination bound for the same resolving application: a compiled graph
with `n` nodes completes within `n * (window + 1)` rounds of the fixed-clock
driver, under arbitrary randomized player and wire policies. The fragment
certificate proves that rules are enabled and prerequisites point backward.
No roster coverage or message service is needed for termination by timeout.

`SealedResolution.runRounds_eq_tracePolicies` identifies the early-stopping
driver with a block-boundary projection of the same full invocation trace.
`SealedCompilation.exists_randomized_round_source_coupling` applies this
projection to the constructed coupling: its native marginal is exactly the
driver's stopping execution, while its source marginal remains the same
mixture of written-source deviations. Histories and pending traffic are
retained at the stopping boundary, not at the end of unused clock calls.
For a completed timeout-free boundary, decoding again returns the coupled
source realization; the continuation beyond that boundary preserves the
registrations used by its decoding and cannot introduce a timeout.

`SealedCompilation.exists_honest_round_source_coupling` supplies the original
written-source law at all-compiled profiles. Every player must occur in the
roster, periodic inclusion capacity must drain each period's possible traffic,
and the relative window must exceed the checked polling bound. At a
whole-period horizon at least the termination bound, the actual stopped
driver completes without timeout and decodes to its paired source realization.
The probability proof counts every player's original conditional draw and
predraws only the environment; it does not infer the honest law from the
unilateral-deviation mixture. `RoundModel.deviation_utility_margin_bound` uses
that mixture to charge a uniform continuation margin times the actual timeout
probability. General post-timeout source settlement and the weaker
information-conditional utility bound remain separate obligations.
