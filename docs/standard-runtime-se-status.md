# What is known about SE preservation in the standard runtime

Analysis by Codex.

**We do not currently have a general SE-preservation theorem for the actual
asynchronous audited runtime. We also do not have a checked impossibility
theorem for that full target.** An independently reviewed
[native paper counterexample](commit-reveal-research/native-late-action-analysis.md)
refutes the uniform preservation claim with collateral fixed before the
builder, under its stated collateral bounds. Its full-runtime Lean
formalization remains outstanding. The pinned calendar theorem is a positive
result for a stronger scheduling interface; the pinned late-leak and
settle-late negatives concern comparison games.
Here "standard" means this repository's `AsyncContract` runtime model; its
sure protected-service assumption is not a claim about an unconditional
liveness guarantee on a deployed blockchain.

**Source admission matters.** The general asynchronous Nash pins cover every
binding-admission interface, including immediate failed bindings and choices
varying between sites. Their admission argument distinguishes
`CommitmentInterface.values` from the complete
`CommitmentInterface.forfeiture` interface. The calendar SE theorem and the
intended-game compositions retain their value-binding specialization. Later
reveals may withhold or fail validation in that source game; the intended
game further requires predicted accepting bindings and mandatory openings.
The [checked runtime boundaries](commit-reveal-research/checked-runtime-boundaries.md)
give the precise positive scope and the operational and belief lemmas for the
native SE obstruction.
Its three-instruction source is now compiled to a checked family of actual
partially public native services: the full raw-history contract, erasure
independence, message alphabet, finite nature and exact early observation laws
are proved. The remaining impossibility obligations concern full information
fibers, relative likelihoods and sequential incentives, not builder
admissibility.

## Checked positive results

- **SE existence in the bounded runtime:** finite response menus, finite
  branching of nature, a fixed horizon and the runtime's remembered
  observations and responses give an SE for arbitrary realized payoffs.
  In particular, the partially public three-instruction native example has
  an SE at every finite lottery weight, without collateral-margin assumptions.
  This is existence in the actual runtime, not preservation of a selected
  source outcome. See
  [the existence result](commit-reveal-research/checked-runtime-boundaries.md#sequential-equilibria-exist-in-the-bounded-runtime).
- **Source to the ideal concurrent event graph:** the pinned
  `Vegas.Paper.concurrent_event_nash_iff` gives exact same-error Nash
  correspondence for compiled profiles of the failure-aware source game,
  including binding failure, under the ideal graph's public scheduler. This
  graph permits independent commitments to complete in either order between
  public barriers. It does not include pending-message traffic or the native
  audit; see [Paper.lean](../Paper.lean).
- **Audited calendar compiler:** every source SE has a native raw-runtime SE
  preserving the required outcome and settlement law, under the theorem's
  service, audit, coverage and deposit hypotheses. Pending traffic can be
  observed; the calendar supplies reliable settlement and the scheduling
  structure used by the information and consistency proof. See
  `Vegas.Paper.source_audited_raw_sequential_equilibrium` in
  [Paper.lean](../Paper.lean). The intended-game composition is
  `Vegas.SourceServiceSpec.intended_audited_raw_sequentialEquilibrium` in
  [IntendedServiceCompilation.lean](../Vegas/Game/IntendedServiceCompilation.lean),
  whose standard axioms are guarded in Paper.
- **Exact asynchronous Nash correspondence:** for arbitrary timely contract
  builders with a barrier-ordered graph, including sequential and
  concurrent-binding modes, the compiled first-opportunity clients are an
  epsilon-Nash equilibrium exactly when their full-source profile is one,
  with the same epsilon. The audit need only be authentic and its deposit
  nonnegative; this theorem does not require a positive coverage rate.
  The intended-game theorem adds the forfeit pass and preserves the joint
  typed-outcome and realized-settlement law exactly. See
  `Vegas.Paper.async_first_turn_nash_iff` and
  `Vegas.Paper.intended_async_first_turn_nash` in [Paper.lean](../Paper.lean).
  These compare source profiles with their compiled profiles, rather than
  asserting that every equilibrium of the runtime decompiles to the source.
  Every binding-admission interface is covered, and the clients preserve the
  exact joint terminal-store and realized-settlement law even when binding
  failure is admitted. The latter is
  `Vegas.AsyncServiceSpec.firstTurnClientProfile_settlement_law` in
  [AsyncServiceRawNash.lean](../Vegas/Game/AsyncServiceRawNash.lean).
  The versions with voluntary deferral have Nash error at most the source
  error plus twice the total deferral weight times the runtime payoff range;
  the intended outcome-law error is at most the deferral weight. They are
  `Vegas.Paper.async_client_nash_correspondence` and
  `Vegas.Paper.intended_async_client_nash`. None asserts SE.
- **Intended opening clients, including concurrent reveals:** a specialized
  asynchronous Nash theorem goes beyond that barrier-ordered correspondence.
  Under its well-formedness, forfeit, authentic audit, nonnegative deposit
  and payoff-bound hypotheses, it constructs an effectively disclosing
  extension for the actual bounded raw menu and gives the same
  deferral-dependent Nash and law-error bounds in every dependency mode.
  At zero deferral these are exact. The full raw-menu capstone is
  `Vegas.Paper.intended_opening_client_nash` in [Paper.lean](../Paper.lean),
  delegating to [IntendedOpeningNash.lean](../Vegas/Game/IntendedOpeningNash.lean).
- **Concrete source publication failure:** every intended SE of the
  three-instruction Boolean-opening/answer-commitment/answer-opening source
  extends to a source SE permitting failed publications, when the forfeit
  covers both players' gross payoff ranges. It preserves the joint terminal
  store and payoff law. Every intended SE has the same Safe outcome, and an
  actual source SE with optional failed publications preserves that specified
  initialized store/payoff law. Binding admission is value-only. This is a source
  result, before adding network timing; see
  [the checked source instance](commit-reveal-research/checked-runtime-boundaries.md#failed-publications-in-the-concrete-source-game).
- **Actual final-opening incentives:** in the initialized two-commitment
  recovery example, a canonical final opening dominates all raw responses
  under every belief over legal decision histories. Its expected advantage
  is at least the forfeit's excess over the gross payoff range times the
  probability of failed publication. This covers arbitrary stochastic
  responses and later policies, including off-path histories, but is specific
  to that recovery scheduler's final activation. It does not construct an SE
  assessment; see
  [the checked native incentive](commit-reveal-research/checked-runtime-boundaries.md#a-final-runtime-opening-is-optimal-under-every-belief).
- **Final opening in the three-instruction native example:** after a clean
  accepted answer commitment, at the actual final callback while publication
  is ready and timely, canonical opening dominates every raw response. Its
  expected advantage under every belief is at least `D` times the alternative's
  failure probability, for every nonnegative forfeit `D`. The audit need only
  be authentic and Bob's deposit nonnegative. The comparator uses his own
  recall and observation. The actual bounded-menu and full information-set
  adapters also give an SE consequence: at any information set with one such
  clean representative, every native SE has zero final-publication failure
  probability when `D>0`. An epsilon bound on the corresponding whole-policy
  deviation gives failure probability at most `epsilon/D`. These are local
  consequences, not a source SE-preservation theorem. See
  [the concrete runtime boundaries](commit-reveal-research/checked-runtime-boundaries.md).
- **Fully observed late-opening comparison:** for every inclusion probability
  between zero and one, a checked comparison family with intrinsic forfeit
  twice its reward preserves every intended source SE by a target SE. This
  is a finite comparison game, not a general source-language compiler
  adapter. See [the actual-runtime analysis](actual-runtime-late-opening-analysis.md).

The last result is useful because it prevents attributing the old negative
example merely to public pending messages and high late inclusion probability.
Both properties coexist with preservation in that comparison family.

## Checked negative results and their limits

The selective late-leak game has no preserving target SE in its stated
parameter regime. Its distinguishing information pattern is essential:
different late emissions need not reveal the value before the receiver's
irreversible choice. A public network with propagation delay can have such
a distinction. The stronger pinned
`Vegas.Paper.settle_late_not_preserved_for_every_margin` handles both late
opportunities, repeated partial pending observations and additional signals
with a capped charge. It remains a comparison game, without a checked
source-program/native-runtime embedding.

The [full native paper construction](commit-reveal-research/native-late-action-analysis.md)
supplies that type of embedding separately, including the entire declared
bounded raw menu, the actual audit, public chance builder, readiness rules and
authentic opening certificates. For each fixed sufficiently large forfeit
and sender/receiver audit deposits, sufficiently reliable late inclusion
prevents every native SE from preserving the selected source joint law. The
builder satisfies the declared service properties; it need not know private
types or collude with players. The result concerns uniform preservation over
this service class, not absence of equilibria in the runtime or failure of
every blockchain configuration. Mechanizing this construction is a missing
capstone. The [async checklist](se-async-checklist.md) retains its existing
owner-controlled target and boxes.

The checked operational boundary is sharper: an actual initialized opening
outside its protected window can be accepted with probability one by a
builder satisfying both the full service contract and all-view erasure
independence. Thus these two requirements alone provide no positive uniform
late-failure probability. The finite-weight partially public three-instruction
family gives the nondegenerate version: exact initialized and full-horizon
late acceptance `w/(1+w)`, with strictly positive final failure for every
finite nonnegative weight and their conjunction for the same builder.
These are execution results, not impossibility theorems about SE; see
[the checked boundaries](commit-reveal-research/checked-runtime-boundaries.md#the-service-contract-gives-no-uniform-late-failure-floor).

There is also a checked negative theorem for a nearby probabilistic backend.
Mix the actual public controller with a positive probability of waiting on
each runtime round. For a nonempty program and a finite runtime horizon,
there is positive probability that its source readout remains unfinished.
Every source terminal law is complete, so **no native behavioral profile**
can realize that exact law; this excludes Nash, PBE and SE profiles equally.
The primitive all-wait event gives the quantitative total-variation lower
bound. This backend keeps the real application, initialization, observation
interface and raw menus, but weakens sure protected service. It is not a
counterexample under the unchanged asynchronous contract. See
[the probabilistic-runtime analysis](probabilistic-runtime-preservation.md).

## Stronger positive mathematics, not yet checked compiler theorems

The [protected native proof](commit-reveal-research/native-protected-execution.md)
preserves every intended source SE in a first-ready restriction of the actual
serial runtime. It retains adaptive public scheduling, actual private packet
samples and full recall, with no invented public timing transcript. It is a
reviewed paper proof, rather than a checked native theorem. Extending it to
all raw timing and packet choices is a separate problem, and the native
counterexample defeats the unrestricted uniform extension.

The [public disclosure-phase proof](full-public-disclosure-phase-preservation.md)
implements every source Nash outcome, hence every source PBE and SE outcome,
by a target SE. It allows lawful withholding, correlated private types with
full joint support, and arbitrary finite value-dependent late inclusion
probabilities. It needs a surely successful protected opening and an intrinsic
failure forfeit above the sender's base payoff range. Its restrictions include
an immutable disclosed value, one emitted opening and no intervening strategic
choices. The [public-reset composition](public-reset-phase-se-preservation.md)
extends it to phases separated by genuine public subgames already in the
source. Retained hidden state and general raw packet behavior remain outside
these proofs.

The [vanishing-noise proof](noisy-runtime-approximate-se-preservation.md)
gives another positive target: exactly consistent assessments with vanishing
whole-continuation sequential regret and convergent outcome laws for every
selected source SE. It needs a fixed finite game and information structure,
bounded fixed payoffs, and uniformly small primitive chance errors at every
source-compatible history, including deviations. It does not promise nearby
exact SEs, and its actual-runtime tree adapter remains unformalized.

## What remains to pin or determine

The strongest reviewed results about the current source/runtime pair are not
all machine checked. The main missing pins are the full native uniform SE
counterexample, the protected first-ready positive, and the same-fixture weak
PBE construction described below. No claim of maximality follows from the
existing capstones: other restricted positive results or stronger negatives
may still be provable.

For a useful general SE positive, public service or settlement properties must
exclude the native counterexample's mechanism. Accepted late openings can be
audit clean, while rare failure continuations force type-dependent timing and
change successful posteriors. Sure protected service and a fixed source
horizon alone do not control that effect. Results with extra delivery-risk
bounds, different failure settlement, or explicit communication remain
separate candidate interfaces with their own source and action scopes.

A weaker intrinsic-forfeit-only concurrent comparison already exhibits timing
incentives despite complete public observation; a sufficiently large audit
charge repairs that example. See
[the concurrent-disclosure analysis](concurrent-disclosure-se-boundary.md).
It therefore does not refute the intended audited target by itself; the full
native uniform negative rests on the separate two-late-opening construction.

We likewise lack a general actual-runtime PBE-preservation theorem. The
disclosure-phase paper result covers PBE outcomes by constructing a target SE;
it does not establish that weakening SE consistency to PBE solves every raw
asynchronous case. The
[same native counterexample has a preserving weak PBE](commit-reveal-research/native-weak-pbe.md)
in a reviewed paper proof, where Bayes' rule is required only at decisions
reached with positive equilibrium probability. That precise convention permits
off-path beliefs which need not share an SE consistency sequence. This is not
a general PBE preservation theorem.
