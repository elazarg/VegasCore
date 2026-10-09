# Checked preservation results and runtime boundaries

Analysis by Codex.

The strongest checked general result for the asynchronous message runtime is
**exact Nash correspondence for every binding-admission interface**. General
sequential-equilibrium preservation, and its full native counterexample, are
still missing. The results below distinguish a compiler theorem, operational
runtime facts, and the belief argument needed for the SE obstruction.

## Exact native Nash correspondence

The source program has a fixed finite sequence of sampling, commitment,
publication and return instructions. A commitment chooses a typed value. Its
interface may also permit immediately installing a failed commitment, at any
chosen subset of commitment sites. A later publication can withhold or fail
its validation. This theorem covers every such interface, including the
complete failure-aware source language.

The target is the existing bounded signed-message runtime. Players may use
every permitted raw response, including silence and malformed submissions.
The builder reads public history and chooses activations, inclusions, clock
advances and expiry. The declared service contract guarantees sufficiently
early owner opportunities, timely receipts for sole protected packets, and
completion by the target horizon. Commitments hide their private values;
pending opening packets can be observed. Fees, capital costs and strategic
miners are absent from this runtime game.

The builder is a fixed public chance rule, not another strategic player. Each
configured game evaluates strategies against that rule; a statement uniform
over builders does not mean that players optimize against an unspecified
distribution over builders. Such uncertainty would require a separate game
or robust equilibrium definition. Ideal cryptography, authenticated authors
and the declared sure protected-service promises are assumed. The results
do not model reorganization, finality risk, outside communication, coalitions
or resource and fee markets. In particular, an SE theorem for this interface
would still need an implementation argument for a deployed blockchain.

"Full raw menu" means every modeled submission within the declared finite
alphabet and candidate capacity. It does not mean every possible blockchain
transaction byte string. The public packet consists of its authenticated
identifier, application call, optional ideal certificate and readiness token.
Private submission forms which emit the same packet are retained as different
remembered actions, but concrete signature randomness, proof encodings,
auxiliary transaction fields and arbitrary outside messages are not separate
public signaling choices in this game. Cryptographic hiding alone would not
justify erasing any such field whose value a player can choose and others can
observe. A refinement exposing those choices needs a separate information and
incentive argument.

For a barrier-ordered compiled graph, each player makes its source decision
at its first suitable opportunity. Then, for every nonnegative audit deposit
and every authentic audit,

> The compiled profile is an epsilon-Nash equilibrium against all bounded raw
> deviations if and only if its source profile is an epsilon-Nash equilibrium,
> with exactly the same epsilon.

No positive audit-coverage rate or builder-dependent deposit is needed. The
theorem quantifies over every builder satisfying the declared service
properties. It compares a source profile with its compiled profile; it does
not assert that every runtime equilibrium is a compiled source equilibrium.

The checked pin is `Vegas.Paper.async_first_turn_nash_iff` in
[Paper.lean](../../Paper.lean). Its explicit admission argument may be
`CommitmentInterface.values`, `CommitmentInterface.forfeiture`, or a choice
varying between binding sites. Successful value-binding source deviations
are admitted by every interface. The compiler's existing deviation readout
and value-binding purification supply the forward comparison.

The clients also preserve the exact joint law of the typed terminal store and
realized net-payoff vector, including randomized audit settlement:
`Vegas.AsyncServiceSpec.firstTurnClientProfile_settlement_law` in
[AsyncServiceRawNash.lean](../../Vegas/Game/AsyncServiceRawNash.lean). An admitted
immediate binding failure has an ordinary conformant opaque packet with no
opening material; it is not represented by silently missing the binding.
Prescribed packets incur no audit charge. Source failure payoffs, including
an explicitly applied forfeit, remain part of the utility being preserved.

If the clients voluntarily defer with total deferral weight delta, the
two-way Nash error is at most epsilon plus `2 * delta * R`, where `R` bounds
the range of realized runtime payoffs. This is
`Vegas.Paper.async_client_nash_correspondence`. The separate intended-game
forfeit composition keeps its existing value-binding source specialization.
None of these statements establishes sequential rationality after an
unreached runtime history.

The concrete two-Boolean runtime examples below fix the player network
observation rule to return no packet signal. Their claims concern physical
execution or pointwise payoff comparisons under arbitrary beliefs, not
preservation of information in a public mempool. The general Nash theorem
above permits pending-packet observations. A full native SE counterexample
still needs the partially public observations specified in its own model.

## Sequential equilibria exist in the bounded runtime

A fixed physical horizon, finite local response menus, finitely branching
initialization and nature, and remembered observations and responses suffice
for SE existence in this runtime. The application states, message and
observation carriers can remain infinite: only the legal histories must be
finite. No sure inclusion, privacy, forfeit margin or audit coverage is needed
for this existence statement. The proof instantiates the existing finite-game
SE theorem with the native runtime's checked decision recall and finite-history
laws; it does not replace native histories with a comparison game.

The general pin is
`Interaction.ReactiveApplication.ResponseMenu.exists_sequentialEquilibrium` in
[ReactiveEquilibriumExistence.lean](../../Interaction/ReactiveEquilibriumExistence.lean).
For the actual partially public three-instruction service described below,
`Vegas.Examples.LateOpeningRuntimeEquilibrium.exists_sequential_equilibrium`
in
[LateOpeningRuntimeEquilibrium.lean](../../Vegas/Examples/LateOpeningRuntimeEquilibrium.lean)
gives an SE for every finite nonnegative lottery weight and every choice of
real-valued reward, forfeit, deposits and audit sampler. These parameters need
no signs or margins for existence in a finite game.

This separates two questions: **the runtime has SEs**, while **whether any of
them realizes a specified source equilibrium law** requires a preservation or
exclusion theorem. The latter is the unresolved full native question.

## Failed publications in the concrete source game

The concrete three-instruction source first opens Alice's committed Boolean,
then lets Bob commit to an answer, then opens that answer. Alice also has a
private preference label, drawn uniformly from three labels independently of
her Boolean. Bob's safe answer pays `2/5`; correctly guessing the preference
label pays one. These are ordinary source instructions and private payoff
parameters, not new network primitives.

At Bob's answer commitment, the actual source information set contains
exactly three histories, one for each label. Every consistent assessment
assigns them probability `1/3`. This is proved from the actual initialization
and execution weights, including a complete enumeration of legal compatible
histories, in
[LateOpeningRuntimeSourceBeliefs.lean](../../Vegas/Examples/LateOpeningRuntimeSourceBeliefs.lean),
pin `Vegas.Examples.LateOpeningRuntimeSource.consistent_bobBinding_uniform`.
It supplies a posterior theorem rather than assuming the desired beliefs.

For any randomized answer law, Bob's expected payoff under that uniform
posterior is at most `2/5 - Pr(unsafe answer)/15`. Consequently an
epsilon-optimal answer uses Safe with probability at least `1 - 15*epsilon`;
an optimal answer law is exactly the Safe point mass. These checked bounds
are in
[LateOpeningRuntimeSourceOptimality.lean](../../Vegas/Examples/LateOpeningRuntimeSourceOptimality.lean).
The actual two-step continuation from Bob's commitment draws precisely his
answer distribution and then publishes it; no later intended action can
change the answer. Combining that law with sequential rationality proves
that **every intended source SE chooses Safe**. Every such SE therefore has
the same joint terminal-store/payoff law: the initialized Boolean and private
label keep their original distribution, both publications succeed, Bob's
answer is Safe, and the payoff vector is `(R/2, 2/5)`. The checked pin is
`Vegas.Examples.LateOpeningRuntimeSource.intended_equilibrium_terminal_law`
in
[LateOpeningRuntimeSourceEquilibrium.lean](../../Vegas/Examples/LateOpeningRuntimeSourceEquilibrium.lean).
Finite-game existence gives an actual SE with that law; equilibrium
existence is not assumed as an adapter premise.

This outcome classification also needs less than SE consistency: an
assessment satisfying Bayes' rule at positive-reach information sets and
sequential rationality has the same exact Safe law. The pin is
`Vegas.Examples.LateOpeningRuntimeSource.bayes_rational_terminal_law` in the
same module. At Bob's commitment each observed Boolean has positive
probability under every strategy, so off-path belief freedom cannot change
the answer. This is a source result under the stated Bayes-and-rationality
convention; it does not establish PBE preservation through the runtime.

For nonnegative Alice reward `R` and a publication forfeit `D` satisfying
`D >= R` and `D >= 1`, **every intended source SE extends to the source game
with optional failed publications**. The extension has no failed publication
on its equilibrium path and preserves the exact joint terminal-store/payoff
law. An actual such source SE exists. The checked results are
`Vegas.Examples.LateOpeningRuntimeSource.intended_equilibrium_preserved_under_withholding`
and `Vegas.Examples.LateOpeningRuntimeSource.exists_withholding_sequential_equilibrium`
in
[LateOpeningRuntimeSourcePreservation.lean](../../Vegas/Examples/LateOpeningRuntimeSourcePreservation.lean).
Composing these results also gives an actual withholding-source SE with the
specified Safe joint law, rather than an unspecified intended outcome:
`Vegas.Examples.LateOpeningRuntimeSource.exists_withholding_equilibrium_with_safe_law`
in
[LateOpeningRuntimeSourceEquilibrium.lean](../../Vegas/Examples/LateOpeningRuntimeSourceEquilibrium.lean).

This instantiates the existing general intended-to-source theorem. Its
binding interface admits values, while publications can fail. It does not
claim admission of immediate failed bindings, absence of failure in every
source equilibrium, or preservation through asynchronous message delivery.
In particular, source failure handling by itself does not explain the
runtime SE obstruction.

## A final runtime opening is optimal under every belief

In the separate initialized two-Boolean-commitment example, Bob has one final
activation and immediate inclusion of a correct opening. This uses the
existing public recovery scheduler and the complete typed source decoder;
it allows all legal raw traffic and the actual terminal audit.

Suppose Bob's gross terminal utility lies in `[L,U]`, his publication forfeit
is `D >= U-L`, his audit deposit is nonnegative, and the audit reports only
authentic evidence. At every legal final Bob decision history, the canonical
opening succeeds without an audit charge. Its payoff weakly dominates every
raw response and arbitrary later player policies. When the alternative
publication fails, its loss is at least `D-(U-L)`.

This also holds after averaging under **any belief over actual decision
histories**, with arbitrary stochastic responses and continuations. The
checked quantitative statement is

> `(D-(U-L)) * Pr(final publication fails)` is at most the expected payoff
> gained by choosing the canonical opening.

The pin is
`Vegas.Examples.CommittedResolutionBobIncentive.canonical_bob_response_regret`
in
[CommittedResolutionBobIncentive.lean](../../Vegas/Examples/CommittedResolutionBobIncentive.lean).
It even allows the alternative to depend on the hidden history, which
includes all information-feasible responses. With a strictly positive gap,
an epsilon-optimal response consequently fails with probability at most
`epsilon/(D-(U-L))`.

No consistency or positive-reach assumption is needed. The result concerns
this scheduler's final publication decision; it is not a general
service-contract theorem or a constructed native SE assessment. It rules out
failure at this decision as the explanation for an SE obstruction while
leaving earlier timing and information choices to be analyzed.

## The service contract gives no uniform late-failure floor

Consider an actual initialized source with two immutable Boolean commitments
and a later opening of each. Alice first remains silent, then sends her
canonical opening after its guaranteed inclusion window has closed but before
its acceptance deadline. The existing runtime accepts that opening if the
builder includes it.

[CommittedResolutionReliability.lean](../../Vegas/Examples/CommittedResolutionReliability.lean)
constructs a public builder for every chosen inclusion probability between
zero and one. Changing that lottery preserves the original contract over
**every legal raw history**. From a supported initialized state, Alice's
opening receives an accepting receipt in the next round with exactly that
probability. At the actual terminal horizon its acceptance probability is at
least as large, since accepting receipts persist through arbitrary later
responses and commands.

Consequently, for every proposed positive uniform failure floor, a checked
contract builder gives this late opening a smaller probability of final
nonacceptance. The pin is
`Vegas.Examples.CommittedResolutionReliability.exists_contract_below_failure_floor`.
This concerns late inclusion, not whole-game reliability or SE preservation.
For stochastic `q < 1`, this family has no checked late-packet
erasure-independence property.

The deterministic endpoint `q=1` supplies a stronger joint boundary. The
same actual scheduler satisfies the all-history service contract and the
all-input late-packet erasure condition. The supported initialized canonical
opening is sent outside the protected window and has acceptance probability
one, both after six rounds and at the full terminal horizon. Thus **even
those two conditions together imply no positive uniform late-failure
floor**. The pin is
`Vegas.Examples.CommittedResolutionErasure.certain_late_inclusion_with_joint_contract`
in
[CommittedResolutionErasure.lean](../../Vegas/Examples/CommittedResolutionErasure.lean).
This is an operational theorem; it is not an SE counterexample and does not
supply a nondegenerate stochastic builder.

The partially public three-instruction runtime described below gives the
nondegenerate joint family as well. For every finite nonnegative weight
`w`, it satisfies both predicates. Both initialized late sending times have
an accepting receipt after nine commands with exactly
`q = w/(1+w) < 1`; an accepting receipt survives **arbitrary later raw
policies and schedulers**. The actual terminal acceptance is therefore at
least `q`. For every positive proposed failure floor, some finite weight
gives smaller final nonacceptance, for every supported Boolean and private
label and both late timings. The pin is
`Vegas.Examples.LateOpeningRuntimeReliability.exists_joint_service_below_failure_floor`
in
[LateOpeningRuntimeReliability.lean](../../Vegas/Examples/LateOpeningRuntimeReliability.lean).
The same file checks that each actual sending decision is outside its
protected window. Its exact probability is the nine-command lottery law;
arbitrary later schedulers give a one-sided continuation bound. With this
actual builder unchanged, later raw policies preserve **exactly** the
Bernoulli receipt law, since it never includes another Alice identifier after
the lottery. Thus its full-horizon acceptance is exactly `q` and its final
nonacceptance is strictly positive `1-q` for every finite weight. This stronger
law is `Vegas.Examples.LateOpeningRuntimeTerminalReceipt.terminal_receipt_law`
in
[LateOpeningRuntimeTerminalReceipt.lean](../../Vegas/Examples/LateOpeningRuntimeTerminalReceipt.lean).
None of these claims assumes sequential rationality or supplies the native SE negative.

## Public lotteries can satisfy erasure independence

A different checked construction gives each distinct pending identifier
weight `w`, and gives waiting weight one. With `n` pending identifiers, each
identifier is selected with probability `w / (1 + n*w)` and nothing is selected
with probability `1 / (1 + n*w)`. Malformed packets compete too; the ordinary
runtime handler determines whether inclusion succeeds.

Deleting a packet and renaming the author's later identifiers gives exactly
the residual lottery, after restoring the surviving identifiers. Therefore
the scheduler law is a mixture of including the deleted packet and behaving
as it would have behaved without that packet. This holds at every input,
including inputs outside initialized play. The proof also establishes that
payload, application state, receipts and command recall cannot influence the
lottery beyond the pending identifiers.

For one packet every inclusion probability `q < 1` is realized by the finite
weight `w = q/(1-q)`. Two distinct identifiers then each receive `q/(1+q)`.
See [PendingOutsideSelection.lean](../../Interaction/PendingOutsideSelection.lean),
[PendingErasureSelection.lean](../../Interaction/PendingErasureSelection.lean),
and the actual runtime pin
`Vegas.EventGraphRuntime.blindToLatePackets_pendingLottery` in
[ReactiveLateLottery.lean](../../Vegas/Pending/ReactiveLateLottery.lean).

This lottery alone gives no protected activation, receipt or completion
guarantee. **The stochastic service-contract family above and this
erasure-independent lottery are separate constructions.** Their conjunction
in the two-late counterexample's single scheduler remains an unproved native
adapter. The deterministic endpoint supplies the distinct checked
conjunction described above.

The generic priority-selection adapter in
[ReactivePriorityErasure.lean](../../Interaction/ReactivePriorityErasure.lean)
and its runtime instantiation in
[ReactiveLatestErasure.lean](../../Vegas/Pending/ReactiveLatestErasure.lean)
prove that deterministic last-eligible selection is erasure-independent:
either it selects the removed identifier or restoration gives the same
retained choice. This holds for arbitrary public inputs, including duplicate
identifiers. Mixing that selector with waiting generally loses the property:
after deleting the latest of two eligible packets, the residual scheduler
would select the older packet with positive probability, while the original
mixture only selects the latest or waits.

## Concrete native execution of the three-instruction example

The same source with Alice's initialized Boolean and private label has
an explicit compiled runtime in
[LateOpeningRuntimeService.lean](../../Vegas/Examples/LateOpeningRuntimeService.lean).
Its relative deadline durations are three ticks for Alice's opening, three
for Bob's answer commitment, and four for Bob's answer opening. The public
schedule has 26 commands, including wait padding for its conditional callback.
Alice has a protected callback at clock zero and late callbacks at clocks
one and two. Bob can observe pending traffic between them. Each protected
receipt stage selects the latest unpublished packet of its authenticated
author, including invalid calls. The clock-two lottery competes over all
pending identifiers. Bindings and their dependency barriers are unchanged.

The native alphabet covers both Booleans, all three private labels and all
six answers; the raw menu includes all its malformed calls, handles and
evidence requests. The compiler's binding-value, initial-candidate and capacity
side conditions are checked in
[LateOpeningRuntimeCoverage.lean](../../Vegas/Examples/LateOpeningRuntimeCoverage.lean).
Initial states, observations and scheduler choices branch
finitely, and the full bounded raw-history type is finite.

Unlike the earlier two-Boolean operational fixture, this runtime samples
foreign pending identifiers. Each subset of its foreign pool has probability
`2^(-pool size)`. A singleton is observed with probability one half and
missed with probability one half. The sampling law reads identifiers and
authors, not packet contents; passive learning retains received certificates.
These exact probability laws are checked in
[LateOpeningRuntimeObservation.lean](../../Vegas/Examples/LateOpeningRuntimeObservation.lean).

The same scheduler satisfies the all-input erasure condition for every
finite nonnegative lottery weight:
`Vegas.Examples.LateOpeningRuntimeServiceErasure.scheduler_blind`.
Its public clock is fixed at every unrestricted raw history, and **every
legal raw terminal execution completes all three events by the declared
horizon**, including malformed calls and silence. These are
`Vegas.Examples.LateOpeningRuntimeService.clock_history` and
`Vegas.Examples.LateOpeningRuntimeService.completes` in
[LateOpeningRuntimeServiceClock.lean](../../Vegas/Examples/LateOpeningRuntimeServiceClock.lean)
and
[LateOpeningRuntimeServiceCompletion.lean](../../Vegas/Examples/LateOpeningRuntimeServiceCompletion.lean).
The required early owner activation is also checked at every raw history:
`Vegas.Examples.LateOpeningRuntimeService.opportunity` in
[LateOpeningRuntimeServiceOpportunity.lean](../../Vegas/Examples/LateOpeningRuntimeServiceOpportunity.lean).
Every raw Bob response and every clock-zero Alice response receives service
before the clock advances, even if its addressed call or payload is invalid.
The receipt theorem does not need the contract's sole-packet premise:
`Vegas.Examples.LateOpeningRuntimeService.protected_submission_receipt` in
[LateOpeningRuntimeServiceReceipt.lean](../../Vegas/Examples/LateOpeningRuntimeServiceReceipt.lean).
Together these prove the full service contract **and** all-view erasure
independence for the same builder, for every finite nonnegative lottery weight:
`Vegas.Examples.LateOpeningRuntimeService.contract_and_blind` in
[LateOpeningRuntimeServiceContract.lean](../../Vegas/Examples/LateOpeningRuntimeServiceContract.lean).
The compiled configuration is an actual instance of `Vegas.AsyncServiceSpec`,
with all its alphabet, capacity and finite-nature requirements discharged.
For this exact configuration,
`Vegas.Examples.LateOpeningRuntimeNash.first_opportunity_nash_iff` gives
same-error Nash preservation and reflection for every source admission
interface, every authentic sampler, nonnegative reward, forfeit and deposits,
and every finite lottery weight. Its realized payoff bounds are derived from
the example's actual utilities. The associated
`Vegas.Examples.LateOpeningRuntimeNash.first_opportunity_settlement_law`
preserves the exact joint terminal store and net payoff vector, for every
source profile. Both are in
[LateOpeningRuntimeNash.lean](../../Vegas/Examples/LateOpeningRuntimeNash.lean).

The late-send policies are actual members of the full bounded raw menu.
Their initialized prefixes and Bob's complete remembered response records
are evaluated in
[LateOpeningRuntimeLatePrefix.lean](../../Vegas/Examples/LateOpeningRuntimeLatePrefix.lean).
Sending at the first late turn gives exactly a half-seen, half-missed record
law. Waiting until the second gives the same missed record with probability
one. Neither record reveals Alice's private preference. Each branch has an
actual legal raw trace; these are not proposed abstract information sets.
After accepted inclusion, Bob's **entire recall and current view** still
agree between the first-send-missed and second-send cases, for any private
labels. They also agree across labels when the first-send packet was observed.
See
[LateOpeningRuntimeLateAcceptance.lean](../../Vegas/Examples/LateOpeningRuntimeLateAcceptance.lean).
For positive lottery weight, every possible branch reaches an actual active
Bob decision in the complete bounded raw game:
`Vegas.Examples.LateOpeningRuntimeLateHistories.answerDecision_trace` in
[LateOpeningRuntimeLateHistories.lean](../../Vegas/Examples/LateOpeningRuntimeLateHistories.lean).
At any raw history matching Bob's complete remembered silent response, no
Bob-authored packet exists in pending, settled, leaked or recorded input
traffic. Any ready Bob answer-binding decision at clock three occurs at the
same callback with fourteen commands left. These full-history restrictions
are checked in
[LateOpeningRuntimeFiberEvidence.lean](../../Vegas/Examples/LateOpeningRuntimeFiberEvidence.lean).
They do not exclude unseen later Alice packets or give a complete posterior.
Identifier zero does exclude every **earlier** emission, including malformed
packets: actual remembered output identifiers are precisely their allocated
serial order. The general checked lemma is
`Interaction.ReactiveApplication.emitted_zero_has_no_prior_outputs` in
[ReactiveEmissionOrder.lean](../../Interaction/ReactiveEmissionOrder.lean).

The complete decoder retains the original Boolean and private label alongside
the answer commitment and publications. Under arbitrary schedulers, deadlines,
observations and raw continuations, a successful Alice publication is her
original bit and a successful Bob publication is his already accepted answer.
See
[LateOpeningRuntimeReadout.lean](../../Vegas/Examples/LateOpeningRuntimeReadout.lean).
The actual service utilities apply the source's one failed-publication forfeit
per owner. Alice has no binding-omission charge. If all her traffic consists
of accepted certified openings, every authentic sampler charges her zero,
regardless of their emission times:
`Vegas.Examples.LateOpeningRuntimeUtility.alice_accepted_openings_audit_clean`
in
[LateOpeningRuntimeUtility.lean](../../Vegas/Examples/LateOpeningRuntimeUtility.lean).
This states actual traffic conditions; an additional forbidden Alice packet
is not silently treated as clean.
At most one accepting identifier per source event is possible in **any** raw
execution, for arbitrary initialization and scheduling. Accepting receipts
also certify the event's authenticated owner and permanent completion. These
are checked in
[ReactiveAcceptanceUniqueness.lean](../../Vegas/Pending/ReactiveAcceptanceUniqueness.lean),
with the pin `Vegas.EventGraphRuntime.accepting_identifiers_unique`.

A retry has a concrete audit consequence. Alice owns one publication event,
so two distinct Alice submissions cannot both be accepted. At settlement,
every unaccepted envelope is forbidden, including malformed envelopes that
name no event. The actual audit therefore collects with at least its declared
coverage rate; full traffic auditing collects with certainty. If Alice's gross
reward is at most `R`, her realized payoff after two distinct submissions is
at most `R - K_A`, where `K_A` is her audit deposit. This holds under every raw
continuation, rather than assuming that she retries a canonical packet. See
`Vegas.Examples.LateOpeningRuntimeRetryAudit.alice_two_envelopes_utility_bound`
in
[LateOpeningRuntimeRetryAudit.lean](../../Vegas/Examples/LateOpeningRuntimeRetryAudit.lean).
Silence can still leave the first packet unaccepted and incur both forfeit
and audit collection. The actual remaining eighteen-command continuation
after a genuine first late opening nevertheless gives a conservative bound:
remaining silent has expected payoff at least `-(1-q)(D+K_A)`, for arbitrary
Bob policies. On acceptance, Alice has nonnegative gross payoff and zero audit
charge; on failure, the bound includes both losses. Every second raw submission
has expected payoff at most `R-K_A`, even with arbitrary later policies. Thus
silence strictly beats every second submission when

`(1-q)(D+K_A) < K_A-R`.

The checked pin is
`Vegas.Examples.LateOpeningRuntimeAliceContinuation.quiet_strictly_beats_second_packet`
in
[LateOpeningRuntimeAliceContinuation.lean](../../Vegas/Examples/LateOpeningRuntimeAliceContinuation.lean).
This canonical-prefix comparison has also been extended to Alice's complete
actual information classes, as described below. Its deposit threshold is
more conservative than the reviewed paper counterexample's threshold.
The quantitative gap is at least
`K_A-R-(1-q)(D+K_A)`. Moreover, for every fixed nonnegative reward and forfeit,
every fixed `K_A>R`, and every positive requested failure floor, one finite
builder in the same actual service family simultaneously satisfies the full
raw-history service contract and packet-erasure requirement, has strictly
positive failure below that floor for both canonical quiet late timing
policies, and makes silence strictly superior for
every bit, preference label, possible early sample and second raw submission.
Both policy continuations remain arbitrary. This collateral-before-builder
existential is
`Vegas.Examples.LateOpeningRuntimeAliceContinuation.exists_service_with_quiet_normalization`.

Alice's remaining decision now has a checked native SE consequence. Suppose
one actual history has her genuine first opening pending, no earlier public
receipt, and a silent earlier Bob response. Her complete remembered actions
and authenticated observation determine that every compatible history has
exactly that opening pending, the same immutable initial binding, and the
same ready and timely publication. The earlier opening can use arbitrary
private raw submission syntax; the proof does not project raw equilibria to
a normalized game. Hidden later Bob behavior remains arbitrary.

The scheduler has no further Alice activation after this response, while
Bob continues to act. The existing assessment's whole-policy continuation
value is proved equal to the actual physical continuation value. Setting her
current response to silence is a legal bounded-menu deviation. Its gain is
at least `Gamma * Pr(second packet)`, where

`Gamma = K_A-R-(1-q)(D+K_A)`.

For nonnegative `R`, `D` and `K_A`, **every actual native SE has zero probability
of a second packet at these information sets when `Gamma>0`**. Sequential
rationality alone suffices; there is no posterior-support assumption or
consistency premise in this local implication. A genuine deviation gain at
most epsilon gives send probability at most `epsilon/Gamma`. The pins are
`Vegas.Examples.LateOpeningRuntimeAliceRationality.equilibrium_second_packet_zero`
and
`Vegas.Examples.LateOpeningRuntimeAliceRationality.second_packet_le_of_deviation_regret`
in [LateOpeningRuntimeAliceRationality.lean](../../Vegas/Examples/LateOpeningRuntimeAliceRationality.lean).
The class is inhabited for every bit, private preference label and possible
early sample, by the actual bounded trace in
[LateOpeningRuntimeAliceWitness.lean](../../Vegas/Examples/LateOpeningRuntimeAliceWitness.lean).

Finite native information classes also give a uniform vanishing retry bound
along every strategy sequence converging to silence at these sites. Summing
over arbitrary private aliases preserves a bound of the form
`retry mass <= epsilon * first-opening mass`, with epsilon tending to zero.
The first-opening mass may itself tend to zero at any rate. This is the
relative control needed for beliefs at unreached decisions; an absolute
error bound would not suffice. The checked quantitative adapter is
`Vegas.Examples.LateOpeningRuntimeAliceTremble.weighted_retry_ratio_tendsto`
in [LateOpeningRuntimeAliceTremble.lean](../../Vegas/Examples/LateOpeningRuntimeAliceTremble.lean).
Its direct SE instance,
`Vegas.Examples.LateOpeningRuntimeAliceTremble.equilibrium_consistency_retry_bound`,
extracts the actual fully mixed Bayes consistency sequence from the native SE
and supplies this uniform bound using its convergence at reachable Alice
information sites. No tremble rate is chosen by the proof. It does not yet
calculate the receiver's complete grouped history weights.

Two other actual operational boundaries are checked. If protected Alice
acceptance is missed, every subsequent unrestricted raw policy has a
positive-probability continuation reaching permanent Alice publication
failure. The lottery's outside option has positive probability for every
finite public weight, even with arbitrary extra pending packets. Consequently
certain terminal Alice success forces protected acceptance, including for
every profile in the actual bounded behavioral game. The pin is
`Vegas.Examples.LateOpeningRuntimeProtectedReceipt.native_almost_sure_success_protected_receipt_law`
in [LateOpeningRuntimeProtectedReceipt.lean](../../Vegas/Examples/LateOpeningRuntimeProtectedReceipt.lean).
This is a necessary condition on a preserving profile, not SE exclusion.

If Bob sends any raw packet while Alice's publication is unresolved, the
actual handler rejects it. Bob's own later source events are not ready; a
packet addressed to Alice's ready event fails the authenticated-owner check.
The early service records the false receipt permanently, and full terminal
auditing collects Bob's deposit. Every later raw policy therefore gives him
payoff at most `1-K_B`, for nonnegative forfeit and deposit. The pin is
`Vegas.Examples.LateOpeningRuntimeEarlyBobAudit.early_submission_continuation_utility_bound`
in [LateOpeningRuntimeEarlyBobAudit.lean](../../Vegas/Examples/LateOpeningRuntimeEarlyBobAudit.lean).
The payoff bound by itself does not establish early silence: a legal quiet
continuation must publish Bob's answer against arbitrary future Alice behavior.
The quiet prefix through Bob's binding opportunity is checked independently
of Alice's behavior: every actual continuation of this prefix reaches a ready
and timely binding opportunity at clock three with no previous Bob emission,
whether Alice's opening succeeded or expired. Canonical answer binding there
is a legal bounded response, accepts immediately, and fixes a ready disclosure
with clean earlier Bob traffic. The checked endpoints are
`Vegas.Examples.LateOpeningRuntimeBobQuietPrefix.binding_activation` and
`Vegas.Examples.LateOpeningRuntimeBobBindingService.binding_round` in
[LateOpeningRuntimeBobQuietPrefix.lean](../../Vegas/Examples/LateOpeningRuntimeBobQuietPrefix.lean)
and [LateOpeningRuntimeBobBindingService.lean](../../Vegas/Examples/LateOpeningRuntimeBobBindingService.lean).
These two operational facts end at the accepting binding; the complete
continuation requires its own publication and audit argument.

The complete physical Safe continuation is checked. From Bob's first
callback with empty own recall and Alice still unresolved, silence followed
by the observable policy which binds Safe at clock three and opens it at
the optional callback ensures successful Safe publication and zero audit
charge against arbitrary future Alice responses. This holds for any authentic
sampler and arbitrary real reward, forfeit and deposits. Bob's payoff is
nonnegative. The pins are
`Vegas.Examples.LateOpeningRuntimeBobSafeContinuation.safe_continuation_clean`
and
`Vegas.Examples.LateOpeningRuntimeBobSafeContinuation.safe_continuation_nonnegative`
in [LateOpeningRuntimeBobSafeContinuation.lean](../../Vegas/Examples/LateOpeningRuntimeBobSafeContinuation.lean).

These are actual whole-policy deviations in Bob's full information set.
With nonnegative forfeit and `K_B>1`, sequential rationality forces his
complete response law to be pure silence at every first callback where
Alice's publication remains unresolved. A quiet current response followed
by his incumbent future policy must be compared alongside the complete
Safe continuation: the latter is worth at least zero, while any premature
packet is worth at most `1-K_B`. If both attainable deviations have regret
at most `epsilon`, premature-packet probability is at most
`epsilon/(K_B-1)`. The pins are
`Vegas.Examples.LateOpeningRuntimeEarlyBobRationality.equilibrium_early_response_law`
and
`Vegas.Examples.LateOpeningRuntimeEarlyBobRationality.early_packet_le_of_deviation_regrets`
in [LateOpeningRuntimeEarlyBobRationality.lean](../../Vegas/Examples/LateOpeningRuntimeEarlyBobRationality.lean).
No posterior, late-inclusion bound or restriction on Alice's later policy
is assumed. This does not prohibit legitimate Bob commitments after Alice
has already settled.

At the actual clock-three first binding callback after Alice has failed,
one representative with silent earlier Bob responses transports readiness,
deadline validity and the failed publication through the entire actual Bob
information set. His remembered and currently sampled pending packets remain
in that information; no prior or posterior about the hidden Boolean or label
is imposed. All six answer choices have a legal canonical commitment followed
by a successful, uncharged opening under arbitrary later Alice behavior.
With Alice's publication failed, the native payoff of that continuation is
exactly one for the bit guess matching her initialized Boolean and zero for
every other answer. This statement reads the bit only to evaluate hidden
histories; it does not expose it to Bob's policy. The checked operational and
payoff endpoints are
`Vegas.Examples.LateOpeningRuntimeBobBindingInformation.decision_of_information`,
`Vegas.Examples.LateOpeningRuntimeBobSafeContinuation.answer_continuation_clean`
and
`Vegas.Examples.LateOpeningRuntimeBobAnswerPayoff.failed_answer_continuation_payoff`
in [LateOpeningRuntimeBobBindingInformation.lean](../../Vegas/Examples/LateOpeningRuntimeBobBindingInformation.lean),
[LateOpeningRuntimeBobSafeContinuation.lean](../../Vegas/Examples/LateOpeningRuntimeBobSafeContinuation.lean)
and [LateOpeningRuntimeBobAnswerPayoff.lean](../../Vegas/Examples/LateOpeningRuntimeBobAnswerPayoff.lean).
The class has actual bounded representatives retaining the specified
initialized Boolean and private label:
`Vegas.Examples.LateOpeningRuntimeBobBindingWitness.failed_binding_representative`
in [LateOpeningRuntimeBobBindingWitness.lean](../../Vegas/Examples/LateOpeningRuntimeBobBindingWitness.lean).

The corresponding native assessment-context values are also checked.
The two fixed bit-guess policies have complementary values summing to one,
so one is worth at least `1/2` under every belief over this actual information
class. Therefore sequential rationality, and in particular every actual SE,
gives Bob incumbent continuation value at least `1/2` after Alice fails.
These are legal whole-policy deviations with actual continuation laws, rather
than an assumed payoff menu or posterior. No collateral or payoff-sign
hypothesis is needed for this lower bound. The checked endpoints are
`Vegas.Examples.LateOpeningRuntimeBobBindingDecision.answer_context_value`,
`Vegas.Examples.LateOpeningRuntimeBobBindingDecision.exists_bit_guess_value_ge_half`
and
`Vegas.Examples.LateOpeningRuntimeBobBindingDecision.equilibrium_binding_value_ge_half`
in [LateOpeningRuntimeBobBindingDecision.lean](../../Vegas/Examples/LateOpeningRuntimeBobBindingDecision.lean).
The strengthened witness
`Vegas.Examples.LateOpeningRuntimeBobBindingWitness.failed_binding_information_representative`
supplies an actual bounded information-site representative, so this condition
is not vacuous. The witness preserves the exact initialization invariant;
it does not supply the complete sampled-history grouping or its likelihoods.
Classifying all optimal raw binding responses still requires a separate upper
bound.

At an active Alice callback after she has emitted no packet, the actual
pending pool is empty even if Bob previously sent arbitrary invalid packets
or prepared private candidates. Those Bob packets already have public
protected receipts and cannot remain pending. The same own-recall and view
argument transports Alice's initialized binding, readiness and timeliness
through her entire final information class. These are operational facts in
[LateOpeningRuntimeAliceEmptyDecision.lean](../../Vegas/Examples/LateOpeningRuntimeAliceEmptyDecision.lean),
including `Vegas.Examples.LateOpeningRuntimeAliceEmptyDecision.quiet_pending_empty`.
The corresponding actual equilibrium implication is also checked. At every
such final information set, sequential rationality forces a genuine opening
with probability one whenever

`Gamma_open = min(D,K_A)-R-(1-q)(D+K_A) > 0`.

Silence causes permanent reveal failure and has expected payoff at most
`R-D`. Every other nongenuine response has expected payoff at most `R-K_A`.
A canonical opening gives expected payoff at least `-(1-q)(D+K_A)` against
arbitrary later Bob behavior. The legal deviation retains every genuine
private submission alias and replaces only nongenuine responses with that
opening. Its actual whole-policy gain is at least
`Gamma_open * Pr(nongenuine response)`; a gain at most epsilon therefore
bounds that probability by `epsilon/Gamma_open`. This proves a local native
SE consequence without a posterior or consistency assumption. It does not
give certain inclusion: the genuine opening still fails with probability
`1-q`. The pins are
`Vegas.Examples.LateOpeningRuntimeAliceOpeningRationality.equilibrium_nongenuine_response_zero`
and
`Vegas.Examples.LateOpeningRuntimeAliceOpeningRationality.nongenuine_le_of_deviation_regret`
in [LateOpeningRuntimeAliceOpeningRationality.lean](../../Vegas/Examples/LateOpeningRuntimeAliceOpeningRationality.lean).

Both last-Alice response laws can be forced by the **same admissible builder
after collateral has been fixed**. For every `R>=0`, `D>R`, `K_A>R`, and any
requested positive failure bound, there is one finite positive lottery weight
whose scheduler satisfies the full raw-history service contract and all-view
packet-erasure independence, has strictly positive canonical late omission
below that bound, and makes both margins positive. Every sequentially rational
assessment for that builder therefore opens after silence and stays silent
after a genuine pending first opening, throughout the corresponding actual
information sets. The pins are
`Vegas.Examples.LateOpeningRuntimeAliceNormalization.equilibrium_last_responses`
and
`Vegas.Examples.LateOpeningRuntimeAliceNormalization.exists_service_with_last_responses_normalized`
in [LateOpeningRuntimeAliceNormalization.lean](../../Vegas/Examples/LateOpeningRuntimeAliceNormalization.lean).
The empty final-callback condition has actual bounded trace witnesses for
every initialized bit and private label:
`Vegas.Examples.LateOpeningRuntimeAliceEmptyWitness.secondLateDecision_trace`
in [LateOpeningRuntimeAliceEmptyWitness.lean](../../Vegas/Examples/LateOpeningRuntimeAliceEmptyWitness.lean).
This quantified result does not swap the collateral/builder order or assert
that a source outcome is preserved or excluded.

The distinction between accepted and permitted envelopes is checked without
normalizing away raw actions. At any terminal history, every actual permitted
Alice envelope contains her initialized Boolean opening, its matching
certificate, and the valid readiness token. Every other actual Alice envelope
is forbidden and, with full authentic traffic auditing and nonnegative
reward, forfeit and deposit, gives utility at most `R-K_A`. This includes an
opening whose raw handler accepted its identifier but whose certificate
failed the audit's content condition. A receipt identifier alone would not
authenticate a fabricated replacement envelope; the proof first identifies
the exact emitted envelope with the ledger entry. The pins are
`Vegas.Examples.LateOpeningRuntimeAliceOpeningAudit.permitted_alice_payload`
and
`Vegas.Examples.LateOpeningRuntimeAliceOpeningAudit.nongenuine_envelope_utility_bound`
in [LateOpeningRuntimeAliceOpeningAudit.lean](../../Vegas/Examples/LateOpeningRuntimeAliceOpeningAudit.lean).
The underlying identity theorem is application- and scheduler-general:
`Interaction.ReactiveApplication.traffic_envelope_eq_ledger_of_id_eq`
in [ReactiveTrafficIdentity.lean](../../Interaction/ReactiveTrafficIdentity.lean).
These statements classify actual traffic; they do not forbid genuine opening
packets sent at different legal times.

At Bob's final callback, a successfully committed answer has a stronger
incentive result when its publication is ready and still within its deadline,
and Bob's earlier traffic consists of accepted canonical commitments. Opening
that answer succeeds and has zero audit charge under every authentic sampler.
Every raw alternative weakly loses; if publication fails, it loses at least
the forfeit `D`. For every belief over these actual histories, every stochastic
raw response and every later policy, the expected gain from opening is at least
`D` times the alternative's failure probability. The comparison does not require
`D` to exceed the gross payoff range. Its chosen response uses only Bob's own
remembered actions and current observation. The pins are
`Vegas.Examples.LateOpeningRuntimeBobIncentive.canonical_dominates` and
`Vegas.Examples.LateOpeningRuntimeBobIncentive.canonical_regret` in
[LateOpeningRuntimeBobIncentive.lean](../../Vegas/Examples/LateOpeningRuntimeBobIncentive.lean).
Clean earlier traffic and a deadline that has not passed are substantive
conditions, not conclusions about every off-path final callback. This is a
native continuation comparison.

The bounded-menu and information-set adapters are also checked. One actual
clean final-history representative suffices: every history at the same Bob
information has the same committed answer, is ready and timely, and has clean
Bob traffic. These facts follow from his own remembered submissions and
current authenticated view, including the public receipts. His canonical
response belongs to the actual bounded menu.
The complete whole-policy continuation value used by the existing native
assessment is exactly the physical response-and-settlement value used above.
Consequently, **every native SE has zero final-publication failure probability
under its belief at such an information set, whenever `D>0`**. Sequential
rationality alone suffices; consistency is unnecessary for this local result.
If the same genuine deviation improves payoff by at most epsilon, failure
probability is at most `epsilon/D`.

The pins are
`Vegas.Examples.LateOpeningRuntimeBobRationality.equilibrium_final_failure_zero`
and
`Vegas.Examples.LateOpeningRuntimeBobRationality.final_failure_le_of_deviation_regret`
in
[LateOpeningRuntimeBobRationality.lean](../../Vegas/Examples/LateOpeningRuntimeBobRationality.lean).
This is an actual-runtime SE consequence at a specified final information set.
It does not establish sequential rationality at earlier decisions or global
source SE preservation.
For every positive finite lottery weight, the history class is inhabited:
every typed answer, private label, either
late sending time and possible early sample can reach a genuine bounded raw
final Bob decision. Its answer was accepted at clock three, the optional
opening callback was passed silently, and the final callback at clock six
remains within the publication deadline. The checked witness and nonemptiness
pins are `Vegas.Examples.LateOpeningRuntimeBobSuffix.finalDecision_trace` and
`Vegas.Examples.LateOpeningRuntimeBobSuffix.final_disclosure_class_nonempty` in
[LateOpeningRuntimeBobSuffix.lean](../../Vegas/Examples/LateOpeningRuntimeBobSuffix.lean).

**This is a checked native service, not yet a checked SE counterexample.**
The full information fibers, relative likelihood errors and remaining sender
incentive comparisons are needed before this construction proves the SE
negative. These checked execution and final-opening facts neither assume the
desired posterior nor identify the native game with a comparison game.
They also leave the relevant communication channel intact: even when every
packet is the genuine Boolean opening, choosing its sending time can convey
information about Alice's separate private preference label. The source
reveals the Boolean and keeps that label private. Accepted late genuine
openings remain audit clean; deterring malformed traffic alone does not remove
this timing choice.

The common-service capstone is
`Vegas.Examples.LateOpeningRuntimeEquilibriumConstraints.exists_service_with_constraints`
in [LateOpeningRuntimeEquilibriumConstraints.lean](../../Vegas/Examples/LateOpeningRuntimeEquilibriumConstraints.lean).
For every fixed `R>=0`, `D>R`, `K_A>R`, `K_B>1`, and any positive requested
failure bound, it supplies one finite positive-weight builder satisfying the
same actual raw-history contract and packet-erasure requirement. Both canonical
late-send policies have positive terminal omission below the requested bound,
for every supported initialized bit and label. The native game has an SE, and
**every SE of that same game** satisfies all these conditions:

- Alice emits a genuine final opening after earlier silence.
- Alice stays silent after a genuine first opening remains pending.
- Bob stays silent at his first callback while Alice is unresolved.
- After Alice fails, Bob's first binding continuation is worth at least `1/2`
  when his earlier responses were silent.
- After a clean accepted answer commitment, Bob has zero final-publication
  failure probability at a ready, timely final information set.

Each conclusion quantifies complete actual information classes using one
representative with the specified operational conditions. The omission bound
concerns the two specified late-send policies through the whole horizon; it
is not a uniform bound on all raw continuations or an equilibrium outcome
claim. This theorem keeps collateral before the builder and establishes
nonvacuity, while leaving first-late timing, receiver response optimization
and consistent posterior calculations open.
The stronger core
`Vegas.Examples.LateOpeningRuntimeEquilibriumConstraints.sequentially_rational_constraints`
needs only the existing native sequential-rationality condition. Bayes
consistency and an SE consistency sequence are unnecessary for these five
constraints. This is useful for assessing weaker equilibrium conventions too;
it is not a PBE-preservation theorem.

## Consistency constrains unreached beliefs

At a decision the probability of a private type is the sum of the reach
weights of its compatible histories divided by the total observation
probability. When two observation families share the same type-dependent
prefix likelihood, Bayes' rule cancels that common likelihood in a cross
identity. Opposite limiting timing choices can then force one entire
observation family to exclude a private type. Those exclusions change which
answer is optimal, even when the observations are unreached in equilibrium.

[ConsistentLikelihood.lean](../../GameTheoryExtensions/Analysis/Protocol/ConsistentLikelihood.lean)
checks this argument for finite groups of actual histories.
[AsymptoticLikelihood.lean](../../GameTheoryExtensions/Analysis/Protocol/AsymptoticLikelihood.lean)
allows additional-history errors which vanish **relative to the shared type
prefix and observation factors**. Absolute errors tending to zero are
insufficient: the observation's probability may tend to zero faster.

The general pin is
`GameTheory.Protocol.InformationModel.AsymptoticHistoryLikelihood.belief_face`.
Its premises concern actual execution likelihoods; they do not assume the
desired posterior beliefs. The checked comparison-game instantiation is
`Vegas.settleLate_opposite_timing_excludes_label` in
[SettleLateLikelihood.lean](../../Vegas/Examples/LateLeak/SettleLateLikelihood.lean).
That comparison is not identified with the compiled runtime. The native
counterexample still needs its own complete history fibers and likelihood
calculations, including hidden extra packets.

The [native SE counterexample](native-late-action-analysis.md),
[protected-execution positive](native-protected-execution.md), and
[same-fixture weak PBE](native-weak-pbe.md) remain reviewed paper results.
The owner-controlled SE target and checklist are unchanged.
