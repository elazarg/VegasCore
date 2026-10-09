# Checked preservation results and runtime boundaries

Analysis by Codex.

The strongest checked general result for the asynchronous message runtime is
**exact Nash correspondence for every binding-admission interface**. A checked
full-menu native counterexample refutes general exact SE outcome preservation
under the existing asynchronous contract. Its collateral, source and
observation scopes are specified in [the native capstone](native-se-obstruction.md).
The results below distinguish general compiler theorems, native operational
facts and the assembled SE obstruction.

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
above permits pending-packet observations. The checked native SE counterexample
uses the partially public observations specified in its own model.

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
exclusion theorem. The checked native obstruction below answers the latter
negatively for one selected source law and admissible service family.

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

This instantiates the existing general intended-to-source theorem with
value-only binding admission. A separate checked concrete restriction extends
**every value-only withholding source SE to immediate failed bindings** when
`D>=0`, preserving the joint terminal-store and payoff law. Bob's only extra
binding action forces his subsequent publication to fail and pays exactly
`-D`. Every ordinary source continuation pays him at least `-D`, so the
existing comparator extension applies without a new source semantic rule.

The complete-interface pins are
`Vegas.Examples.LateOpeningRuntimeSource.withholding_equilibrium_preserved_under_forfeiture`,
`.intended_equilibrium_preserved_under_forfeiture` and
`.exists_forfeiting_equilibrium_with_safe_law` in
[SourceForfeiture](../../Vegas/Examples/LateOpeningRuntimeSourceForfeiture.lean).
The intended composition and Safe-law existence use `R>=0,D>=R,D>=1`.
They do not classify every full-source SE, establish a generic full-language
failed-binding extension, or imply preservation through asynchronous delivery.
The native obstruction is therefore not explained merely by comparing a
failure-free source with a failure-aware runtime.

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
guarantee. The stochastic service-contract family above and this generic
lottery are separate constructions. The concrete three-instruction scheduler
below proves the service and erasure conjunction on every legal bounded raw
history; it is used by the checked SE obstruction. The deterministic endpoint
supplies another checked conjunction.

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

**This service is the target of the checked full-menu native SE counterexample.**
Its information fibers, relative likelihood limits and exact sender timing
values are assembled in [the native capstone](native-se-obstruction.md).
The checked execution and final-opening facts do not assume a desired
posterior or identify the native game with a comparison game.
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
- Every supported raw response at that binding opportunity fixes a bit guess
  maximizing its value under the actual assessment belief. The incumbent's
  continuation value equals the better of his two clean fixed guesses.
- If Bob's remembered view contains an authentic certificate for Alice's bit,
  his continuation value is one. Every supported continuation publishes the
  correct bit guess and has zero receiver audit charge.
- At Alice's first late callback after earlier silence, she either remains
  silent or emits her genuine opening envelope. Nongenuine packets have zero
  response probability; all genuine private submission aliases remain.
- After a clean accepted answer commitment, Bob has zero final-publication
  failure probability at a ready, timely final information set.

Each conclusion quantifies complete actual information classes using one
representative with the specified operational conditions. The omission bound
concerns the two specified late-send policies through the whole horizon; it
is not a uniform bound on all raw continuations or an equilibrium outcome
claim. This theorem keeps collateral before the builder and establishes
nonvacuity, while leaving the choice between the two legitimate late sending
times and consistent posterior calculations open.
The stronger core
`Vegas.Examples.LateOpeningRuntimeEquilibriumConstraints.sequentially_rational_constraints`
needs only the existing native sequential-rationality condition. Bayes
consistency and an SE consistency sequence are unnecessary for these five
constraints. This is useful for assessing weaker equilibrium conventions too;
it is not a PBE-preservation theorem.

## Complete raw responses at the concrete late decisions

The source first publishes Alice's initialized Boolean, then asks Bob to
commit one of six answers and publish it. Alice also has an independent
private preference label that the source never publishes. Bob's answers are
a Safe answer, three guesses of that label, and two guesses of the Boolean.
If Alice's publication fails, only a correct Boolean guess earns Bob one;
the other answers earn zero. Forfeit and audit deductions are nonnegative.

At Bob's actual first binding callback after that failure and earlier Bob
silence, **every raw response and every later policy has realized payoff at
most the correctness score of the answer fixed by the immediate service**.
This includes malformed calls, unusable handles, silence, hidden preparation,
certificate aliases and arbitrary later packets. A binding omitted at that
service cannot be repaired: the optional callback stays disabled, expiry
stores binding failure, and the later callback occurs after that settlement.
The same raw current response fixes the same typed result throughout Bob's
actual information class, because his recall and view determine its immediate
physical service. These are checked in
[BobRawBinding](../../Vegas/Examples/LateOpeningRuntimeBobRawBinding.lean),
[BobBindingOmission](../../Vegas/Examples/LateOpeningRuntimeBobBindingOmission.lean)
and [BobRawPayoff](../../Vegas/Examples/LateOpeningRuntimeBobRawPayoff.lean).
The payoff bound permits arbitrary audit sampling and only requires
`D>=0` and `K_B>=0`.

Clean complete bit-guess policies attain their corresponding expected
correctness scores. Hence sequential rationality forces continuation value
equal to the maximum of those two policy values, and **each supported current
raw response successfully binds a maximizing bit guess**. A tie permits both
guesses. Private submission syntax is retained; the conclusion classifies
the logical answer rather than presuming a canonical runtime menu. It applies
under any belief on the complete native information class. The pins are
`Vegas.Examples.LateOpeningRuntimeBobBindingOptimization.rational_value_eq_bestGuessValue`
and
`Vegas.Examples.LateOpeningRuntimeBobBindingOptimization.rational_supported_binding`
in [BobBindingOptimization](../../Vegas/Examples/LateOpeningRuntimeBobBindingOptimization.lean).

For `D>0` and `K_B>0`, every such supported current response also publishes
that same maximizing guess successfully with zero audit charge, at every
positive-belief hidden history and every supported physical continuation.
This includes histories where the chosen guess is wrong: positive forfeit
makes withholding strictly worse there too. The proof saturates the
nonnegative difference between logical score and realized payoff, first over
the assessed belief and then over runtime outcomes. The pin is
`Vegas.Examples.LateOpeningRuntimeBobBindingSettlement.rational_supported_clean_settlement`
in [BobBindingSettlement](../../Vegas/Examples/LateOpeningRuntimeBobBindingSettlement.lean).

The successful late-publication case is checked for the same unrestricted
raw menu. At a ready, timely fresh binding with silent Bob recall, Safe has
value `2/5`, each label guess has value equal to its actual posterior label
probability, and both Boolean guesses have value zero. Sequential rationality
therefore forces value
`max(2/5, Pr(label=0), Pr(label=1), Pr(label=2))`; every supported current
response binds Safe or a maximizing label guess. The pins are
`Vegas.Examples.LateOpeningRuntimeBobSuccessOptimization.bestAnswerValue_formula`
and `Vegas.Examples.LateOpeningRuntimeBobSuccessOptimization.rational_supported_binding`
in [BobSuccessOptimization](../../Vegas/Examples/LateOpeningRuntimeBobSuccessOptimization.lean).
Ready and timely are essential: success during Alice's protected clock-zero
opportunity can leave this later Bob binding callback overdue.

For `D>0` and `K_B>0`, that answer also publishes with zero Bob audit charge
at every positive-belief hidden history and supported physical continuation.
This is `Vegas.Examples.LateOpeningRuntimeBobSuccessSettlement.rational_supported_clean_settlement`
in [BobSuccessSettlement](../../Vegas/Examples/LateOpeningRuntimeBobSuccessSettlement.lean).
For Alice's first two preference labels, the corresponding payoff is at least
`R/2` minus her own audit deduction; see
`Vegas.Examples.LateOpeningRuntimeAliceSuccessFloor.rational_supported_payoff_floor`
in [AliceSuccessFloor](../../Vegas/Examples/LateOpeningRuntimeAliceSuccessFloor.lean).
These support statements do not cover merely possible histories assigned zero
Bob belief. Extending them to histories reached by Alice's deviations requires
a separate physical continuation argument.

An authentic opening certificate in Bob's remembered view proves the value
of Alice's original binding across that entire class. It does not require
an accepting publication receipt: the packet can have leaked and then been
omitted. The correct fixed guess consequently has value one. Under `D>=0`
and `K_B>0`, sequential rationality forces correct final publication and zero
full-audit charge on every supported physical continuation averaged over his
assessed belief. Merely possible histories assigned zero belief are not
included in that support assertion. These are
`Vegas.Examples.LateOpeningRuntimeBobKnownBit.equilibrium_correct_publication`
in [BobKnownBit](../../Vegas/Examples/LateOpeningRuntimeBobKnownBit.lean), and
the actual bounded information-class witness
`Vegas.Examples.LateOpeningRuntimeBobKnownBitWitness.failed_publication_known_bit_class`
in [BobKnownBitWitness](../../Vegas/Examples/LateOpeningRuntimeBobKnownBitWitness.lean).
The witness retains the exact initialized Boolean and private label.

At Alice's first late callback after no earlier transmission, a nongenuine
packet is bounded above by `R-K_A`. Repairing only that response to silence
leaves her entire future policy unchanged. Every supported intervening Bob
response and service leads to a legal bounded final Alice callback with her
immutable opening ready and timely. Global sequential rationality supplies
the genuine final opening there, even after this counterfactual deviation.
The resulting continuation is bounded below by `-(1-q)(D+K_A)`.
Therefore the positive final-opening margin
`min(D,K_A)-R-(1-q)(D+K_A)>0` also forces zero nongenuine first-late packet
probability. Both silence and genuine first-late opening remain legitimate.
This is
`Vegas.Examples.LateOpeningRuntimeAliceFirstRationality.equilibrium_nongenuine_packet_zero`
in [AliceFirstRationality](../../Vegas/Examples/LateOpeningRuntimeAliceFirstRationality.lean).
The [physical prefix adapter](../../Vegas/Examples/LateOpeningRuntimeAliceQuietPrefix.lean)
and [initialized witness](../../Vegas/Examples/LateOpeningRuntimeAliceFirstWitness.lean)
keep real bounded traces and unrestricted intervening Bob policies.

Private aliases of a genuine final opening have exactly the same terminal
payoff distribution for every player and any audit sampler. The proof erases
only the inactive sender's private recall as a total comparison projection;
application state, packets, knowledge, receipts and every other player's
recall remain exact. This projection does not change the runtime's memory or
its information sets. See
[AliceOpeningAliases](../../Vegas/Examples/LateOpeningRuntimeAliceOpeningAliases.lean)
and [InactiveRecall](../../Interaction/ReactiveInactiveRecall.lean).

Finally, any raw native profile whose decoded **Alice publication marginal**
is almost surely successful must obtain her protected accepting receipt
almost surely. Neither target equilibrium, hidden-binding equality, audit
authenticity nor collateral assumptions are required. In particular, matching
any intended source equilibrium's joint terminal and payoff law forces that
protected receipt. The pins are
`Vegas.Examples.LateOpeningRuntimePreservingLaw.successful_readout_protected_receipt`
and
`Vegas.Examples.LateOpeningRuntimePreservingLaw.intended_law_protected_receipt`
in [PreservingLaw](../../Vegas/Examples/LateOpeningRuntimePreservingLaw.lean).
This supplies a necessary condition on every candidate preserving equilibrium;
the native consistent-likelihood argument is still needed to exclude them.

Matching the selected source's **joint terminal and realized-payoff law** has
an additional consequence independent of equilibrium or audit sampling.
Every supported native terminal history has the successful Safe readout, and
its settlement law is the deterministic source payoff vector: `R/2` to Alice
and `2/5` to Bob. Every player with a nonzero deposit consequently has zero
audit-charge probability at each such history. The pins are
`Vegas.Examples.LateOpeningRuntimePreservingSettlement.history_settlement_pure`
and `Vegas.Examples.LateOpeningRuntimePreservingSettlement.history_charge_zero`
in [PreservingSettlement](../../Vegas/Examples/LateOpeningRuntimePreservingSettlement.lean).
No collateral sign or preservation theorem is assumed beyond the stated
joint-law equality.

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

The actual native consistency sequence now has uniform vanishing conditional
nongenuine-first-packet bounds across all legal first-late sender information
classes. Weighted sums retain a relative bound even when the protected-silence
prefix weights vanish arbitrarily quickly. This is
`Vegas.Examples.LateOpeningRuntimeAliceFirstTremble.equilibrium_consistency_nongenuine_bound`
and its ratio lemma in
[AliceFirstTremble](../../Vegas/Examples/LateOpeningRuntimeAliceFirstTremble.lean).
Together with the checked pending-opening retry bound, this controls two
sources of hidden raw traffic without prescribing a posterior.

The corresponding final-after-silence bound also counts omission as a
nongenuine response. All three finite-site bounds can be taken along **one
actual SE consistency sequence**, with a single uniform error tending to zero.
The same sequence gives every initialized-input conditional-probability limit
at every fresh Bob binding class. This is
`Vegas.Examples.LateOpeningRuntimeConsistency.equilibrium_consistency_witness`
in [Consistency](../../Vegas/Examples/LateOpeningRuntimeConsistency.lean),
using [AliceOpeningTremble](../../Vegas/Examples/LateOpeningRuntimeAliceOpeningTremble.lean).
The approximating assessments need not themselves be sequentially rational.

An exact physical observation factor is also checked. For any actual first
late sender decision and **any raw response probability law**, the probability
that Bob learns the exact genuine opening packet at his next actual callback
is one half the probability that Alice emitted that genuine envelope.
Malformed responses and private aliases remain in the law; Bob's subsequent
policy is arbitrary. A nongenuine first envelope cannot manufacture this
exact observed packet. The pin is
`Vegas.Examples.LateOpeningRuntimeFirstObservation.first_observation_probability`
in [FirstObservation](../../Vegas/Examples/LateOpeningRuntimeFirstObservation.lean).
This proves the first fair-sampling factor, not the complete receiver
information-fiber reach sums or their consistent limiting beliefs.

The complete native history groups now have a checked probability adapter.
At Bob's fresh binding callback at clock three, the public clock and unused
binding distinguish it from all other callbacks. Every compatible history
has exactly seventeen protocol transitions: initialization, twelve service
commands, and four completed player responses. The actual behavioral law at
this depth is eleven complete runtime rounds followed by Bob's next activation
and pending sample. The scheduler's later conditional callbacks remain intact.
`Vegas.Examples.LateOpeningRuntimeBindingPrefix.binding_common_depth` and
`Vegas.Examples.LateOpeningRuntimeBindingPrefix.binding_prefix_law` check this
identification in [BindingPrefix](../../Vegas/Examples/LateOpeningRuntimeBindingPrefix.lean).

Grouping **all** compatible histories by immutable initialized inputs gives
exactly the physical joint probability of those inputs and Bob's information.
The group includes every private submission representation and pending trace;
the input readout is a mathematical grouping, unavailable to Bob's policy.
`Vegas.Examples.LateOpeningRuntimeBindingPrefix.initialized_type_reach_eq_prefix`
pins the equality. Bayes' rule then divides the joint physical probability by
the actual information probability. One SE consistency witness makes these
ratios converge to the assessed beliefs for every readout, even if that
information probability tends to zero. See
`Vegas.Examples.LateOpeningRuntimeBindingPosterior.consistent_conditional_probabilities`
in [BindingPosterior](../../Vegas/Examples/LateOpeningRuntimeBindingPosterior.lean).

For Alice's failed publication, Bob's checked all-raw optimum is consequently
the maximum of the actual posterior probabilities of false and true. His
value is also the limit of these two optimal conditional prefix probabilities
along the same consistency sequence; it is not fixed at the original bit
prior. These statements are
`Vegas.Examples.LateOpeningRuntimeBobPosteriorOptimization.rational_value_eq_posterior_max`
and `Vegas.Examples.LateOpeningRuntimeBobPosteriorOptimization.consistent_value_limit`
in [BobPosteriorOptimization](../../Vegas/Examples/LateOpeningRuntimeBobPosteriorOptimization.lean).

An additional checked physical kernel retains the original probability that
Bob responds silently at his early observation. A transmitted first packet
splits into the two actual fair observation branches; any event requiring
silent Bob recall excludes every nonsilent raw early response by permanent
recall. The remaining lottery, clock advance, expiry and second observation
are computed from the complete actual pending pool, including duplicates and
malformed packets. See
`Vegas.Examples.LateOpeningRuntimeLatePrefixKernel.transmitted_binding_silent_event_probability`
and `Vegas.Examples.LateOpeningRuntimeLatePrefixKernel.settlement_activation`
in [LatePrefixKernel](../../Vegas/Examples/LateOpeningRuntimeLatePrefixKernel.lean).
The actual remaining Alice response is also retained, rather than replaced
by a canonical policy: `after_early_quiet_law` in
[LateResponseKernel](../../Vegas/Examples/LateOpeningRuntimeLateResponseKernel.lean)
composes its original raw response law with the full settlement kernel.
For any genuine first-opening representation and a silent retry, the typed
publication law is exactly `q` success and `1-q` failure. The pin is
`Vegas.Examples.LateOpeningRuntimeLateResponseKernel.genuine_retry_publication_law`.
These adapters still do not establish the final timing factors or posterior
exclusions: complete observation-event calculations and their relative errors
must be composed with the native probability bridge.

The full recalled receipt history also establishes an exact inverse fact:
an actual later Bob observation with an empty receipt list proves that Alice
sent no raw packet at the protected opportunity. This applies to every
compatible native history, including packets which would have been rejected;
it uses permanent receipts, rather than a belief restriction. See
`Vegas.Examples.LateOpeningRuntimeProtectedRecall.information_histories_protected_silent`
in [ProtectedRecall](../../Vegas/Examples/LateOpeningRuntimeProtectedRecall.lean).
Consequently the actual physical prefix gives zero mass to such an observation
together with any protected raw submission, under every behavioral profile.
This is
`Vegas.Examples.LateOpeningRuntimeProtectedPrefix.protected_submission_event_zero`
in [ProtectedPrefix](../../Vegas/Examples/LateOpeningRuntimeProtectedPrefix.lean).

The general pin is
`GameTheory.Protocol.InformationModel.AsymptoticHistoryLikelihood.belief_face`.
Its premises concern actual execution likelihoods; they do not assume the
desired posterior beliefs. The checked comparison-game instantiation is
`Vegas.settleLate_opposite_timing_excludes_label` in
[SettleLateLikelihood.lean](../../Vegas/Examples/LateLeak/SettleLateLikelihood.lean).
That comparison is not identified with the compiled runtime. The native
counterexample still needs the observation-specific likelihood calculations
for its complete native history groups, including relative contributions of
hidden extra packets.

The [native SE counterexample](native-late-action-analysis.md),
[protected-execution positive](native-protected-execution.md), and
[same-fixture weak PBE](native-weak-pbe.md) remain reviewed paper results.
The owner-controlled SE target and checklist are unchanged.

## Full-information publication and exact pending observations

These results concern the same three-instruction source and actual bounded
runtime: Alice reveals an initialized Boolean, Bob commits one of six answers,
and Bob reveals that immutable answer. Alice's additional private label is
never published by the source. Her two legal late submission opportunities
precede Bob's commitment. The builder samples pending identifiers fairly at
two receiver callbacks and includes the pending pool through a public lottery
with probability `q = weight/(1+weight)` for its singleton canonical packet.
It admits all bounded raw responses, rather than restricting players to the
canonical submission syntax.

After Alice succeeds, every supported rational Bob commitment is clean
throughout its **whole actual information set**, including histories with
zero assigned belief. A single positive-belief clean settlement certifies
the supported response's public commitment packet. Bob's remembered actions
and current observation then fix that same packet and accepting receipt at
every compatible legal history. Private response aliases remain possible.
The pin is
`Vegas.Examples.LateOpeningRuntimeBobSuccessBindingClean.rational_supported_clean_binding`
in [BobSuccessBindingClean](../../Vegas/Examples/LateOpeningRuntimeBobSuccessBindingClean.lean).
The actual accepting handler also proves the publication became ready at
clock three, with its timer set to three, and that the canonical opening is
available for the immutable selected answer. These are derived operational
facts in [BobBindingChronology](../../Vegas/Examples/LateOpeningRuntimeBobBindingChronology.lean).

At a clean, ready and timely **final** receiver callback, each supported
response publishes the bound answer at every compatible history and every
physical suffix in support. This includes zero-belief histories and arbitrary
future player policies. The proof compares the full receiver-view law across
the information set, then transports the zero failure probability established
by sequential rationality. It does not infer audit equivalence from that view.
The pin is
`Vegas.Examples.LateOpeningRuntimeBobFinalFiberRationality.equilibrium_supported_publication`
in [BobFinalFiberRationality](../../Vegas/Examples/LateOpeningRuntimeBobFinalFiberRationality.lean).
Its conditions are `D>0`, nonnegative receiver collateral and authentic audit
sampling.

With the actual full-record audit and `K_B>0`, the same scope also has zero
receiver charge. This uses an additional audit argument: public terminal
state, exact receipts and receiver-authored emitted envelopes determine his
full charge. Those quantities have the same law across the final information
set for a fixed response. The pin is
`Vegas.Examples.LateOpeningRuntimeBobFinalAuditRationality.equilibrium_supported_clean_publication`
in [BobFinalAuditRationality](../../Vegas/Examples/LateOpeningRuntimeBobFinalAuditRationality.lean).
The audit transfer is proved in
[BobFinalAuditObservation](../../Vegas/Examples/LateOpeningRuntimeBobFinalAuditObservation.lean).
It is not asserted for an arbitrary sampler depending on other players'
traffic.

The earlier optional publication callback has a complete clean comparator:
publish the current bound answer immediately, then use the existing answer
policy, which stays silent at the final callback. Its actual whole suffix
publishes that answer and has zero receiver charge on every physical branch.
The immediate response belongs to the unchanged bounded menu. This is
`Vegas.Examples.LateOpeningRuntimeOptionalOpening.canonical_continuation_clean`
in [OptionalOpening](../../Vegas/Examples/LateOpeningRuntimeOptionalOpening.lean).
The [optional information adapter](../../Vegas/Examples/LateOpeningRuntimeOptionalInformation.lean)
distinguishes this callback from the earlier binding callback at the same
clock using the exact number of remembered own responses. One actual clean
representative supplies readiness, timeliness and cleanliness throughout the
whole information set. The actual finite whole-policy comparison is checked
in [OptionalDecision](../../Vegas/Examples/LateOpeningRuntimeOptionalDecision.lean).

The comparator also attains the immutable answer's exact gross score at each
hidden history. Every raw current response and future raw policy satisfies
`raw payoff + actual audit charge*K_B + D*publication failure <= comparator payoff`.
This pointwise bound retains the actual initialized inputs and every physical
suffix; it has no sign restriction on the reward, forfeit or deposit. With
nonnegative forfeit and deposit it gives weak dominance. The pin is
`Vegas.Examples.LateOpeningRuntimeOptionalIncentive.canonical_audit_regret`
in [OptionalIncentive](../../Vegas/Examples/LateOpeningRuntimeOptionalIncentive.lean).
For `D>0` and `K_B>0`, payoff saturation implies successful publication and
zero charge on assessed continuation support, in
[OptionalRationality](../../Vegas/Examples/LateOpeningRuntimeOptionalRationality.lean).
More strongly, every supported current response is **silence or immediate
successful publication of the bound answer**, throughout the entire legal
information set. A clean assessed branch certifies the current packet, and
the actual information fixes its public effect even at zero-belief histories.
The pin is
`Vegas.Examples.LateOpeningRuntimeOptionalPacket.equilibrium_supported_response`
in [OptionalPacket](../../Vegas/Examples/LateOpeningRuntimeOptionalPacket.lean).
This statement does not normalize a later callback after publication has
already completed.

The callbacks compose on the original receiver policy. An accepted clean
answer commitment really enables the optional callback at clock three. If
the receiver is silent there, the actual five-command prefix enables a clean,
timely final callback at clock six, for every possible pending-message sample.
Consequently every physical fourteen-command suffix publishes the selected
answer, whether Alice previously succeeded or failed, without any positive
belief premise. The pin is
`Vegas.Examples.LateOpeningRuntimeBobDisclosurePublication.binding_publication`
in [BobDisclosurePublication](../../Vegas/Examples/LateOpeningRuntimeBobDisclosurePublication.lean),
using [BobDisclosureChronology](../../Vegas/Examples/LateOpeningRuntimeBobDisclosureChronology.lean).
For Alice's first two private labels, her successful branch therefore pays at
least `R/2` before her own audit deduction, at every compatible hidden history.
Receiver rationality does not by itself clear sender traffic. This is
`Vegas.Examples.LateOpeningRuntimeAliceFullFiberFloor.sequentially_rational_supported_payoff_floor`
in [AliceFullFiberFloor](../../Vegas/Examples/LateOpeningRuntimeAliceFullFiberFloor.lean).
After Alice's failure, the supported maximizing Boolean commitment is also
clean throughout the whole information set, in
[BobFailedBindingClean](../../Vegas/Examples/LateOpeningRuntimeBobFailedBindingClean.lean).

The actual initialized prefix now decomposes over the original hidden-input
prior and Alice's **original** protected response law. Any event requiring
Bob's remembered empty protected receipts has zero probability after a
protected raw packet. Its exact remaining probability therefore keeps the
original protected-silence atom multiplied by the original first-late raw
response law and the full later kernel. See
`Vegas.Examples.LateOpeningRuntimeInitializedPrefix.clean_information_probability`
in [InitializedPrefix](../../Vegas/Examples/LateOpeningRuntimeInitializedPrefix.lean).
The silence atom may tend to zero arbitrarily fast; no lower bound is assumed.

For any genuine first-opening alias and a silent retry, Bob's full remembered
information has exact branch probabilities. Inclusion contributes `q`.
Omission after Bob already learned the packet contributes `1-q`, since that
knowledge persists. After he missed the packet earlier, the second sample
splits omitted branches into newly learned and still empty information with
probability `(1-q)/2` each. Actual receipts distinguish success from failure;
the packet's public identity is retained. These laws are in
[BindingFactors](../../Vegas/Examples/LateOpeningRuntimeBindingFactors.lean),
using [BindingObservation](../../Vegas/Examples/LateOpeningRuntimeBindingObservation.lean).
Actual bounded history representatives also witness the failure information
classes in [BindingObservationWitness](../../Vegas/Examples/LateOpeningRuntimeBindingObservationWitness.lean).

Replacing only the final retry by silence changes its whole native execution
law by total variation at most the actual probability of an emitted retry.
Every admitted genuine private first-opening representation has an actual
bounded native retry information class, so the common consistency bound
applies without a canonical-syntax restriction. A mixture with total prefix
mass `m` consequently has event error at most `epsilon*m`. Dividing by positive
`m` gives an error tending to zero even when `m` itself vanishes arbitrarily
quickly. The pins are
`Vegas.Examples.LateOpeningRuntimeRetryWitness.genuine_alias_response_close_quiet`
and `Vegas.Examples.LateOpeningRuntimeRetryKernel.relative_event_error_tendsto` in
[RetryWitness](../../Vegas/Examples/LateOpeningRuntimeRetryWitness.lean) and
[RetryKernel](../../Vegas/Examples/LateOpeningRuntimeRetryKernel.lean).
The original early Bob policy is retained in the pending kernels; these
claims do not replace it by an independent or fixed silence probability.

The original mixture over **all** first responses and early receiver
responses has a sharper retry error: at most `epsilon*alpha`, where `alpha`
is the original genuine first-emission probability. Every other response
keeps its original continuation in the comparison. Under the positive native
retry-deterrence margin, sequential rationality makes the two laws exactly
equal. The pins are
`Vegas.Examples.LateOpeningRuntimeFirstRetryComparison.original_close_comparison`
and `Vegas.Examples.LateOpeningRuntimeFirstRetryRationality.rational_comparison_law` in
[FirstRetryComparison](../../Vegas/Examples/LateOpeningRuntimeFirstRetryComparison.lean)
and [FirstRetryRationality](../../Vegas/Examples/LateOpeningRuntimeFirstRetryRationality.lean).

For an information record remembering the canonical opening at the earlier
sample, both acceptance and omission have actual first-prefix likelihood
`alpha*p_seen*(q or 1-q)/2`, with error at most `epsilon*alpha`.
Here $p_{\mathrm{seen}}$ is the original receiver-silence atom at that observation.
A nongenuine first packet consumes Alice's identifier zero; no later raw
policy can recreate the canonical identifier-zero opening. Earlier silence
or an empty earlier sample also cannot create the remembered earlier packet.
These exact exclusions support
`Vegas.Examples.LateOpeningRuntimeSeenLikelihood.original_seen_error` in
[SeenLikelihood](../../Vegas/Examples/LateOpeningRuntimeSeenLikelihood.lean), using
[OpeningIdentity](../../Vegas/Examples/LateOpeningRuntimeOpeningIdentity.lean) and
[EarlyRecall](../../Vegas/Examples/LateOpeningRuntimeEarlyRecall.lean).
The relevant canonical early observations are actual bounded histories; their
original receiver law is pure silence when `D>=0` and `K_B>1`, by
[EarlyResponseLaw](../../Vegas/Examples/LateOpeningRuntimeEarlyResponseLaw.lean).

This likelihood is connected to the complete initialized native history
groups. Let `omega` be the actual prior atom times the original protected
silence atom for that private bit and label. The seen-opening group's reach
mass differs from `omega*alpha*p_seen*(q or 1-q)/2` by at most
`epsilon*omega*alpha`. Immutable original inputs exclude every other private
type exactly. Thus the error remains relative even when both protected
silence and genuine first emission vanish arbitrarily fast. The actual
receiver-silence atom converges to one along the **same** assessment sequence
whose target is globally sequentially rational. These are
`Vegas.Examples.LateOpeningRuntimeInitializedSeenLikelihood.initialized_history_seen_error`
and `.early_silence_tendsto` in
[InitializedSeenLikelihood](../../Vegas/Examples/LateOpeningRuntimeInitializedSeenLikelihood.lean).
Actual legal representatives witness both the accepted and omitted seen
information sets. The unseen-success group and paired posterior cross-identity
are checked in
[InitializedUnseenLikelihood](../../Vegas/Examples/LateOpeningRuntimeInitializedUnseenLikelihood.lean)
and [LabelCross](../../Vegas/Examples/LateOpeningRuntimeLabelCross.lean).

The complete eighteen-command suffix after Alice's last callback decomposes
into the actual inclusion lottery, receiver observation and original receiver
continuation. Genuine private first-opening aliases with silent retry, and
genuine final-opening aliases after earlier silence, preserve the exact whole
payoff distribution against arbitrary future policies. The pins are
`Vegas.Examples.LateOpeningRuntimeSettlementContinuation.genuine_first_payoff_law`
and `.genuine_final_payoff_law` in
[SettlementContinuation](../../Vegas/Examples/LateOpeningRuntimeSettlementContinuation.lean).
The private submission recall remains present in the actual execution.

The sender's complete continuation values after settlement are also exact.
For the original rational receiver policy and positive `D,K_B`, successful
singleton inclusion gives zero Alice audit charge, and omitted singleton
inclusion gives charge one under the full audit. On every physical branch Bob
publishes his selected answer. Alice's values are:

| Alice's publication | Bob's selected answer | Alice's net payoff |
| --- | --- | --- |
| Success | Safe | `R/2` |
| Success | Any of the three label guesses | `R` for Alice's labels zero and one; `0` for label two |
| Failure | Guess true | `R-D-K_A` for label zero; `-D-K_A` otherwise |
| Failure | Guess false | `R-D-K_A` for label one; `-D-K_A` otherwise |

These are the actual source utility and deductions, not assumed continuation
rewards. They retain all raw private commitment aliases. Their expectations
are taken over Bob's **original current response law**, using the actual
immediately serviced typed binding result. No desired posterior or
positive-belief-history restriction is supplied. The expected-value pins are
`Vegas.Examples.LateOpeningRuntimeAliceSuccessfulContinuation.receiver_expected_value`
and `Vegas.Examples.LateOpeningRuntimeAliceFailureContinuation.receiver_expected_value`
in [AliceSuccessfulContinuation](../../Vegas/Examples/LateOpeningRuntimeAliceSuccessfulContinuation.lean)
and [AliceFailureContinuation](../../Vegas/Examples/LateOpeningRuntimeAliceFailureContinuation.lean).
Expected-value integrability uses `R>=0,K_A>=0`; the pointwise payoff and audit
identities in
[AliceFailurePayoff](../../Vegas/Examples/LateOpeningRuntimeAliceFailurePayoff.lean)
need no such sign assumptions.

For successful Alice publication, Bob's native rational value is the maximum
of `2/5` and his three actual posterior label probabilities. The same quantity
computed from complete conditional physical prefix probabilities converges
to that value along the given common SE consistency witness. This is
`Vegas.Examples.LateOpeningRuntimeSuccessPosterior.conditional_value_tendsto`
in [SuccessPosterior](../../Vegas/Examples/LateOpeningRuntimeSuccessPosterior.lean).
It neither assumes that the posterior remains uniform nor supplies the
observation-specific exclusion needed by the negative proof.

## Checked full-menu native SE obstruction

For fixed `R>0`, `D>R`, `K_A>R`, `K_B>1` and any `epsilon>0`, one finite
admissible public chance builder has canonical terminal late-opening omission
strictly between zero and epsilon. Native SEs exist, but every one fails to
realize the source Safe joint terminal-store and realized-payoff law. The
builder satisfies the unchanged full raw-history service contract and
all-view late-packet erasure property; it is chosen before all equilibria.

The headline pin is
`Vegas.Examples.LateOpeningRuntimeUniformSeObstruction.exists_service_with_no_preserving_equilibrium`
in [UniformSeObstruction](../../Vegas/Examples/LateOpeningRuntimeUniformSeObstruction.lean).
The fixed-service exclusion and direct mandatory-source comparison are
`Vegas.Examples.LateOpeningRuntimeSeObstruction.equilibrium_terminal_law_ne_safe`
and `.equilibrium_terminal_law_ne_intended` in
[SeObstruction](../../Vegas/Examples/LateOpeningRuntimeSeObstruction.lean).

With the additional sufficient source bound `D>=1`, the explicit complete
source-interface composition is
`Vegas.Examples.LateOpeningRuntimeSourceSeObstruction.exists_source_equilibrium_with_uniform_service_obstruction`
in [SourceSeObstruction](../../Vegas/Examples/LateOpeningRuntimeSourceSeObstruction.lean).
It fixes one source SE admitting both failed bindings and failed publications
before every requested failure bound and builder. Each bound gets one
admissible service with native SEs, all of whose joint laws differ from that
same source assessment's law. Both existence statements are proved.

The proof is assembled from actual native histories and original future
policies. Its main checked dependencies are:

| Mathematical step | Owning module |
| --- | --- |
| Complete first and protected sender information fibers | [AliceFirstFiber](../../Vegas/Examples/LateOpeningRuntimeAliceFirstFiber.lean), [AliceProtectedFiber](../../Vegas/Examples/LateOpeningRuntimeAliceProtectedFiber.lean) |
| Original full continuation laws after any available first response | [FirstSettlementContinuation](../../Vegas/Examples/LateOpeningRuntimeFirstSettlementContinuation.lean), [FirstResponseRetryNormalization](../../Vegas/Examples/LateOpeningRuntimeFirstResponseRetryNormalization.lean) |
| Successful and failed typed receiver values, including all aliases | [AliceSuccessfulReduction](../../Vegas/Examples/LateOpeningRuntimeAliceSuccessfulReduction.lean), [AliceFailureReduction](../../Vegas/Examples/LateOpeningRuntimeAliceFailureReduction.lean) |
| Exact first-versus-second timing values and strictly opposite preferences | [AliceTimingValues](../../Vegas/Examples/LateOpeningRuntimeAliceTimingValues.lean), [AliceTimingSorting](../../Vegas/Examples/LateOpeningRuntimeAliceTimingSorting.lean) |
| Initialized unseen-success groups and label readout | [InitializedUnseenLikelihood](../../Vegas/Examples/LateOpeningRuntimeInitializedUnseenLikelihood.lean), [InitializedSuccessReadout](../../Vegas/Examples/LateOpeningRuntimeInitializedSuccessReadout.lean) |
| Common-witness posterior cross-identity, retaining vanishing type weights | [LabelCross](../../Vegas/Examples/LateOpeningRuntimeLabelCross.lean) |
| Positive Safe probability bounds every posterior label to `[1/5,2/5]` | [BobSafePosterior](../../Vegas/Examples/LateOpeningRuntimeBobSafePosterior.lean), [BobSafeProbability](../../Vegas/Examples/LateOpeningRuntimeBobSafeProbability.lean) |
| An available first-opening value above the preserved `R/2` | [AliceTimingFloor](../../Vegas/Examples/LateOpeningRuntimeAliceTimingFloor.lean), [AliceProtectedOptimality](../../Vegas/Examples/LateOpeningRuntimeAliceProtectedOptimality.lean) |

See [the model reminder and proof](native-se-obstruction.md) for the exact
quantifiers, utility table and source-interface distinction. This is an exact
joint-law negative with the full authentic audit and fair partial observations,
not yet a public-outcome-only negative or a statement about every blockchain.
The smaller-deposit and partial-audit paper variants, protected first-ready
positive, and same-fixture weak PBE still need their own checked capstones.
All runtime scope exclusions stated above continue to apply.
