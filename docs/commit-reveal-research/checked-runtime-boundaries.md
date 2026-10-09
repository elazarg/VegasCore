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
This family has no checked late-packet erasure-independence property.

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
guarantee. **The service-contract family above and this erasure-independent
lottery are separate constructions.** Their conjunction in the two-late
counterexample's single scheduler remains an unproved native adapter.

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
