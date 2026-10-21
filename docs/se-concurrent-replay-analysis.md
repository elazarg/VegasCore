# Replay analysis: an exact foreign-alias reduction

The proposed stopped chronological construction in
[the likelihood note](se-concurrent-likelihood.md) has agent review of local
arguments. Exhaustive weighted coverage and preparation provenance still have
mathematical gaps. Its Lean theorem and end-to-end preservation remain unproved.
The following reductions record reviewed local
parts of that argument: foreign private syntax aliases do not require equal
alias counts, or a bijection of raw aliases, between different target catalogues.
The likelihood derivation states the target reconstruction; the local
reductions here do not prove its global coverage claim.

## The quotient and its operational effect

At each foreign callback retain `PhaseProposal.responseClass`: the typed
binding preparation, if present, and the exact emitted packet. Retain every
focal raw action literally. Restrict to the no-foreign-generated-BAD slice.
The foreign callback cases have the following exhaustive behavior on genuine
counted histories.

* At a ready binding, the counted shape theorem gives a fresh prepared handle
  owned by the actor. A proper preparation class fixes its opening data
  exactly to `Raw.mk payload value`: a raw value of another type or no opening
  would have failure class. Thus two proper aliases of this class perform the
  same candidate update. `Submission.register` and
  `Submission.candidateAfter_eq` in `EventSubmission.lean` show that no other
  candidate, semantic cell, clock, or accepted handle changes during this
  preparation. Equal emitted packets give equal subsequent network effects.
* At an opening, the class fixes the complete packet, including its plaintext.
  The auxiliary `Submission.opening` field is ignored by
  `Submission.register` for this constructor. The resulting application and
  network effects therefore agree for every alias.
* Silence is the single action with no transmission. Spent or disabled counted
  callbacks have no additional nonsilent branch.

Consequently aliases in one retained foreign class have identical successor
application and network states. Only the acting foreign player's literal raw
recall can differ. Its emitted-output list and submission count agree. The
exact existing theorem `phaseProposalReferencePolicy_congr_input` in
`PhaseProposalReference.lean` then identifies its entire future policy whenever
these summaries and its current view agree. For every other owner the ordinary
input already agrees. This proves the needed closure under later callbacks;
equality of just the current packet marginal would not prove it.
For a fixed original reserved tape, `ReservedEpoch.command` also agrees: it
reads the environment-command count, the pending head, and the public phase,
all preserved here. No equality of arbitrary scheduler policies is asserted.

Foreign failure classes are deliberately outside this argument. A wrong-type
raw preparation can leave a different private candidate from a missing
preparation even when their typed failure classes coincide. The
no-foreign-generated-BAD restriction removes these classes. Focal failure and
alias actions are never quotiented; they stay in the literal focal recall.

## Exact finite-path summation

For any fixed initialized draw and tape, induct on the remaining finite native
execution length. The previous operational equality makes every continuation
quantity measurable on the quotient constant across one foreign alias fiber.
Summing its original conditional action probabilities therefore gives the
class probability, exactly as
`phaseProposalReferenceResponses_project` states. All focal and environment
steps remain their original kernels. Repeating this equality proves that the
pushforward of the actual raw path law is the path law with these foreign
class kernels. Initialization and the original tape weights are untouched.

This sums every actual foreign alias preimage once: the fibers of the actual
`projectResponse` are a partition, and the law is pushed forward rather than
replaced by a chosen representative. No cardinality comparison between fibers
at different states is used. Zero class atoms remain zero. Conditioning on
no foreign BAD and occupation at the focal information set is permitted:
foreign BAD is determined by retained preparation classes, and the focal full
information is unchanged by the eliminated foreign recall. The same applies
to a physical admission gate, which reads the retained application, packets,
and receipts.

This removes raw-alias multiplicity from the remaining replay obligation. It
does not identify the class laws across two different hidden-value targets.
Cross-target identification instead uses the chronological source-query and
addressed saved/restore construction at every retained proper SEND.

## Attach the auxiliary source history after projection

Use the existing full-history projection `pi` from
[`phaseProposalReference_alias_history`](../Vegas/Game/PhaseProposalAliasHistory.lean).
It preserves the complete application and network history and the focal
player's literal information. Choose the auxiliary source witness and its
source-cause annotation kernel `K` on `pi(h)`, retaining the literal initial
draw, and pull that choice back to the original experiment. Then summing raw
aliases before attaching `K` is exactly the same probability law as attaching
`K(pi(h))` to each raw history and summing afterward. This is ordinary finite
`map`/`bind` composition; it does not require uniqueness of independently
chosen source witnesses.

Project the predecision reference experiment, the literal focal response and
the subsequent ordinary continuation separately, then compose their kernels.
The generic history-projection API applies from a supplied starting history;
the ordinary continuation has the required outputs/count/view congruence.
There is no need to represent the change of policy at the selected decision
as one global behavioral policy. Foreign policies that inspect their raw
alias names are outside this argument.

Use the actual operational normalizer, which preserves registered raw values,
including unusable preparations. It is finer than the response-class quotient
on arbitrary BAD actions. On genuine proper binding and opening actions its
fibers agree with the relevant response classes. Generated-BAD qualification,
the first-close admission gate and physical finish payoffs are preserved.

This removes the same-input raw-alias issue from the proposed mathematical
transport. It does not establish reconstruction across different hidden
inputs or values, their weighted source marginal, or the source payoff law.
Those remain open. No additional Lean theorem is claimed by this reduction.

## The remaining getter obligation is smaller than full-history equality

The definitions `phaseVirtualSourceView?`, `phaseVirtualSourceQuery?`, and
`phaseProposalQuery?` read only the current actor's masked typed store, the
virtual repair of introduced unusable cells, the numeric public address/control
word, and the observed proposal archive. The final erased information removes
past private signals and own-play tags. Therefore a replay need not identify a
target's latent full source history with a canonical decoder history. It must
instead prove equality of these actual readout inputs at the addressed
occurrence. In particular the saved logical store must be the selected saved
checkpoint, not merely a store with the same public projection.

On the clean-current comparison branch, the observable absence of current
own binding failure covers every unresolved own failed binding, rather than
only the currently requested event. This follows the existential `pending`
field of `Config.FailedBinding` and the original, unrepaired typed-view
classifier `phaseProposalCurrentBindingFailure`. All earlier current-block
own commitments are still unresolved at a binding decision. Canceled BAD
actions remain in recall but their restored-away cells do not trigger the
classifier. This distinction is required when showing that the focal live
view already agrees with its virtual repair; admission receipts alone do not
establish typed properness.

This local reduction alone does not supply chronological target reconstruction
or the common qualified coefficient. Those are supplied by the stopped
construction reviewed in the likelihood note, together with its same-joint
postclose payoff attachment.

## A full source information fiber fixes the historical omission mask

There is also no freedom to change a historical source omission pattern while
holding the full focal `J` fixed. `commitRecoverySignals` records the exclusion
set, generation, and saved rank after every source instruction; full recall
retains all these signals. `proposalRecoverySignals` retains the same data and
adds proposal deltas. The source view's position identifies the static rank.
Thus each historical row has fixed rank, attempt, and exclusion sets immediately
before and after it, including rows at the end of a canceled attempt.

For a commitment owned by `j`, inspect `ProtocolState.recoveryStep` in
`CommitRecoveryStep.lean`. If `j` is already excluded, the row is automatic and
the exclusion set does not change. Otherwise the owner is inserted exactly
when the move's `missing` flag is true; an admitted unusable binding does not
insert it. `CommitRecoveryState.close_excluded` preserves this exact set
through clean close, retry, and exhaustion. Therefore the ordered full signals
determine each commitment row as inherited automatic, active missing, or active
admitted. On the foreign-good slice an active admitted foreign row is proper;
the full focal own-play coordinate separately determines whether an admitted
focal row was proper or BAD.

This proves constancy of the source mask on the full `J` fiber. It does not
prove that a fixed native skeleton realizes this mask for every target in that
fiber; that physical/source alignment remains part of chronological replay.

## A foreign miss cannot synthesize a surviving focal action

A historical concurrent attempt cannot retry before an unsubmitted surviving
focal row resolves. `PhaseRuntimeState.settle` checks `phase.Finished` only
after `RuntimePhase.drain`; `Finished` requires every event of the installed phase
completed. The drain selects only `AutomaticReady` events whose owner is
already excluded. Accordingly `drainFuel_completed_survivor` preserves the
completion status of every surviving focal event. A foreign miss alone cannot
complete the missing focal row.

Before this attempt can retry, that focal row must therefore be admitted or
expire. Expiry immediately inserts its owner into the permanent exclusion set,
so it cannot precede a later active focal information set. Every earlier closed
attempt of a currently surviving focal owner consequently has its actual focal
binding admissions. There is no canceled auxiliary focal typed choice absent
from native recall which must be remembered by the selected full source `J`.

## A later physical miss does not alter an earlier binding query

Consider one historical failed attempt: a static-earlier foreign row misses,
but a static-later owner sends before that miss physically expires. The source
owner's raw source signal contains the new exclusion while its actual native
callback did not. Rank truncation alone would not identify their domain keys.

The actual `commitRecoveryNoMissInformation` removes this difference. At an
active commitment it applies `commitRecoveryWithAttemptExclusions` from the
computed attempt-entry cut with the saved-entry exclusion set.
`attemptSignal` replaces the exclusion component of every signal at or after
that cut; `attemptWord` applies this to the entire current signal word, and
the same operation transforms the own-play information tags. The generation
and saved-rank components remain unchanged. Subsequent erased information
discards past private signals and own actions. Other owners' binding cells
are hidden, and this commitment interval has no public value writes.

Consequently the source normalized key does not retain the prospective
current-attempt miss. It agrees with the native query's current-segment word
using the saved-entry exclusions even when the physical SEND preceded the
expiry. Earlier completed attempts retain their literal public exclusion
words on both sides. This argument applies at each historical callback; it
does not rely on the current all-TRUE gate removing earlier failed attempts.
