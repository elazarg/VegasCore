# Two-player Odds–Evens on the forced-exit runtime

The source has two Boolean commitments followed by two reveals. [The setup](../Vegas/Examples/OddsEvensSetup.lean)
computes the paper's five settlement cases: matching bits pay (126,74), differing
bits pay (74,126), one failed reveal pays (0,200) or (200,0), and two failures pay
(0,0). Utilities are the declared payouts; initial stake deductions, execution
fees and actual asset transfer are separate refinements.

[The fair source assessment](../Vegas/Examples/OddsEvensFairProfile.lean) chooses
independent uniform bits and performs the intended reveals. Its actual source
information sets, consistent Bayes beliefs and sequential rationality are
checked in [the value proof](../Vegas/Examples/OddsEvensFairValue.lean). Every
unilateral intended policy has expected payout 100 against the fair opponent.
[The law proof](../Vegas/Examples/OddsEvensFairLaw.lean) identifies the complete
typed terminal/payoff distribution and derives expected payout 100 for each
player. [The full-source extension](../Vegas/Examples/OddsEvensFullSource.lean) supplies
a sequential equilibrium of the ordinary source menus, where failed commitments
and withheld reveals are legal, with the same joint law. It uses the existing
zero payout for an owner whose reveal fails, without an added forfeit. It
establishes existence of this extension, not preservation of every full-source SE.

## Actual service

[The service](../Vegas/Examples/OddsEvensRecoveryService.lean) runs the ordinary
forced-exit application. Failure permanently excludes its owner; there is no
checkpoint, attempt number or rollback. Each event has duration six, with
reaction and inclusion bounds three and two.

Each cycle processes at most 64 pending envelopes, offers callbacks to Even
then Odd on odd cycles, checks the four expirations, and advances the clock.
There are 32 cycles. Players receive no pending packets in this concrete
instance. This is a bounded periodic service instance, not a necessity claim
about blockchain scheduling or capacity.

The [clock](../Vegas/Examples/OddsEvensRecoveryClock.lean),
[opportunity](../Vegas/Examples/OddsEvensRecoveryOpportunity.lean),
[receipt](../Vegas/Examples/OddsEvensRecoveryReceipts.lean),
[capacity](../Vegas/Examples/OddsEvensRecoveryCapacity.lean) and
[completion](../Vegas/Examples/OddsEvensRecoveryCompletion.lean) proofs concern
actual raw histories, including deviations and histories after exclusion.
Rejected application calls still receive ledger receipts. The pending bound
comes from counting every possible callback transmission within the finite
horizon; it is not inferred from honest play.

## Imperfect evidence and funding

[The evidence service](../Interaction/ThinnedEvidenceService.lean) retains or
loses the entire observed evidence list, and separately retains or loses its
reports. The two rates are parameters in [0,1]. Reports have a one-unit delivery
window. Items within a stage have correlated fates; coverage does not assume
independent sampling of individual messages.

For each actual evidence item, final catch probability is the product of the
capture and delivery rates. [The count adapter](../Vegas/Pending/ThinnedCountCollection.lean)
derives the existing evidence-coverage premise from these kernels. Rates of
one half give catch probability one quarter. The utility spread is at most
200, so deposit 800 meets the funding inequality. This deposit is separate
from the game pot and incurs no charge on the implementing equilibrium's paths.

Capture remains an evidence-service model; it is not derived from a real
network or identified with the ledger. Malformed authenticated traffic may
require evidence outside ledger inclusion. The operational availability
question in the [open-problems guide](sequential-se-open-problems.md) remains.

## End-to-end scope

[The raw equilibrium](../Vegas/Examples/OddsEvensRecoveryRawEquilibrium.lean)
combines the source assessment, actual service and imperfect audit funding.
Every intended source SE has a raw-runtime SE preserving its readout/payoff
joint law, with nobody excluded or charged on the supported paths. The runtime
and evidence service are fixed before the source equilibrium is chosen.
Specializing to the explicit fair assessment gives its exact joint law and
expected payout 100 per player.

[Monetary preservation](../Vegas/Game/RecoveryPaymentPreservation.lean) uses the
same forced-exit runtime and distinguishes executable cash from valuation.
Neither result needs phase recovery machinery. Concurrent SE preservation is
separate research; its failure rules must be justified by its own argument.

Useful refinements are an operational evidence-capture producer, a more
selective service satisfying the same all-history contract, and concrete
instances with nonempty partial pending observation. The general recovery
preservation theorem already permits arbitrary finitely branching observation.
