# Two-player Odds–Evens on the sequential phase runtime

The concrete instance uses the same singleton-phase runtime as the retained
monetary preservation theorem. Its source has two Boolean commitments followed
by two reveals. [The setup](../Vegas/Examples/OddsEvensSetup.lean) computes the
paper's five settlement cases: matching bits pay (126,74), differing bits pay
(74,126), one failed reveal pays (0,200) or (200,0), and two failures pay (0,0).
Utilities are the declared payouts; initial stake deductions, execution fees
and an actual asset-transfer implementation are separate refinements.

[Source existence](../Vegas/Examples/OddsEvensEquilibrium.lean) supplies a
sequential equilibrium of the actual finite intended game. This does not yet
identify the witness with the uniform-bit strategy or prove its expected
payout is 100. The fairness/unique intended-law calculation remains a useful
small source-game follow-up.

[The service](../Vegas/Examples/OddsEvensService.lean) proves the raw-history
opportunity, protected inclusion and completion obligations. Each event has
duration six; the reaction and inclusion bounds are three and two. A legal
trace witnesses activation after an actual clock tick. Players receive no
pending packets in this instance. The scheduler is the existing bounded
reserved-epoch producer and processes its bounded pending batch; it is a
concrete service instance, not a claim about arbitrary public-chain capacity.

The service producer admits sequential plans containing adjacent commitment
phases or adjacent reveal phases. Readiness is confined by either the existing
phase-kind barriers or total source dependencies. The latter applies to this
program without adding dummy source instructions. Existing single-player
service examples remain regression consumers of the former condition.

## Imperfect evidence and funding

[The evidence service](../Interaction/ThinnedEvidenceService.lean) retains or
loses the entire observed evidence list, and separately retains or loses its
reports. The two rates are parameters in [0,1]. Reports have a one-unit delivery
window. Items within a stage have correlated fates; coverage does not assume
independent sampling of individual messages.

For any actual evidence item, observation probability equals the capture rate,
conditional delivery probability equals the delivery rate, and final catch
probability equals their product. [The phase adapter](../Vegas/Pending/PhaseThinnedCollection.lean)
derives the existing count-evidence coverage premise from these kernels.
Capture and delivery rates of one half give catch probability one quarter.
The utility spread is at most 200, so a deposit of 800 meets the theorem's
funding inequality. This deposit is distinct from the 200-unit game pot and
is not charged on the implementing equilibrium's supported paths.

This is an explicit imperfect evidence backend. Its capture operation remains
an evidence-service model: the construction does not derive that operation
from a real network or identify it with the ledger. Malformed authenticated
traffic may require evidence outside ledger inclusion. The operational
availability question in the [open-problems guide](sequential-se-open-problems.md)
therefore remains relevant.

## End-to-end conclusion and next work

[The raw equilibrium](../Vegas/Examples/OddsEvensRawEquilibrium.lean) combines
source existence, actual runtime service and imperfect audit funding. Its
assessment is sequentially rational against all permitted raw deviations,
preserves the source readout/payoff joint law, and excludes and charges nobody
on its supported path. The runtime and evidence service are fixed independently
of the chosen source equilibrium.

This chooses the phase runtime for the concrete example and monetary result;
no payment port to a second runtime is required. The other retained theorem
remains available under its own hypotheses. A paper exposing only one main
runtime theorem can use this shared phase interface without claiming an
equivalence of the two underlying execution games.

Further work can strengthen this instance in three independent ways: identify
the fair uniform source assessment, derive the audit's capture kernel from a
specified operational service, and replace the reserved batch scheduler by a
more selective producer satisfying the same all-history service contract.
