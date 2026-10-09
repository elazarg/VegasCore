# Module architecture

| Layer | Responsibility |
| --- | --- |
| GameTheory | Separately managed probability and game-theory foundation. |
| GameTheoryExtensions | Protocol limits, belief transport, enforcement and probability adapters. |
| Interaction | Signed message networks, partial observation, recall, execution and evidence. |
| Vegas.Foundation and Vegas.Expr | Typed contexts, values and expressions. |
| Vegas.Source | The source language, source information and evaluation. |
| Vegas.EventGraph | Typed dependencies, source-event execution and observations. |
| Vegas.Pending | Runtime packet submission, inclusion, deadlines and pending-message laws. |
| Vegas.Compile | Source-to-graph compiler and correspondence. |
| Vegas.Game | Strategic composition and the checked calendar SE proof. |
| Test libraries and Paper | Regressions and the calendar theorem's axiom pins. |

The [active plan](se-schedule-generalization.md) governs arbitrary-builder work.
The [calendar checklist](se-proof-checklist.md) records checked evidence. The
[archive](../archive/se-generalization/README.md) is searchable reference material,
outside the Lean source and default build roots.

Search with rg and inspect signatures with lean-defs.py before adding machinery.
Useful existing boundaries are the
[source runtime](../Vegas/Game/RevealService.lean),
[compiler observation relation](../Vegas/Compile/EventGraphObservation.lean),
[final-record verdict](../Vegas/Pending/ReactiveSettledVerdict.lean),
[asynchronous contract](../Vegas/Pending/ReactiveAsyncContract.lean),
[scheduler support refinement](../Vegas/Pending/ReactiveAsyncRefinement.lean),
[complete public traffic at raw decisions](../Interaction/ReactiveCompleteObservation.lean),
[behavioral commutation](../Vegas/EventGraph/PolicyCommutation.lean),
[whole-continuation enforcement](../GameTheoryExtensions/Analysis/Enforcement.lean),
[local comparison limit](../GameTheoryExtensions/Analysis/Protocol/LocalSimulationLimit.lean),
[copied-site limit with component completion](../GameTheoryExtensions/Analysis/Protocol/CopiedSiteLimit.lean),
[consistent completion over component laws](../GameTheoryExtensions/Analysis/Protocol/ComponentCompletion.lean),
[proportional belief transport](../GameTheoryExtensions/Analysis/Protocol/ProportionalBeliefTransport.lean),
[posterior exclusion from factored reach weights](../GameTheoryExtensions/Analysis/Protocol/ConsistentLikelihood.lean),
[relative likelihood errors at unreached decisions](../GameTheoryExtensions/Analysis/Protocol/AsymptoticLikelihood.lean),
[finite-prefix scheduler agreement](../Interaction/ReactiveSchedulerPrefix.lean),
[public pending selection under packet erasure](../Interaction/PendingErasureSelection.lean),
[deterministic priority selection under packet erasure](../Interaction/ReactivePriorityErasure.lean),
[authenticated emission order in actual recall](../Interaction/ReactiveEmissionOrder.lean),
[own response counts from actual activation commands](../Interaction/ReactiveResponseAccounting.lean),
[receipt identifiers and permanent rejection](../Interaction/ReactiveReceiptIdentity.lean),
[actual traffic and ledger envelope identity](../Interaction/ReactiveTrafficIdentity.lean),
[policy independence without further activation](../Interaction/ReactivePassiveContinuation.lean),
[the exact behavioral law at a player's final response](../Interaction/ReactivePassiveDecision.lean),
[equilibrium existence in finite reactive runtimes](../Interaction/ReactiveEquilibriumExistence.lean),
[unique accepting receipts for completed source events](../Vegas/Pending/ReactiveAcceptanceUniqueness.lean),
[menu restriction](../GameTheoryExtensions/Protocol/MenuRestriction.lean),
[intended game](../Vegas/Source/IntendedGame.lean),
[choices drawn from an observation-local readout](../GameTheoryExtensions/Math/Probability/ObservedChoice.lean),
[expected regret from pointwise failure gaps](../GameTheoryExtensions/Math/Probability/Regret.lean),
[conditional survival through bounded adaptive opportunities](../GameTheoryExtensions/Math/Probability/Survival.lean),
[survival in scheduler rounds and bounded stopping](../Interaction/ReactiveSurvival.lean),
[explicit probabilistic service in the native evaluator](../Interaction/ReactiveOutage.lean),
[fixed-horizon compiled-outcome obstruction](../Vegas/Game/ProbabilisticServiceObstruction.lean),
[final immutable disclosure readout](../Vegas/Examples/CommittedResolutionBobReadout.lean),
[actual final-disclosure continuation law](../Vegas/Examples/CommittedResolutionBobDecision.lean),
[native disclosure regret under arbitrary beliefs](../Vegas/Examples/CommittedResolutionBobIncentive.lean),
[certain success requires protected acceptance](../Vegas/Examples/LateOpeningRuntimeProtectedReceipt.lean),
[native equilibrium silence after a pending opening](../Vegas/Examples/LateOpeningRuntimeAliceRationality.lean),
[permitted sender packets and accepted but forbidden envelopes](../Vegas/Examples/LateOpeningRuntimeAliceOpeningAudit.lean),
[native final-opening response normalization](../Vegas/Examples/LateOpeningRuntimeAliceOpeningRationality.lean),
[one admissible service after collateral is fixed](../Vegas/Examples/LateOpeningRuntimeAliceNormalization.lean),
[common-service native equilibrium constraints](../Vegas/Examples/LateOpeningRuntimeEquilibriumConstraints.lean),
[public outcome requires protected acceptance](../Vegas/Examples/LateOpeningRuntimePreservingLaw.lean),
[actual first-late sender repair](../Vegas/Examples/LateOpeningRuntimeAliceFirstRationality.lean),
[legal silent-prefix final callbacks](../Vegas/Examples/LateOpeningRuntimeAliceQuietPrefix.lean),
[inactive-owner recall projection](../Interaction/ReactiveInactiveRecall.lean),
[exact final-opening alias payoff laws](../Vegas/Examples/LateOpeningRuntimeAliceOpeningAliases.lean),
[full raw first-binding result invariance](../Vegas/Examples/LateOpeningRuntimeBobRawBinding.lean),
[irreparable omitted first bindings](../Vegas/Examples/LateOpeningRuntimeBobBindingOmission.lean),
[full raw receiver score bounds](../Vegas/Examples/LateOpeningRuntimeBobRawPayoff.lean),
[optimal native logical bit guesses](../Vegas/Examples/LateOpeningRuntimeBobBindingOptimization.lean),
[authentic native bit knowledge and clean publication](../Vegas/Examples/LateOpeningRuntimeBobKnownBit.lean),
[clean native answer continuations](../Vegas/Examples/LateOpeningRuntimeBobSafeContinuation.lean),
[native equilibrium silence before publication settlement](../Vegas/Examples/LateOpeningRuntimeEarlyBobRationality.lean),
[actual information after sender publication failure](../Vegas/Examples/LateOpeningRuntimeBobBindingInformation.lean),
[exact native payoff of truthful bit guesses](../Vegas/Examples/LateOpeningRuntimeBobAnswerPayoff.lean),
[whole-policy bit-guess values under arbitrary native beliefs](../Vegas/Examples/LateOpeningRuntimeBobBindingDecision.lean),
[uniform relative retry bounds](../Vegas/Examples/LateOpeningRuntimeAliceTremble.lean),
[complete native binding prefix probabilities](../Vegas/Examples/LateOpeningRuntimeBindingPrefix.lean),
[native conditional-belief limits](../Vegas/Examples/LateOpeningRuntimeBindingPosterior.lean),
[native posterior-optimal bit guesses](../Vegas/Examples/LateOpeningRuntimeBobPosteriorOptimization.lean),
[raw pending-pool observation kernels](../Vegas/Examples/LateOpeningRuntimeLatePrefixKernel.lean),
[actual raw final-response and typed settlement kernels](../Vegas/Examples/LateOpeningRuntimeLateResponseKernel.lean),
[one native SE consistency witness](../Vegas/Examples/LateOpeningRuntimeConsistency.lean),
[success-case raw answer optimization](../Vegas/Examples/LateOpeningRuntimeBobSuccessOptimization.lean),
[success-case clean settlement on assessed support](../Vegas/Examples/LateOpeningRuntimeBobSuccessSettlement.lean),
[exact settlement forced by source joint-law equality](../Vegas/Examples/LateOpeningRuntimePreservingSettlement.lean),
[protected submission absence from actual receipt recall](../Vegas/Examples/LateOpeningRuntimeProtectedRecall.lean),
[zero protected-submission mass in actual binding prefixes](../Vegas/Examples/LateOpeningRuntimeProtectedPrefix.lean),
[initialized full raw binding prefixes](../Vegas/Examples/LateOpeningRuntimeInitializedPrefix.lean),
[complete receiver observation factors](../Vegas/Examples/LateOpeningRuntimeBindingFactors.lean),
[relative raw retry kernel errors](../Vegas/Examples/LateOpeningRuntimeRetryKernel.lean),
[native retry representatives for private aliases](../Vegas/Examples/LateOpeningRuntimeRetryWitness.lean),
[successful binding cleanliness throughout the information set](../Vegas/Examples/LateOpeningRuntimeBobSuccessBindingClean.lean),
[final publication throughout the information set](../Vegas/Examples/LateOpeningRuntimeBobFinalFiberRationality.lean),
[optional-publication information transfer](../Vegas/Examples/LateOpeningRuntimeOptionalInformation.lean),
[complete optional-publication audit regret](../Vegas/Examples/LateOpeningRuntimeOptionalIncentive.lean),
[supported optional publication across the information set](../Vegas/Examples/LateOpeningRuntimeOptionalPacket.lean),
[full-audit final publication across the information set](../Vegas/Examples/LateOpeningRuntimeBobFinalAuditRationality.lean),
[publication through the original callback sequence](../Vegas/Examples/LateOpeningRuntimeBobDisclosurePublication.lean),
[sender success floor throughout the information set](../Vegas/Examples/LateOpeningRuntimeAliceFullFiberFloor.lean),
[whole settlement payoff laws for genuine private aliases](../Vegas/Examples/LateOpeningRuntimeSettlementContinuation.lean),
[sender value after actual successful settlement](../Vegas/Examples/LateOpeningRuntimeAliceSuccessfulContinuation.lean),
[sender value after actual failed settlement](../Vegas/Examples/LateOpeningRuntimeAliceFailureContinuation.lean),
[retry comparison retaining all original first responses](../Vegas/Examples/LateOpeningRuntimeFirstRetryComparison.lean),
[actual likelihood after an earlier observed opening](../Vegas/Examples/LateOpeningRuntimeSeenLikelihood.lean),
[initialized complete-history likelihood after an earlier observed opening](../Vegas/Examples/LateOpeningRuntimeInitializedSeenLikelihood.lean),
[positive collection over finite contingent plans](../GameTheoryExtensions/Analysis/PositiveCollection.lean),
[finite reliability gaps and disclosure incentives](../GameTheoryExtensions/Analysis/DisclosureReliability.lean),
[finite-deposit SE extension under a terminal audit](../GameTheoryExtensions/Analysis/Protocol/TerminalAudit.lean),
[the owner's information through its own phase](../Vegas/Pending/ReactiveOwnerPhase.lean),
[permitted deviations phase by phase](../Vegas/Game/SourceServiceDeviationLaw.lean),
[whole-policy deviations under a restriction](../GameTheoryExtensions/Analysis/Protocol/RetainedDeviation.lean),
[the first-turn coupling against one deviator](../Vegas/Game/ServiceTimingCoupling.lean),
[one deviator against an arbitrary builder, phase by phase](../Vegas/Game/AsyncDeviationLaw.lean),
[one deviator up to withholding on a reveal-relaxed graph](../Vegas/Game/AsyncWithholdLaw.lean),
and [depth-free extension](../GameTheoryExtensions/Analysis/Protocol/PassageRestrictionExtension.lean).

Behavioral commutation preserves the typed store and original own recall;
native traffic and conditional beliefs need their own argument. Enforcement
uses actual gain and change in charge probability; it does not construct the
runtime's collection mechanism or assessment.
The probability regret module also combines two attainable value comparisons:
silence with an incumbent continuation and a separate nonnegative outside
continuation. A payoff bound on costly packets alone does not establish
silence. Actual traffic identity is needed before a receipt identifier can
authenticate an envelope's complete payload and certificate.
Likelihood adapters require grouped weights of actual compatible histories;
absolute error bounds do not control beliefs when the observation mass also
vanishes. Erasure-independent selection supplies no service contract by itself.

Imports expose results; they do not establish that the headline theorem uses
those results. The SE evidence check examines declaration dependencies. New
adapters need actual runtime premises, not hypotheses restating desired
posteriors, comparisons or equilibrium existence.
