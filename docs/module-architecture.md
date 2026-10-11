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
| Vegas.Game | Strategic composition, source equilibrium extension, runtime preservation and obstruction proofs. |
| Test libraries and Paper | Regressions and checked capstone axiom guards. |

The [active plan](se-schedule-generalization.md) governs work beyond the fixed calendar.
The [calendar checklist](se-proof-checklist.md) records checked evidence. The
[archive](../archive/se-generalization/README.md) is searchable reference material,
outside the Lean source and default build roots.

Search with rg and inspect signatures with lean-defs.py before adding machinery.
Useful existing boundaries are the
[source runtime](../Vegas/Game/RevealService.lean),
[fixed service specification](../Vegas/Game/SourceServiceSpec.lean),
[compiler observation relation](../Vegas/Compile/EventGraphObservation.lean),
[final-record verdict](../Vegas/Pending/ReactiveSettledVerdict.lean),
[asynchronous contract](../Vegas/Pending/ReactiveAsyncContract.lean),
[scheduler support refinement](../Vegas/Pending/ReactiveAsyncRefinement.lean),
[complete public traffic at raw decisions](../Interaction/ReactiveCompleteObservation.lean),
[independent event action kernels](../Vegas/EventGraph/KernelCommutation.lean),
[behavioral commutation](../Vegas/EventGraph/PolicyCommutation.lean),
[whole-continuation enforcement](../GameTheoryExtensions/Analysis/Enforcement.lean),
[local comparison limit](../GameTheoryExtensions/Analysis/Protocol/LocalSimulationLimit.lean),
[copied-site limit with component completion](../GameTheoryExtensions/Analysis/Protocol/CopiedSiteLimit.lean),
[consistent completion with whole-player rationality and fixed opponent laws](../GameTheoryExtensions/Analysis/Protocol/PrescribedCompletion.lean),
[consistent completion over component laws](../GameTheoryExtensions/Analysis/Protocol/ComponentCompletion.lean),
[proportional belief transport](../GameTheoryExtensions/Analysis/Protocol/ProportionalBeliefTransport.lean),
[posterior exclusion from factored reach weights](../GameTheoryExtensions/Analysis/Protocol/ConsistentLikelihood.lean),
[relative likelihood errors at unreached decisions](../GameTheoryExtensions/Analysis/Protocol/AsymptoticLikelihood.lean),
[finite-prefix scheduler agreement](../Interaction/ReactiveSchedulerPrefix.lean),
[scheduler laws through backend observations](../Interaction/ReactiveSchedulerObservation.lean),
[public pending selection under packet erasure](../Interaction/PendingErasureSelection.lean),
[deterministic priority selection under packet erasure](../Interaction/ReactivePriorityErasure.lean),
[authenticated emission order in actual recall](../Interaction/ReactiveEmissionOrder.lean),
[own response counts from actual activation commands](../Interaction/ReactiveResponseAccounting.lean),
[receipt identifiers and permanent rejection](../Interaction/ReactiveReceiptIdentity.lean),
[distinct authored ledger identifiers](../Interaction/MessageLedgerCount.lean),
[observer-local submission and ledger accounting](../Interaction/ReactiveSubmissionSerial.lean),
[actual traffic and ledger envelope identity](../Interaction/ReactiveTrafficIdentity.lean),
[policy independence without further activation](../Interaction/ReactivePassiveContinuation.lean),
[the exact behavioral law at a player's final response](../Interaction/ReactivePassiveDecision.lean),
[the native recovery kernel with arbitrary later callbacks](../Vegas/Pending/ReactiveRecoveryContinuation.lean),
[joint private-memory conditioning through actual scheduler rounds](../Interaction/ReactiveImplementationProfile.lean),
[equilibrium existence in finite reactive runtimes](../Interaction/ReactiveEquilibriumExistence.lean),
[unique accepting receipts for completed source events](../Vegas/Pending/ReactiveAcceptanceUniqueness.lean),
[menu restriction](../GameTheoryExtensions/Protocol/MenuRestriction.lean),
[intended game](../Vegas/Source/IntendedGame.lean),
[successful bindings inside arbitrary admission menus](../Vegas/Source/AdmissionRestriction.lean),
[persistent failed-binding obligations](../Vegas/Source/FailedBinding.lean),
[actual value-history representations of unilateral failed-binding deviations](../Vegas/Source/BindingRepairTrace.lean),
[actual continuation kernels against copied value-interface opponents](../Vegas/Source/BindingRepairContinuation.lean),
[value-binding continuation mixtures at actual source information sites](../Vegas/Source/ProtocolValueBindingContinuation.lean),
[intended SE preservation under arbitrary admission](../Vegas/Game/IntendedPreservation.lean),
[value-only SE preservation under arbitrary admission](../Vegas/Game/ValueAdmissionPreservation.lean),
[initialized private-intention uniqueness and restoration](../Vegas/Pending/ReactivePosteriorUniqueness.lean),
[accepted original intentions in initialized executions](../Vegas/Pending/ReactiveAcceptedIntentionRecall.lean),
[original-action configurations and actual sampler laws](../Vegas/Pending/ReactiveOriginalConfig.lean),
[raw unilateral callbacks and mixed foreign-frontier replay](../Vegas/Pending/ReactiveDeviationRecall.lean),
[opaque binding responses and foreign activation inputs](../Vegas/Pending/ReactiveBindingNoise.lean),
[foreign original source recall through raw callbacks](../Vegas/Game/ReactiveSourceForeignRecall.lean),
[original-action retention through actual responses](../Vegas/Pending/ReactiveOriginalResponseStability.lean),
[original-action retention through actual packet inclusion](../Vegas/Pending/ReactiveOriginalInclusionStability.lean),
[fresh sampled events outside retained intention frontiers](../Vegas/Pending/ReactiveSampledFrontierFreshness.lean),
[owner-authenticated joint intention frontiers](../Vegas/Pending/ReactiveSampledFrontierOwnership.lean),
[reachable frontiers through actual compiler responses](../Vegas/Pending/ReactiveFrontier.lean),
[unique semantic frontiers from genuine retained memory](../Vegas/Pending/ReactiveFrontierUniqueness.lean),
[actual pending inclusion preserving original decisions](../Vegas/Pending/ReactiveFrontierInclusion.lean),
[canonical continuation through actual callbacks and environment commands](../Vegas/Pending/ReactiveFrontierPotential.lean),
[posterior conservation through complete rounds and terminal execution](../Vegas/Pending/ReactiveFrontierExecution.lean),
[silent resolution expiry preserving original decisions](../Vegas/Pending/ReactiveFrontierExpiry.lean),
[physical readiness and foreignness of retained pending intentions](../Vegas/Pending/ReactivePendingFrontierReadiness.lean),
[foreign completion sequences preserving decision kernels](../Vegas/EventGraph/ForeignCompletionSequence.lean),
[reachable restriction to causal cuts and exact foreign replay](../Vegas/EventGraph/ConfigRestriction.lean),
[retained evaluations through foreign completion](../Vegas/EventGraph/ForeignCompletionEvaluation.lean),
[completed-output agreement and terminal stores](../Vegas/EventGraph/CompletedOutputAgreement.lean),
[canonical continuation at sampled pending-event frontiers](../Vegas/Pending/ReactiveSampledFrontierContinuation.lean),
[original sampled bindings through actual delayed acceptance](../Vegas/Pending/ReactiveSampledBindingSettlement.lean),
[original sampled resolutions through actual acceptance](../Vegas/Pending/ReactiveSampledResolutionSettlement.lean),
[silent original resolutions through delayed expiry](../Vegas/Pending/ReactiveSampledSilentSettlement.lean),
[sampled frontier outputs agreeing with physical settlement](../Vegas/Pending/ReactiveSampledValueAgreement.lean),
[timely actual owner responses before expiry](../Vegas/Pending/ReactiveOwnerOpportunity.lean),
[sample coverage through actual prescribed callbacks](../Vegas/Pending/ReactiveResponseSampling.lean),
[actual callback chronology and activation clocks](../Vegas/Pending/ReactiveChronologicalRecall.lean),
[immutable evaluation at recorded resolutions](../Vegas/Pending/ReactiveResolutionRecall.lean),
[recorded conformance from timely prescribed responses](../Vegas/Pending/ReactiveTimelyCalls.lean),
[unique event emissions on prescribed runs](../Vegas/Pending/ReactiveSingleSubmission.lean),
[canonical prepared-slot allocation and prescribed-envelope conformance](../Vegas/Pending/ReactivePrescribedAllocation.lean),
[fresh service calls from timely supported responses](../Vegas/Game/SourceServicePrescribedCall.lean),
[protected timely calls excluding due expiry](../Vegas/Game/SourceServiceExpiry.lean),
[disclosing source joint laws under every graph execution mode](../Vegas/Compile/EventGraphDisclosurePolicy.lean),
[actual concurrent reveal-order dependence with withholding](../Vegas/Examples/ConcurrentRevealOrderLaw.lean),
[compiled canonical continuation decoded to the source law](../Vegas/Compile/EventGraphCanonicalContinuation.lean),
[joint initialized source/runtime laws under protected asynchronous service](../Vegas/Game/SourceServiceReactiveLaw.lean),
[zero authentic standard audit charge and joint realized net-payoff laws](../Vegas/Game/SourceServiceReactiveAudit.lean),
[actual prescribed first-opportunity response laws](../Vegas/Pending/ReactiveFirstOpportunity.lean),
[repeated prescribed turns under arbitrary raw opponents](../Vegas/Pending/ReactiveRecordedOpportunity.lean),
[source-event boundary advance for arbitrary raw continuations](../Vegas/Game/SourceServiceRawCompletionBoundary.lean),
[first source decisions under arbitrary raw opponents](../Vegas/Game/ReactiveSourceFirstOpportunity.lean),
[private posterior stability through off-turn callbacks](../Vegas/Pending/ReactiveOffTurnPosterior.lean),
[original source recall through actual responses](../Vegas/Game/ReactiveSourceResponseRecall.lean),
[joint external execution and original source recall](../Vegas/Game/ReactiveSourceResponseLaw.lean),
[reactive source decision laws](../Vegas/Game/ReactiveSourceDecision.lean),
[acceptance of recorded source calls during their live window](../Vegas/Game/ReactiveSourceAcceptance.lean),
[live-window acceptance of supported prescribed source responses](../Vegas/Game/ReactiveSupportedSourceAcceptance.lean),
[full source observations at chronological reactive prefixes](../Vegas/Game/ReactiveSourceObservation.lean),
[choices drawn from an observation-local readout](../GameTheoryExtensions/Math/Probability/ObservedChoice.lean),
[expected regret from pointwise failure gaps](../GameTheoryExtensions/Math/Probability/Regret.lean),
[conditional survival through bounded adaptive opportunities](../GameTheoryExtensions/Math/Probability/Survival.lean),
[survival in scheduler rounds and bounded stopping](../Interaction/ReactiveSurvival.lean),
[explicit probabilistic service in the native evaluator](../Interaction/ReactiveOutage.lean),
[fixed-horizon compiled-outcome obstruction](../Vegas/Game/ProbabilisticServiceObstruction.lean),
[final immutable disclosure readout](../Vegas/Examples/CommittedResolutionBobReadout.lean),
[actual final-disclosure continuation law](../Vegas/Examples/CommittedResolutionBobDecision.lean),
[native disclosure regret under arbitrary beliefs](../Vegas/Examples/CommittedResolutionBobIncentive.lean),
[native Alice completion against any fixed Bob policy](../Vegas/Examples/LateOpeningRuntimeEquilibrium.lean),
[native label symmetry through every raw packet handler](../Vegas/Examples/LateOpeningRuntimeLabelSymmetry.lean),
[authenticated native label transition symmetry](../Vegas/Examples/LateOpeningRuntimeLabelTransitions.lean),
[native execution, raw-menu and prior label symmetry](../Vegas/Examples/LateOpeningRuntimeLabelHistories.lean),
[actual legal native traces and complete Bob information under label permutations](../Vegas/Examples/LateOpeningRuntimeLabelTrace.lean),
[legal native history and Bob information-fiber label bijections](../Vegas/Examples/LateOpeningRuntimeLabelOrbits.lean),
[concrete late-opening game data](../Vegas/Examples/LateOpeningRuntimeGame.lean),
[certain success requires protected acceptance](../Vegas/Examples/LateOpeningRuntimeProtectedReceipt.lean),
[native equilibrium silence after a pending opening](../Vegas/Examples/LateOpeningRuntimeAliceRationality.lean),
[permitted sender packets and accepted but forbidden envelopes](../Vegas/Examples/LateOpeningRuntimeAliceOpeningAudit.lean),
[native final-opening response normalization](../Vegas/Examples/LateOpeningRuntimeAliceOpeningRationality.lean),
[one admissible service after collateral is fixed](../Vegas/Examples/LateOpeningRuntimeAliceNormalization.lean),
[actual sender and receiver continuation rationality](../Vegas/Examples/LateOpeningRuntimeContinuationRationality.lean),
[actual sender response-normalization predicates](../Vegas/Examples/LateOpeningRuntimeAliceResponseNormalization.lean),
[authentic all-or-none traffic charges and successful-binding continuation payoffs](../Vegas/Examples/LateOpeningRuntimeAllOrNoneTrafficAudit.lean),
[all-or-none Alice continuation comparisons](../Vegas/Examples/LateOpeningRuntimeAllOrNoneAlice.lean),
[sampled binding comparisons with quiet failed or dirty successful publications](../Vegas/Examples/LateOpeningRuntimeAllOrNoneBinding.lean),
[sampled binding comparisons after clean successful publication](../Vegas/Examples/LateOpeningRuntimeAllOrNoneCleanBinding.lean),
[sampled continuation comparisons after successful receiver binding](../Vegas/Examples/LateOpeningRuntimeAllOrNonePostBinding.lean),
[sampled dirty failed-publication binding comparisons](../Vegas/Examples/LateOpeningRuntimeAllOrNoneDirtyFailedBinding.lean),
[exhaustive actual sampled receiver continuation comparisons](../Vegas/Examples/LateOpeningRuntimeAllOrNoneRationality.lean),
[actual sampled early receiver silence](../Vegas/Examples/LateOpeningRuntimeAllOrNoneEarlyBob.lean),
[uniform sampled native and fixed-source SE obstruction](../Vegas/Examples/LateOpeningRuntimeAllOrNoneSeObstruction.lean),
[realized source-law preservation under all-or-none sampling](../Vegas/Examples/LateOpeningRuntimeAllOrNonePreservingSettlement.lean),
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
[full native binding information fibers](../Vegas/Examples/LateOpeningRuntimeBobBindingFiber.lean),
[rejected receiver traffic and sunk charges on dirty information fibers](../Vegas/Examples/LateOpeningRuntimeBobDirtyPrefix.lean),
[actual first-binding service after arbitrary receiver traffic](../Vegas/Examples/LateOpeningRuntimeBobBindingTransport.lean),
[receiver score ceilings after a sunk charge](../Vegas/Examples/LateOpeningRuntimeBobDirtyScore.lean),
[fresh answer attainment throughout dirty information fibers](../Vegas/Examples/LateOpeningRuntimeBobDirtyAttainment.lean),
[actual whole-policy context values on dirty information fibers](../Vegas/Examples/LateOpeningRuntimeBobDirtyContext.lean),
[supported receiver score optimality on dirty information fibers](../Vegas/Examples/LateOpeningRuntimeBobDirtyOptimization.lean),
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
[one common native consistency witness](../Vegas/Examples/LateOpeningRuntimeConsistency.lean),
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
[canonical publication after a sunk rejection charge](../Vegas/Examples/LateOpeningRuntimeBobSunkDisclosure.lean),
[rational publication throughout dirty final information sets](../Vegas/Examples/LateOpeningRuntimeBobDirtyFinalFiber.lean),
[whole-policy optional continuation laws on dirty information sets](../Vegas/Examples/LateOpeningRuntimeBobDirtyOptionalContext.lean),
[optional failure regret after a sunk charge](../Vegas/Examples/LateOpeningRuntimeBobDirtyOptionalRationality.lean),
[optional failure exclusion across every hidden history](../Vegas/Examples/LateOpeningRuntimeBobDirtyOptionalFiber.lean),
[binding-to-publication under the original strategy after arbitrary earlier traffic](../Vegas/Examples/LateOpeningRuntimeBobDirtyDisclosurePublication.lean),
[protected sender lottery floors against rational future receiver play](../Vegas/Examples/LateOpeningRuntimeAliceProtectedPublication.lean),
[sender reward bounds by private label](../Vegas/Examples/LateOpeningRuntimeAliceSuccessFloor.lean),
[full-audit final publication across the information set](../Vegas/Examples/LateOpeningRuntimeBobFinalAuditRationality.lean),
[publication through the original callback sequence](../Vegas/Examples/LateOpeningRuntimeBobDisclosurePublication.lean),
[sender success floor throughout the information set](../Vegas/Examples/LateOpeningRuntimeAliceFullFiberFloor.lean),
[whole settlement payoff laws for genuine private aliases](../Vegas/Examples/LateOpeningRuntimeSettlementContinuation.lean),
[sender value after actual successful settlement](../Vegas/Examples/LateOpeningRuntimeAliceSuccessfulContinuation.lean),
[sender value after actual failed settlement](../Vegas/Examples/LateOpeningRuntimeAliceFailureContinuation.lean),
[retry comparison retaining all original first responses](../Vegas/Examples/LateOpeningRuntimeFirstRetryComparison.lean),
[actual likelihood after an earlier observed opening](../Vegas/Examples/LateOpeningRuntimeSeenLikelihood.lean),
[initialized complete-history likelihood after an earlier observed opening](../Vegas/Examples/LateOpeningRuntimeInitializedSeenLikelihood.lean),
[initialized complete-history likelihood without an earlier observed opening](../Vegas/Examples/LateOpeningRuntimeInitializedUnseenLikelihood.lean),
[actual successful label readout](../Vegas/Examples/LateOpeningRuntimeInitializedSuccessReadout.lean),
[paired native posterior cross-identities from one consistency witness](../Vegas/Examples/LateOpeningRuntimeLabelCross.lean),
[exact lawful sender timing values](../Vegas/Examples/LateOpeningRuntimeAliceTimingValues.lean),
[rational sender timing probabilities](../Vegas/Examples/LateOpeningRuntimeAliceTimingSorting.lean),
[protected and late sender value bounds retaining original future policies](../Vegas/Examples/LateOpeningRuntimeAliceProtectedOptimality.lean),
[native outcome exclusion from continuation rationality and consistency](../Vegas/Examples/LateOpeningRuntimeSeObstruction.lean),
[one native SE obstruction service after collateral is fixed](../Vegas/Examples/LateOpeningRuntimeUniformSeObstruction.lean),
[the concrete value-only source SE extension to immediate failed bindings](../Vegas/Examples/LateOpeningRuntimeSourceForfeiture.lean),
[one full-forfeiture source SE excluded by arbitrarily reliable native services](../Vegas/Examples/LateOpeningRuntimeSourceSeObstruction.lean),
[positive collection over finite contingent plans](../GameTheoryExtensions/Analysis/PositiveCollection.lean),
[finite reliability gaps and disclosure incentives](../GameTheoryExtensions/Analysis/DisclosureReliability.lean),
[finite-deposit SE extension under a terminal audit](../GameTheoryExtensions/Analysis/Protocol/TerminalAudit.lean),
[exact pure settlement from zero expected deductions](../GameTheoryExtensions/Analysis/Protocol/TerminalAuditSettlement.lean),
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
The recovery callback comparison retains the genuine private posterior,
every opponent continuation and the actual action-indexed native kernel,
including the incumbent recovery policy at every later callback. It requires
source values to equal that kernel's expected payoff and supported source
actions to maximize those values. Global integrability suffices for both
compared laws. The final-callback case additionally removes the owner's future
policy using genuine absence of further activation. Deriving source-value
correspondence at arbitrary off-path sites and extending one-response domination
to arbitrary whole continuation policies remain separate obligations.
The [event-kernel diamond](../Vegas/EventGraph/KernelCommutation.lean) requires
kernel stability only along supported actions and intermediate outcomes. It
preserves the typed store for arbitrary independent events; preserving original
own recall additionally requires that no player owns both events. Ownerless
chance events instantiate the same evaluator and diamond.
The [service specification](../Vegas/Game/SourceServiceSpec.lean) owns calendar
service data and basic readouts independently of local continuation comparisons.
The probability regret module also combines two attainable value comparisons:
silence with an incumbent continuation and a separate nonnegative outside
continuation. A payoff bound on costly packets alone does not establish
silence. Actual traffic identity is needed before a receipt identifier can
authenticate an envelope's complete payload and certificate.
Likelihood adapters require grouped weights of actual compatible histories;
absolute error bounds do not control beliefs when the observation mass also
vanishes. Erasure-independent selection supplies no service contract by itself.
An observation-based scheduler exists exactly when indistinguishable backend
inputs receive the same full command distribution. The checked criterion in
`Interaction.ReactiveSchedulerObservation` quantifies all inputs; its witness
uses a wait command outside the observation image. Existing scheduler
factorization then preserves execution laws for every player policy. Providing
executable choice code and deployed settlement remains a separate task.
The limiting Bayes cross identity retains nonzero timing factors as well as the
zero-product exclusion corollary. Conditional domination and proportional Bayes
transport derive the target mass positivity from their operational premises.
Positive collection needs finitely many complete plans and integrable charges,
not a finite outcome carrier.

[Agreement at decision sites](../GameTheory/GameTheory/Protocol/DecisionPlan.lean)
preserves pure and behavioral continuation laws. With the same history beliefs,
it also preserves terminal sequential equilibrium; decision-plan fallback
choices therefore have no strategic effect. Supported-choice optimality uses
integrability of the incumbent and the particular comparator, retaining the
extended-value treatment of other whole-policy deviations.

Imports expose results; they do not establish that the headline theorem uses
those results. The SE evidence check examines declaration dependencies. New
adapters need actual runtime premises, not hypotheses restating desired
posteriors, comparisons or equilibrium existence.

Protected initialized asynchronous source-law correspondence now includes
concurrent reveals for source profiles satisfying `Disclosing`. The generic
graph frontier and continuation laws use relaxed reveal ordering and actual
profile `ReadyIndependent`; the compiler derives that kernel condition from
disclosure. Sequential and concurrent-binding modes retain arbitrary source
profiles. This is an execution-law result, distinct from SE preservation.
The authentic source audit is clear in these same modes, and the realized
joint initial-state, final-store and net-payoff law holds for arbitrary
authentic audit sampling and deposits. The full unilateral-deviation
source-information and noise factorization remains a separate obligation.
