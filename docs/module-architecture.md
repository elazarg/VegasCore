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
[consistent completion with restricted local laws and a common tremble witness](../GameTheoryExtensions/Analysis/Protocol/RestrictedComponentCompletion.lean),
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
[menus restricted at flagged information values](../GameTheoryExtensions/Protocol/FlaggedMenuRestriction.lean),
[intended game](../Vegas/Source/IntendedGame.lean),
[successful bindings inside arbitrary admission menus](../Vegas/Source/AdmissionRestriction.lean),
[persistent failed-binding obligations](../Vegas/Source/FailedBinding.lean),
[actual value-history representations of unilateral failed-binding deviations](../Vegas/Source/BindingRepairTrace.lean),
[actual continuation kernels against copied value-interface opponents](../Vegas/Source/BindingRepairContinuation.lean),
[value-binding continuation mixtures at actual source information sites](../Vegas/Source/ProtocolValueBindingContinuation.lean),
[intended SE preservation under arbitrary admission](../Vegas/Game/IntendedPreservation.lean),
[the source game with exclusion](../Vegas/Source/ExclusionGame.lean),
[intended SE extension to the exclusion game](../Vegas/Game/ExclusionExtension.lean),
[exclusion SE extension without voluntary failure at nonexcluded sites](../Vegas/Game/ExclusionMoveExtension.lean),
[typed commitment phases and exclusion-preserving rollback](../Vegas/Source/CommitPhaseRecovery.lean),
[the complete source recovery protocol and finite retry budget](../Vegas/Source/CommitRecoveryProtocol.lean),
[its observed transcripts and perfect recall](../Vegas/Source/CommitRecoveryInformation.lean),
[clear recovery source-step laws](../Vegas/Source/CommitRecoveryClear.lean),
[physical attempt namespaces](../Vegas/Pending/AttemptNamespace.lean),
[the all-phase recovery dispatcher](../Vegas/Pending/PhaseApplication.lean),
[its exact saved frontier](../Vegas/Pending/PhaseFrontier.lean),
[maximal phase boundaries and global readiness](../Vegas/Pending/PhaseReadiness.lean),
[finite recovery source menus](../Vegas/Source/CommitRecoveryFiniteness.lean),
[full mixing and all legal recovery source histories](../Vegas/Game/CommitRecoveryReference.lean),
[exact intended recovery source steps](../Vegas/Source/CommitRecoveryIntended.lean),
[actual clear recovery-to-source history projection](../Vegas/Source/CommitRecoveryProjection.lean),
[intended source histories and full recovery information](../Vegas/Game/CommitRecoveryInformationEmbedding.lean),
[their structural action restriction and exact local-step law](../Vegas/Game/CommitRecoveryRestriction.lean),
[consistent source recovery completions and exact initialized laws](../Vegas/Game/CommitRecoveryCompletion.lean),
[typed commitment-block layouts](../Vegas/Compile/CommitPhaseLayout.lean),
[canonical compiled maximal phases](../Vegas/Game/CompiledRuntimePhases.lean),
[accepted-table source attempt decoding](../Vegas/Game/CompiledCommitAttempt.lean),
[actual phase omission provenance](../Vegas/Game/CompiledCommitOmissions.lean),
[completed commitment-block exclusion and typed store](../Vegas/Game/CompiledCommitReadback.lean),
[source attempts reconstructed from actual drained operations](../Vegas/Game/CompiledPhaseReadback.lean),
[inert compiler guard extensions at source reveals](../Vegas/Compile/EventGraphRecoveryReveal.lean),
[phase count menus and zero audited charges](../Vegas/Pending/PhaseCountMenu.lean),
[binding acceptance from actual counted histories](../Vegas/Pending/PhaseBindingService.lean),
[surviving opening handles and actual counted acceptance](../Vegas/Pending/PhaseOpeningAcceptance.lean),
[actual surviving binding namespace stamps](../Vegas/Pending/PhaseBindingStampHistory.lean),
[immutable independently addressed scheduler seeds](../Interaction/ReactiveAddressedScheduler.lean),
[their command-conditioned product posterior](../Interaction/ReactiveAddressedPosterior.lean),
[the concrete erased-query phase calendar](../Vegas/Pending/PhaseSeedCalendar.lean),
[full clocked owner recall for its inputs](../Vegas/Pending/PhaseSeedRecall.lean),
[saved native values through rollback](../Vegas/Pending/PhaseStoredCheckpoint.lean),
[private scheduler memory and exact joint behavioral realization](../Interaction/ReactiveSchedulerImplementation.lean),
[the count verdict on signed traffic](../Vegas/Pending/ReactiveCountVerdict.lean),
[the count audit and persistence of forbidden packets](../Vegas/Pending/ReactiveCountAudit.lean),
[the one-packet menu and its zero count charge](../Vegas/Pending/ReactiveOnePacketMenu.lean),
[one-packet equilibria extended to the effective and raw runtimes](../Vegas/Game/OnePacketExtension.lean),
[actual directed binding and opening trace repair](../Vegas/Game/OnePacketDirectedRepairOpeningTrace.lean),
[whole-history binding repair from intended witnesses](../Vegas/Game/OnePacketBindingRepairWitness.lean),
[finite composition of actual private-binding repairs](../Vegas/Game/OnePacketBindingRepairIteration.lean),
[source-weight comparison along paired actual histories](../Vegas/Game/OnePacketPairedWeight.lean),
[default-runtime SE preservation with exclusion payoff](../Vegas/Game/OnePacketBindingRepairCompilation.lean),
[permanent exclusion and automatic native failure](../Vegas/Pending/ExclusionApplication.lean),
[recovery history invariants](../Vegas/Pending/ExclusionInvariant.lean),
[native projection before exclusion](../Vegas/Pending/ExclusionProjection.lean),
[exact recovery of clear recalled histories](../Vegas/Pending/ExclusionClearLift.lean),
[recovery packet accounting and zero-charge menus](../Vegas/Pending/ExclusionCountMenu.lean),
[clear recovery menu agreement](../Vegas/Pending/ExclusionMenuProjection.lean),
[paired actual environment kernels before exclusion](../Vegas/Pending/ExclusionPairedEnvironment.lean),
[collection of forbidden recovery packets](../Vegas/Pending/ExclusionCountCollection.lean),
[recovery one-packet SE extension to raw menus](../Vegas/Game/RecoveryOnePacketExtension.lean),
[compiled failures retaining source debt](../Vegas/Game/SourceFailureRecord.lean),
[source debt of permanently excluded recovery players](../Vegas/Game/RecoverySourceFailure.lean),
[public reconstruction of permanent exclusion](../Vegas/Pending/ExclusionPublicRecord.lean),
[exact clear-history bijection](../Vegas/Pending/ExclusionClearHistory.lean),
[complete clear information-fiber bijection](../Vegas/Pending/ExclusionInformationHistory.lean),
[per-command probabilities at clear outcomes](../Vegas/Pending/ExclusionClearStepMass.lean),
[actual clear-history reach weights](../Vegas/Pending/ExclusionClearReach.lean),
[bounded pre-exclusion Bayes transport](../Vegas/Pending/ExclusionBoundedBelief.lean),
[actual continuation laws stopped at exclusion](../Vegas/Pending/ExclusionStoppedLaw.lean),
[response-menu embedding of complete stopped laws](../Interaction/ReactiveResponseStopped.lean),
[actual response-menu first-exclusion laws](../Vegas/Pending/ExclusionMenuStopped.lean),
[debt-stopped native payoff comparison](../Vegas/Game/RecoveryDebtStoppedComparison.lean),
[native comparison profiles from recovery completion weights](../Vegas/Game/RecoveryNativeComparison.lean),
[clear regularity before focal source debt](../Vegas/Game/OnePacketClearRegularity.lean),
[canonical first responses excluding later public failure](../Vegas/Game/RecoveryMainResponseSafety.lean),
[total tremble mass outside main support](../Vegas/Game/OnePacketRareMainMass.lean),
[foreign first-activation temporal provenance](../Vegas/Game/OnePacketForeignFreshness.lean),
[actual owner callback recall under recovery opportunity](../Vegas/Pending/ReactiveOwnerActivationRecall.lean),
[fresh commitment calls at clear recovery first activations](../Vegas/Game/RecoveryCommitmentFreshCall.lean),
[prescribed recovery mixtures at forced nonlate decisions](../Vegas/Game/RecoveryPrescribedMixture.lean),
[exact recovery component laws on native optional actions](../Vegas/Game/RecoveryNativeLaw.lean),
[actual native first-exclusion environment boundaries](../Vegas/Pending/ExclusionStoppedBoundary.lean),
[protected recovery binding completion and exact source-step laws](../Vegas/Game/RecoveryStoppedSourceLaw.lean),
[prescribed first-callback source kernels under actual recovery service](../Vegas/Game/RecoveryPrescribedSourceKernel.lean),
[same-weight comparison source values at actual first callbacks](../Vegas/Game/RecoveryComparisonSourceKernel.lean),
[waiting for actual recovery owner callbacks](../Vegas/Game/RecoveryBoundaryWaiting.lean),
[honest callback successor boundaries](../Vegas/Game/RecoverySuccessorBoundary.lean),
[raw recovery chance-phase source laws](../Vegas/Game/RecoveryChanceSourceLaw.lean),
[finite-menu recovery chance stopping](../Vegas/Game/RecoveryChanceStoppedLaw.lean),
[terminal source-prefix continuation laws](../Vegas/Game/RecoveryTerminalSourceLaw.lean),
[decoded failures in existing terminal readouts](../Vegas/Game/SourceServiceFailureReadout.lean),
[honest terminal laws imply intended intermediate states](../Vegas/Game/HonestContinuationIntended.lean),
[full honest recovery source continuations](../Vegas/Game/RecoveryHonestContinuation.lean),
[honest recovery recall at every supported future input](../Vegas/Game/RecoveryHonestRecall.lean),
[honest debt-stopped terminal laws](../Vegas/Game/RecoveryHonestStoppedLaw.lean),
[bounded stopped expectations under honest choice retention](../Vegas/Game/StoppedHonestComparison.lean),
[recovery boundary stopped values](../Vegas/Game/RecoveryStoppedContinuationValue.lean),
[common-weight honest continuation retention](../Vegas/Game/RecoveryComparisonRetention.lean),
[common-weight stopped source continuation values](../Vegas/Game/RecoveryComparisonContinuationValue.lean),
[finite-menu representations of raw stopped values](../Vegas/Game/RecoveryFiniteStoppedValue.lean),
[local-law stopped comparison under the original weights](../Vegas/Game/RecoveryLocalStoppedValue.lean),
[actual raw recovery boundary value bounds](../Vegas/Game/RecoveryComparisonRawValue.lean),
[source belief bounds at all clear debt-free recovery sites](../Vegas/Game/RecoverySourceBeliefBounds.lean),
[event-phase continuation towers](../Vegas/Game/RecoverySourcePhaseValue.lean),
[protected event-phase stopped laws](../Vegas/Game/RecoveryEventPhaseLaw.lean),
[first-activation baseline source value bounds](../Vegas/Game/RecoveryFirstActivationValue.lean),
[local nonlate phase source values](../Vegas/Game/RecoveryNonLateSourceValue.lean),
[legal nonowing transmissions and unpending singleton choices](../Vegas/Game/RecoveryNonLateChoices.lean),
[unchanged local laws at unpending recovery sites](../Vegas/Game/RecoveryUnpendingChoices.lean),
[initialized recovery honest source laws](../Vegas/Game/RecoveryInitializedLaw.lean),
[actual common recovery initialized joint laws](../Vegas/Game/RecoveryInitializedProjection.lean),
[same-witness recovery SE and joint laws from pure local comparisons](../Vegas/Game/RecoverySequentialLimit.lean),
[original pooled recovery member gains from affine keyed values](../Vegas/Game/RecoveryPooledGains.lean),
[actual recovery local values versus same-weight native stopped values](../Vegas/Game/RecoveryLocalValueComparison.lean),
[actual pending binding source factors and unintended own debt](../Vegas/Game/RecoveryLateSourcePhase.lean),
[pending completion potentials and disclosure source values](../Vegas/Game/RecoveryPhasePotential.lean),
[pending physical phase values and bad-support bounds](../Vegas/Game/RecoveryPhaseValueBlind.lean),
[original-posterior common primitive failure scores](../Vegas/Game/RecoveryKeyedFailure.lean),
[actual keyed continuation values under the original posterior](../Vegas/Game/RecoveryKeyedValueBounds.lean),
[uniform component-mixture gain bounds from the original pooled witness](../Vegas/Game/RecoveryPooledMemberGains.lean),
[all nonlate recovery choices versus original source deviations](../Vegas/Game/RecoveryNonLateComparisons.lean),
[intended keyed commitments versus success-weighted source deviations](../Vegas/Game/RecoveryKeyedCommitmentComparisons.lean),
[legal keyed waiting and disclosure choices](../Vegas/Game/RecoveryLatePureChoices.lean),
[exclusion values of unintended commitments](../Vegas/Game/RecoveryUnintendedValue.lean),
[all local recovery comparisons under one common completion](../Vegas/Game/RecoveryLocalComparisons.lean),
[sequential recovery preservation with exact settled joint laws and zero charges](../Vegas/Game/RecoverySequentialCompilation.lean),
[common affine-score pooled ranking](../GameTheoryExtensions/Analysis/Protocol/AffineKeyedPools.lean),
[affine payoff decorrelation bounds](../GameTheoryExtensions/Math/Probability/AffineDecorrelation.lean),
[intended readout and settled-payoff laws through raw recovery extension](../Vegas/Game/RecoveryOnePacketRawLaw.lean),
[terminal public failures and initialized exclusion coupling](../Vegas/Pending/ExclusionTerminalClearance.lean),
[actual pending-event completion](../Vegas/Game/RecoveryPendingCompletion.lean),
[current-event failure under actual recovery completion](../Vegas/Game/RecoveryPendingFailure.lean),
[original common-posterior keyed record bounds](../Vegas/Game/RecoveryKeyedRecords.lean),
[original-seed first binding service logs](../Vegas/Pending/ReactiveSeedBindingService.lean),
[pure clock and slot binding service rules](../Vegas/Pending/ReactiveBindingServiceRule.lean),
[globally legal guarded binding service policies](../Vegas/Pending/ReactiveBindingServicePolicy.lean),
[physical inclusion and expiry binding readouts](../Vegas/Pending/ReactiveSeedBindingReadout.lean),
[typed binding outcomes under actual service policies](../Vegas/Pending/ReactiveSeedBindingOutcome.lean),
[same-seed binding outputs at actual Bayes information sites](../Vegas/Pending/ReactiveSeedBindingSiteOutcome.lean),
[recovery gains versus concrete native debt-stopped gains](../Vegas/Game/RecoveryValueTransport.lean),
[one source policy for each intended native commitment](../Vegas/Game/OnePacketCommitmentSourcePolicy.lean),
[same-weight native comparison at actual clear decisions](../Vegas/Game/RecoveryNativeStrategy.lean),
[common recovery and comparison full-history beliefs](../Vegas/Game/RecoveryComparisonBelief.lean),
[complete finite comparison information histories](../Vegas/Game/RecoveryComparisonInformation.lean),
[complete comparison fibers at all clear forced debt-free sites](../Vegas/Game/RecoveryComparisonSite.lean),
[actual recovery prefix posterior bounds](../Vegas/Game/RecoveryPrefixBeliefBounds.lean),
[same-opponent stopped laws under arbitrary focal policies](../Vegas/Game/RecoveryComparisonStopped.lean),
[foreign first-exit rank bounds before focal debt](../Vegas/Game/RecoveryForeignFailureBound.lean),
[foreign first-exit bounds averaged over history beliefs](../Vegas/Game/RecoveryForeignExitBeliefBound.lean),
[actual recovery continuation rank bounds](../Vegas/Game/RecoveryContinuationComparison.lean),
[uniform irregular-history bounds for the common recovery beliefs](../Vegas/Game/RecoveryIrregularBeliefBounds.lean),
[belief-averaged recovery payoff error](../Vegas/Game/RecoveryBeliefContinuation.lean),
[uniformly vanishing actual recovery foreign exits](../Vegas/Game/RecoveryForeignExitBounds.lean),
[vanishing recovery continuation payoff error](../Vegas/Game/RecoveryContinuationLimit.lean),
[clear comparison reach weights and Bayes normalization](../Vegas/Game/RecoveryNativeClearBelief.lean),
[future non-main callbacks behind actual first foreign failures](../Vegas/Game/RecoveryForeignFailure.lean),
[full-state filtered local seed products at clear recovery sites](../Vegas/Pending/ExclusionLocalSeedProduct.lean),
[complete finite clear information-fiber projection](../Vegas/Pending/ExclusionBoundedInformationHistory.lean),
[focal policy updates under clear menu projection](../Vegas/Pending/ExclusionPolicyDeviation.lean),
[original seed products through physical recovery continuation](../Vegas/Pending/ExclusionSeedContinuation.lean),
[actual first-failure command classification](../Vegas/Game/OnePacketCompletionOrigin.lean),
[full clear recovery control and original seed Bayes laws](../Vegas/Pending/ExclusionSeedBelief.lean),
[seed posteriors through recovery scheduler lifting](../Vegas/Pending/ExclusionSchedulerSeed.lean),
[complete-control Bayes projection at clear recovery sites](../Vegas/Pending/ExclusionBoundedStateBelief.lean),
[original immutable seeds at actual command occupations](../Interaction/ReactiveSchedulerSeedOccupation.lean),
[continuation error bounded by exclusion probability](../Vegas/Pending/ExclusionContinuationLaw.lean),
[continuation error from foreign first exclusions only](../Vegas/Game/RecoveryForeignExitBound.lean),
[native stopped payoff comparison for finite recovery menus](../Vegas/Game/RecoveryForeignExitComparison.lean),
[completion of actual recovery executions](../Vegas/Pending/ExclusionService.lean),
[fixed utility after permanent exclusion](../Vegas/Game/RecoveryExclusionPayoff.lean),
[latent source debt through recovery continuations](../Vegas/Game/RecoveryDecodedDebt.lean),
[whole-policy indifference after recovery debt](../Vegas/Game/RecoveryIndifference.lean),
[uniform own debt on complete recovery information fibers](../Vegas/Game/RecoveryDebtUniformity.lean),
[whole-policy rationality at owing recovery agents](../Vegas/Game/RecoveryOwingOptimality.lean),
[protected canonical calls through first exclusion](../Vegas/Game/RecoveryCanonicalSafety.lean),
[actual recovery base-payoff continuation laws](../Vegas/Game/RecoveryContinuationPayoff.lean),
[includability of count-permitted commitments](../Vegas/Pending/ReactiveCountedBindingService.lean),
[includability of authentic count-permitted openings](../Vegas/Pending/ReactiveCountedOpeningAcceptance.lean),
[stopped laws from paired actual kernels](../GameTheoryExtensions/Analysis/Protocol/StoppedKernelComparison.lean),
[unread scheduler-seed independence](../Interaction/ReactiveSchedulerFreshSeed.lean),
[actual event-local scheduler inputs](../Vegas/Pending/ReactiveLocalSeedInput.lean),
[scoped local seed controller and its operational domain](../Vegas/Pending/ReactiveLocalSeedScheduler.lean),
[actual execution-prefix splicing for local seeds](../Vegas/Pending/ReactiveLocalSeedRun.lean),
[immutable-seed replay with full private query logs](../Vegas/Pending/ReactiveLocalSeedReplay.lean),
[actual transcript/log conditioning](../Vegas/Pending/ReactiveLocalSeedPosteriorLog.lean),
[owner reconstruction of positive local queries](../Vegas/Pending/ReactiveLocalSeedOwnerRun.lean),
[actual clean ready-owner seed posteriors](../Vegas/Pending/ReactiveCountedSeedPosterior.lean),
[full owner-observation seed product laws](../Vegas/Pending/ReactiveCountedSeedObservation.lean),
[standard Bayes beliefs as command-boundary occupation posteriors](../Interaction/ReactiveOccupationPosterior.lean),
[original immutable seeds at command-boundary controls](../Vegas/Pending/ReactiveSeedOccupation.lean),
[original immutable seeds under actual finite-site Bayes beliefs](../Vegas/Pending/ReactiveSeedBayes.lean),
[actual Bayes-site responses and original-seed first resolution](../Vegas/Pending/ReactiveSeedCompletion.lean),
[locally filtered seed products at native information sites](../Vegas/Pending/ReactiveSeedBayesProduct.lean),
[conditioning deterministic observations with their sampled values](../GameTheoryExtensions/Math/Probability/TaggedPosterior.lean),
[value-only SE preservation under arbitrary admission](../Vegas/Game/ValueAdmissionPreservation.lean),
[initialized private-intention uniqueness and restoration](../Vegas/Pending/ReactivePosteriorUniqueness.lean),
[accepted original intentions in initialized executions](../Vegas/Pending/ReactiveAcceptedIntentionRecall.lean),
[original-action configurations and actual sampler laws](../Vegas/Pending/ReactiveOriginalConfig.lean),
[actual focal graph observations](../Vegas/Pending/ReactiveDeviationObservation.lean),
[accepted focal packets and reconstructed graph completion](../Vegas/Pending/ReactiveDeviationInclusion.lean),
[native focal expiry and reconstructed graph steps](../Vegas/Pending/ReactiveDeviationCompletion.lean),
[raw unilateral callbacks and mixed foreign-frontier replay](../Vegas/Pending/ReactiveDeviationRecall.lean),
[opaque binding responses and foreign activation inputs](../Vegas/Pending/ReactiveBindingNoise.lean),
[foreign original source recall through raw callbacks](../Vegas/Game/ReactiveSourceForeignRecall.lean),
[original-action retention through actual responses](../Vegas/Pending/ReactiveOriginalResponseStability.lean),
[original-action retention through actual packet inclusion](../Vegas/Pending/ReactiveOriginalInclusionStability.lean),
[fresh sampled events outside retained intention frontiers](../Vegas/Pending/ReactiveSampledFrontierFreshness.lean),
[owner-authenticated joint intention frontiers](../Vegas/Pending/ReactiveSampledFrontierOwnership.lean),
[shared reachability, output and ordered recall relations](../Vegas/Pending/ReactiveRetainedFrontier.lean),
[frontiers retaining arbitrary focal physical completions](../Vegas/Pending/ReactiveUnilateralFrontier.lean),
[arbitrary focal inclusion](../Vegas/Pending/ReactiveUnilateralInclusion.lean),
[mixed chance draws and environment steps](../Vegas/Pending/ReactiveUnilateralEnvironment.lean),
[actual focal expiry](../Vegas/Pending/ReactiveUnilateralExpiry.lean),
[foreign prescribed sampling with arbitrary focal traffic](../Vegas/Pending/ReactiveUnilateralSampling.lean),
[authenticated foreign and focal pending settlement](../Vegas/Pending/ReactiveUnilateralSettlement.lean),
[retained silent foreign expiry](../Vegas/Pending/ReactiveUnilateralSilentExpiry.lean),
[actual focal source observations under public barriers](../Vegas/Pending/ReactiveUnilateralObservation.lean),
[accepted events' authenticated ownership](../Vegas/Pending/AcceptedEventOwnership.lean),
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
[marginal transport through an approximate product factorization](../GameTheoryExtensions/Math/Probability/ProductTransport.lean),
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
[uniform raw response kernels under label permutations](../Vegas/Examples/LateOpeningRuntimeLabelKernels.lean),
[actual label-symmetric history laws and reach weights](../Vegas/Examples/LateOpeningRuntimeLabelReach.lean),
[uniform conditional label beliefs through Bayes limits](../Vegas/Examples/LateOpeningRuntimeLabelBeliefs.lean),
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
policy using genuine absence of further activation. Unrestricted exact off-path
source-value correspondence is refuted by the late-callback result below.
Protected first-opportunity correspondence and domination against arbitrary
whole continuation policies remain separate obligations.
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

Full-support prescribed decision laws can be retained exactly at every
approximant of the consistent whole-player completion, as well as at the limit.
The native uniform raw Alice policy therefore supports genuine Bayes reference
beliefs with a uniform conditional label marginal at every Bob information site,
including sites unreached by the limit strategy. This requires the checked
uniform Alice laws; arbitrary consistency witnesses are not assumed symmetric.

Recovery source-value correspondence needs a physical settlement opportunity.
A legal final activation can leave zero environment rounds, in which case the
actual response preserves the physical store and every authored action has the
same native store-based value. This is a necessary boundary for general raw
callbacks, not a counterexample under the protected completion contract.

The native `exists_uniform_alice_bob_completion` constructs the Bob reference
assessment: Alice's uniform raw decision laws remain fixed in a fully mixed
Bayes sequence and its consistent limit, Bob is rational against every whole
continuation policy at every legal information fiber, and his label beliefs
are uniform at every fiber. The reference assessment has actual-positive Bayes
beliefs. This does not make uniform Alice rational or establish the selected
source law; transferring Bob's continuation to the later Alice completion and
assembling the weak PBE remain separate obligations.

[Bob tail continuation transfer](../Vegas/Examples/LateOpeningRuntimeBobTail.lean)
derives that every legal Bob information fiber with public clock at least three
is after Alice's last activation. The complete terminal-history law and
whole-policy rationality are invariant under changing Alice's future policy,
while retaining Bob's original beliefs and decision laws. This does not cover
the clock-one binding callback or transport consistency or Bayes beliefs.
[Protected Bob binding and opening](../Vegas/Examples/LateOpeningRuntimeProtectedBobPrefix.lean)
retains the whole graph configuration and clean binding traffic across arbitrary
intervening Alice responses, and reaches an accepted opening of the same typed
answer at clock three.
[Canonical Bob terminal continuations](../Vegas/Examples/LateOpeningRuntimeProtectedBobContinuation.lean)
derive final publication of that answer and zero Bob audit charge for arbitrary
authentic sampling and arbitrary Alice future policies. On a successful Alice
branch the Safe comparator attains exactly `2/5`, with no payoff-parameter
restrictions.
[Early binding activation](../Vegas/Examples/LateOpeningRuntimeProtectedBobTiming.lean)
derives timestamp zero at the genuine initialized ready Bob callback. Whole-policy
optimality and first-response selection remain separate obligations.

The native `exists_uniform_bob_reference` additionally forces pure silence at
every unresolved first Bob callback under full audit, nonnegative source
forfeit and Bob deposit greater than one. This uses local whole-policy
optimality, without assuming Alice rationality. Protected-ready early optimality,
the initialized selected source law and the weak-PBE assembly remain separate.

[Late-callback recovery values](../Vegas/Examples/LateOpeningRuntimeRecoveryValue.lean)
refute unrestricted exact off-path source-value correspondence in the unchanged
native service. At a genuine legal, ready, timely late Alice callback, the literal
compiled proper opening against SafeBob has value
`q*(R/2) - (1-q)*(D+K_A)`, strictly below the actual successful-opening source
run's `R/2` when `R>0` and `D+K_A>=0`, where `D` is the source forfeit.
The protected first-opportunity value
adapter and optimality against arbitrary whole continuation policies remain
separate obligations; the one-response comparison retains its explicit value
correspondence hypothesis.

[Native canonical Bob decisions](../Vegas/Examples/LateOpeningRuntimeProtectedBobPolicy.lean)
instantiate the existing source-canonical policy: a genuine fresh ready binding
selects its typed answer, a ready opening discloses TRUE, and completion of both
Bob events forces silence. This includes another callback at the same clock,
without emitting a second opening identifier. Binding readiness supplies the
source observation decoder's publication requirement. These policy identities
introduce no runtime model and do not assert full terminal audit cleanliness,
optimality or weak PBE.

[Raw response binding posteriors](../Vegas/Pending/ReactiveBindingResponseNoise.lean)
extend the existing opaque-binding activation law through an arbitrary observer
raw policy. At a fixed actual prefix, a foreign private binding draw is
independent of the full next activation input and chosen raw response. Its
posterior conditional on both equals the original draw law, including the
owning posterior's total fallback at impossible observations. This assumes no
desired noise law and permits arbitrary leak rules; it does not establish a
whole-phase or initialized unilateral source-information/noise factorization.

`ReactiveRetainedFrontier` owns the common reachable configuration, input,
completed-domain, output agreement and ordered recall relation. The prescribed
frontier adds equality with every owner's sampled intention list. The unilateral
frontier instead retains the focal player's actual physical completions and an
empty auxiliary focal intention list; it imposes no prescribed focal raw policy.
The shared pending-owner suffix proof requires consistency and posterior support
only from owners with a retained intention. Fresh-event foreignness needs only
the current prescribed owner's consistency and support. The original initialized
joint source-store, audit and realized-net-payoff capstones retain their scope.

Public-barrier foreign completion preserves the entire normalized observation,
which supplies the existing policy-kernel commutation by applying the policy.
The same observation equality lifts through actual foreign completion replay
and the unilateral frontier to the focal physical source observation. The
observation adapter explicitly requires `BarrierOrdered`; arbitrary focal raw
deviations in concurrent reveal graphs need a separate information argument.
Actual mixed sampling, chance, inclusion and expiry branches are checked, with
their stated provenance, posterior and retained-silent-opportunity hypotheses.
[Foreign author conformance](../Vegas/Pending/ReactiveTimelyCalls.lean)
is owner-local and its invariant follows from actual policies only at the
selected owners. An arbitrary focal raw policy imposes no conformance obligation
on that owner. Existing all-prescribed source-store, audit and net-payoff laws
retain their conclusions.
[Mixed callbacks](../Vegas/Pending/ReactiveUnilateralCallback.lean),
[complete native commands](../Vegas/Pending/ReactiveUnilateralCommands.lean),
[source-service expiry](../Vegas/Game/SourceServiceUnilateralExpiry.lean),
[environment dispatch](../Vegas/Game/SourceServiceUnilateralEnvironment.lean) and
[whole rounds](../Vegas/Game/SourceServiceUnilateralRound.lean) feed
[initialized unilateral execution](../Vegas/Game/SourceServiceUnilateralExecution.lean).
Every supported bounded prefix admits a reachable mixed frontier for every
compatible foreign posterior memory, under actual opportunity, timely deadline
and protected-inclusion guarantees. This operational support theorem covers
every source-service mode and retains arbitrary focal raw policies.
[Public source decisions](../Vegas/Game/ReactiveSourcePublicCheckpoint.lean)
derive a genuine source observation and its exact decision encoding from the
actual frontier at public ready events in `toEventGraph`, with explicit compiler
reference coverage hypotheses. Private-binding chronology and the full
conditional source-information/noise law remain separate obligations.

[Actual silent recovery continuations](../Vegas/Examples/LateOpeningRuntimeRecoveryDomination.lean)
derive the native silent payoff law `pure(-D)` at the same genuine legal, ready,
timely late callback used by the opening-value obstruction. Absence of authored
Alice traffic supplies audit charge zero; the actual clock-three Safe Bob
continuation supplies publication. Under full audit, the literal compiled TRUE
opening loses to silence if `K_A > weight*(R/2+D)`, while source TRUE beats FALSE
if `R/2+D>0`. Every fixed positive `K_A` admits a positive service weight chosen
afterward with this reversal, uniformly over all remaining Alice policies and
initial bits and labels. This is a local action-value obstruction; protected
first-opportunity correspondence and whole-policy recovery remain open.

[Canonical Bob menu admissibility](../Vegas/Examples/LateOpeningRuntimeProtectedBobMenu.lean)
represents every existing source-canonical Bob profile as a whole bounded raw
policy, including failed bindings and arbitrary earlier traffic.
[Whole Bob continuation ceilings](../Vegas/Examples/LateOpeningRuntimeLabelContinuation.lean)
derive the full terminal-history orbit law for every whole Bob alternative from
the coherent fully mixed Bayes sequence retaining uniform Alice. A finite
successful-publication summary gives gross payoff at most `2/5`. The public
successful Alice cell transfers across every legal Bob information fiber and
persists through actual terminal continuations. Nonnegative source forfeit and
Bob deposit give actual audited context value at most `2/5` for every whole Bob
alternative, under arbitrary audit sampling. This bound is distinct from the
Safe attainment theorem; first-binding selection and weak-PBE assembly remain
open.
