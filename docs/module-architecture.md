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
[whole deviations restricted to actual public-exclusion sites](../Vegas/Game/PhasePublicCompletion.lean),
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
[normalized live phases and actual owner or sample progress](../Vegas/Pending/PhaseLive.lean),
[strict phase progress of actual singleton samples](../Vegas/Pending/PhaseSampleProgress.lean),
[maximal phase boundaries and global readiness](../Vegas/Pending/PhaseReadiness.lean),
[finite recovery source menus](../Vegas/Source/CommitRecoveryFiniteness.lean),
[full mixing and all legal recovery source histories](../Vegas/Game/CommitRecoveryReference.lean),
[uniform source reference laws determined by static position and exclusion](../Vegas/Game/CommitRecoveryReferencePosition.lean),
[actual auxiliary prefix reconstruction and full next-move conditioning](../Vegas/Game/CommitRecoveryPrefixConditioning.lean),
[exact source omission laws independent of hidden values at each address](../Vegas/Game/CommitRecoveryOmissionPosition.lean),
[exact intended recovery source steps](../Vegas/Source/CommitRecoveryIntended.lean),
[actual clear recovery-to-source history projection](../Vegas/Source/CommitRecoveryProjection.lean),
[intended source histories and full recovery information](../Vegas/Game/CommitRecoveryInformationEmbedding.lean),
[complete information along arbitrary clear source histories](../Vegas/Source/CommitRecoveryClearRecall.lean),
[actual clear information at intended source views](../Vegas/Game/CommitRecoveryClearInformation.lean),
[complete auxiliary information at every realized clear source view](../Vegas/Game/CommitRecoveryClearDecoder.lean),
[their complete clear source fibers and common depth](../Vegas/Game/CommitRecoveryClearFiber.lean),
[actual auxiliary Bayes beliefs as source-run passage laws](../Vegas/Game/CommitRecoveryClearBayes.lean),
[initialized intended-source histories or persistent departure debt](../Vegas/Game/SourceIntendedTrace.lean),
[their structural action restriction and exact local-step law](../Vegas/Game/CommitRecoveryRestriction.lean),
[consistent source recovery completions and exact initialized laws](../Vegas/Game/CommitRecoveryCompletion.lean),
[checkpointed source debt through every recovery reset](../Vegas/Source/CommitRecoveryDebt.lean),
[actual processed failure coverage and terminal exclusion](../Vegas/Source/CommitRecoveryFailureCoverage.lean),
[actual exclusion payoffs and exact intended joint laws](../Vegas/Game/CommitRecoveryPayoff.lean),
[checkpointed debt forcing the actual terminal payoff floor](../Vegas/Game/CommitRecoveryDebtPayoff.lean),
[hidden commitment-block information retained through closure](../Vegas/Game/CommitRecoveryHiddenInformation.lean),
[extra source recovery actions forcing the actual payoff floor](../Vegas/Game/CommitRecoveryDeviationPayoff.lean),
[intended SE extended to the auxiliary rollback source game](../Vegas/Game/CommitRecoveryPreservation.lean),
[source rollback menus without voluntary omission or withholding](../Vegas/Source/CommitRecoveryContinuingMenu.lean),
[actual permanent exclusion after source omission or withholding](../Vegas/Source/CommitRecoveryVoluntaryFailure.lean),
[their exact continuation payoff and global terminal floor](../Vegas/Game/CommitRecoveryVoluntaryFailurePayoff.lean),
[auxiliary rollback SE without omissions or withheld openings at any site](../Vegas/Game/CommitRecoveryContinuingExtension.lean),
[exact source voluntary-failure laws and uniform tremble bounds](../Vegas/Game/CommitRecoveryContinuingProbability.lean),
[uniform silence bounds at actual clear native binding callbacks](../Vegas/Game/PhaseBindingSilenceProbability.lean),
[typed commitment-block layouts](../Vegas/Compile/CommitPhaseLayout.lean),
[canonical compiled maximal phases](../Vegas/Game/CompiledRuntimePhases.lean),
[accepted-table source attempt decoding](../Vegas/Game/CompiledCommitAttempt.lean),
[actual phase omission provenance](../Vegas/Game/CompiledCommitOmissions.lean),
[completed commitment-block exclusion and typed store](../Vegas/Game/CompiledCommitReadback.lean),
[source attempts reconstructed from actual drained operations](../Vegas/Game/CompiledPhaseReadback.lean),
[clean, retry and exhausted physical commitment closures](../Vegas/Game/CompiledCommitClosing.lean),
[syntax-derived compiled residuals and exact recovery lifts](../Vegas/Game/CompiledRecoveryResidual.lean),
[exact maximal commitment phase identification](../Vegas/Game/CompiledCommitMaximality.lean),
[actual remaining-plan suffix and inherited geometry](../Vegas/Pending/PhasePlanSuffix.lean),
[canonical terminal references along compiler traversal](../Vegas/Compile/CompiledReadoutSuffix.lean),
[typed-attempt compiler tail certificates](../Vegas/Game/CompiledCommitTail.lean),
[canonical source-view and named-action suffix certificates](../Vegas/Compile/ProtocolViewSuffix.lean),
[their source disclosure-telescope composition](../Vegas/Game/CompiledViewTail.lean),
[typed commitment-prefix splits](../Vegas/Source/CommitPrefixSplitting.lean),
[original dependent commitment-prefix laws and full-view conditioning](../Vegas/Source/CommitPrefixLaw.lean),
[foreign-profile-independent focal views and exact next-binding posterior kernels](../Vegas/Source/CommitPrefixInformationLaw.lean),
[legal unclosed source commitment paths](../Vegas/Source/CommitRecoveryPrefixPath.lean),
[typed prefix completion from partial native stores](../Vegas/Compile/CommitPrefixCompletion.lean),
[own admitted choices reflected through commitment predecessors](../Vegas/Source/IntendedCommitPredecessor.lean),
[intended hidden-foreign prefix completion retaining the full focal view](../Vegas/Compile/CommitPrefixIntendedCompletion.lean),
[exact source views at partial commitment prefixes](../Vegas/Compile/CommitPrefixView.lean),
[visible prefix availability from actual graph readiness](../Vegas/Game/CompiledCommitPartialView.lean),
[exact typed prefix own-action words](../Vegas/Game/CommitPrefixFillRecall.lean),
[actual initialized source witnesses at partial binding cuts](../Vegas/Game/RecoveryCommitPrefixWitness.lean),
[chronological native checkpoint history through rollback](../Vegas/Pending/PhaseHistoryCheckpoint.lean),
[canonical dependent binding-completion records](../Vegas/Game/CommitAttemptHistory.lean),
[source-ranked same-owner recall in relaxed graphs](../Vegas/EventGraph/RelaxedRecall.lean),
[exact physical versus canonical owned records](../Vegas/Game/CommitAttemptRecall.lean),
[complete typed recall through clear commitment phases](../Vegas/Game/CommitAttemptOwnRecall.lean),
[source words certified by actual ranked completion records](../Vegas/Game/RecordedSourceHistory.lean),
[typed prefixes selected by actual binding layouts](../Vegas/Compile/CommitPrefixAtEvent.lean),
[ready-prefix action alignment](../Vegas/Game/CommitPrefixReadyRecall.lean),
[actual ready-binding source traces](../Vegas/Game/RecoveryReadyCommitWitness.lean),
[physical source-view and clear decision information](../Vegas/Game/RecoveryReadyCommitInformation.lean),
[complete played information at ready binding checkpoints](../Vegas/Game/RecoveryBindingCounterpart.lean),
[initialized native binding counterparts without supplied checkpoints](../Vegas/Game/PhaseBindingCounterpart.lean),
[actual ready-binding source Bayes prefix laws](../Vegas/Game/PhaseBindingBayesPrefix.lean),
[reachable saved source checkpoints](../Vegas/Game/RecoverySourceCheckpoint.lean),
[their actual current terminal readback](../Vegas/Game/RecoverySourceReadout.lean),
[legal whole-source lifted commitment closures](../Vegas/Source/CommitRecoveryBlockCloseLift.lean),
[actual initialized source checkpoints](../Vegas/Game/RecoveryInitialCheckpoint.lean),
[all-phase source checkpoint normalization](../Vegas/Game/RecoveryCheckpointNormalization.lean),
[reachable saved source checkpoints at every initialized history](../Vegas/Game/RecoveryCheckpointHistory.lean),
[completed reveal checkpoint transitions](../Vegas/Game/RecoveryRevealCheckpoint.lean),
[completed sample checkpoint transitions](../Vegas/Game/RecoverySampleCheckpoint.lean),
[actual retry checkpoints](../Vegas/Game/RecoveryCommitCheckpoint.lean),
[clean and exhausted commitment checkpoints](../Vegas/Game/RecoverySettledCommitCheckpoint.lean),
[actual terminal source-history and payoff-vector correspondence](../Vegas/Game/RecoverySourceTerminal.lean),
[actual saved and live commitment-block frontiers](../Vegas/Source/CommitRecoveryFrontier.lean),
[typed attempts as legal whole-source recovery paths](../Vegas/Source/CommitRecoveryBlockPath.lean),
[exact typed clean, retry and exhausted source closure paths](../Vegas/Source/CommitRecoveryBlockClose.lean),
[legal noncommit paths and their whole-source lifting](../Vegas/Source/CommitRecoveryPathLift.lean),
[actual completed reveal boundary readback and legal source paths](../Vegas/Game/CompiledRevealCompletion.lean),
[actual chance-sample readback and legal source steps](../Vegas/Game/CompiledSampleCompletion.lean),
[inert compiler guard extensions at source reveals](../Vegas/Compile/EventGraphRecoveryReveal.lean),
[phase count menus and zero audited charges](../Vegas/Pending/PhaseCountMenu.lean),
[binding acceptance from actual counted histories](../Vegas/Pending/PhaseBindingService.lean),
[surviving opening handles and actual counted acceptance](../Vegas/Pending/PhaseOpeningAcceptance.lean),
[globally fresh prepared slots at actual histories](../Vegas/Pending/PhaseCandidateSupply.lean),
[bounded raw representation of typed binding laws](../Vegas/Pending/PhasePreparedBinding.lean),
[their actual unsent one-packet encodings](../Vegas/Pending/PhasePreparedOnePacket.lean),
[globally legal guarded source binding policies](../Vegas/Game/PhaseSourceBindingPolicy.lean),
[whole physical source-policy dispatch and finite strategy representation](../Vegas/Game/PhaseSourcePolicy.lean),
[exact dispatched binding and canonical-opening laws](../Vegas/Game/PhaseSourcePolicyLaw.lean),
[dispatched bindings at genuinely played source information](../Vegas/Game/PhaseSourcePolicyInformation.lean),
[joint source-result/omission laws with independent fresh slots](../Vegas/Game/PhaseRecoverySlotComponent.lean),
[their actual unsent-history slot supply](../Vegas/Game/PhaseRecoverySlotHistory.lean),
[whole recovery slot dispatch and finite strategy representation](../Vegas/Game/PhaseSourceSlotPolicy.lean),
[actual slot-dispatch binding and opening laws](../Vegas/Game/PhaseSourceSlotPolicyLaw.lean),
[slot-dispatch laws at complete played source information](../Vegas/Game/PhaseSourceSlotInformation.lean),
[independent raw-noise and slot perturbation rates](../Vegas/Game/PhaseSourcePerturbation.lean),
[positive original source masses and fixed-capacity canonical replacement bounds](../Vegas/Game/PhaseBindingReplacementMass.lean),
[one native consistent assessment with clear recipes and optimal public-exclusion continuations](../Vegas/Game/PhaseAssessmentCompletion.lean),
[exact common typed-response laws under independent slot and raw perturbations](../Vegas/Game/PhaseSourceResponseLaw.lean),
[source joint response laws at the same native assessment limit](../Vegas/Game/PhaseSourceResponseLimit.lean),
[full canonical physical binding and opening strategies at that same limit](../Vegas/Game/PhaseSourceStrategyLimit.lean),
[globally legal source-value-preserving fresh-slot laws](../Vegas/Pending/PhaseBindingSlotPolicy.lean),
[all bounded fresh slots offered at actual binding sites](../Vegas/Pending/PhaseBindingSlotHistory.lean),
[global fresh-handle provenance for permitted raw bindings](../Vegas/Pending/PhaseBindingFreshness.lean),
[raw binding handles covered by the slot law with a fixed mass denominator](../Vegas/Pending/PhaseBindingSlotSupport.lean),
[syntax-directed complete source views at partial cuts](../Vegas/Game/PhaseEventSourceView.lean),
[auxiliary source-choice binding components with omission flags](../Vegas/Game/PhaseRecoveryBindingComponent.lean),
[every typed compiled binding result admitted at its decoded source address](../Vegas/Compile/EventSourceBindingChoice.lean),
[actual fully mixed source support for every typed binding result](../Vegas/Game/PhaseRecoveryBindingChoice.lean),
[actual bounded saved and live handles](../Vegas/Pending/PhaseBoundedHandles.lean),
[authentic finite-menu opening coverage](../Vegas/Pending/PhaseOpeningCoverage.lean),
[globally legal local disclosure laws](../Vegas/Pending/PhaseOpeningPolicy.lean),
[first-response persistence including silence](../Vegas/Pending/PhaseOncePolicy.lean),
[same-attempt authentic origins of completed owned events](../Vegas/Pending/PhaseCompletionStampHistory.lean),
[authentic current-token prerequisite retention](../Vegas/Pending/PhaseCurrentTokens.lean),
[counted surviving packets remaining pending](../Vegas/Pending/PhaseCountedSurvivor.lean),
[source-ordered publication failure suppression](../Vegas/Pending/PhaseFailureOrder.lean),
[its actual history and pre-retirement drained endpoints](../Vegas/Pending/PhaseFailureOrderHistory.lean),
[activation origins through physical rollback](../Vegas/Pending/PhaseActivationOrigin.lean),
[current-clock activation origins across retries](../Vegas/Pending/PhaseRetryClock.lean),
[phase count-audit coverage and permanent forbidden evidence](../Vegas/Pending/PhaseCountCollection.lean),
[counted-menu SE extended to the actual bounded raw menu](../Vegas/Game/PhaseOnePacketExtension.lean),
[actual excluded-player full-fiber continuation optimality](../Vegas/Game/PhaseExcludedRationality.lean),
[raw typed-readout and realized audited payoff-vector laws](../Vegas/Game/PhaseRawReadoutLaw.lean),
[actual surviving binding namespace stamps](../Vegas/Pending/PhaseBindingStampHistory.lean),
[immutable independently addressed scheduler seeds](../Interaction/ReactiveAddressedScheduler.lean),
[their command-conditioned product posterior](../Interaction/ReactiveAddressedPosterior.lean),
[the concrete erased-query phase calendar](../Vegas/Pending/PhaseSeedCalendar.lean),
[its actual finite-ticket clock accounting](../Vegas/Pending/PhaseSeedClockAccounting.lean),
[a uniform clock bound at every legal initialized history](../Vegas/Pending/PhaseSeedClockBound.lean),
[finite calendar completion for arbitrary raw responses](../Vegas/Pending/PhaseSeedHorizon.lean),
[completion under the original-seed posterior mixture](../Vegas/Pending/PhaseSeedMixtureHorizon.lean),
[erased pre-activation queries from actual owner information](../Vegas/Pending/PhaseSeedInformationInput.lean),
[their actual active-history reconstruction](../Vegas/Pending/PhaseSeedHistoryInput.lean),
[all-history elapsed-tick query exhaustion](../Vegas/Pending/PhaseSeedTickExhaustion.lean),
[permanent resolution of physical attempt coordinates](../Vegas/Pending/PhaseResolutionPersistence.lean),
[historical nonactivation replies for surviving requests](../Vegas/Pending/PhaseSeedSurvivalReply.lean),
[all-candidate coin invariance at actual unsent information](../Vegas/Pending/PhaseSeedUnsentInformation.lean),
[exact unsent original-seed constraints across the whole owner fiber](../Vegas/Pending/PhaseSeedUnsentFiber.lean),
[original-prior coordinate posterior factorization](../Interaction/ReactiveAddressedCoordinatePosterior.lean),
[unsent local seed products under actual scheduler controls](../Vegas/Pending/PhaseSeedUnsentPosterior.lean),
[the complete unsent native Bayes product](../Vegas/Pending/PhaseSeedUnsentBayes.lean),
[the original delay at actual first callbacks](../Vegas/Pending/PhaseSeedFirstCallback.lean),
[protected first inputs under the actual finite Bayes law](../Vegas/Pending/PhaseSeedFirstBayes.lean),
[semantic source-view constancy while a binding waits](../Vegas/Game/PhaseWaitingSourceView.lean),
[ready-event semantic stability under immutable extension](../Vegas/EventGraph/ReadySemanticStability.lean),
[actual phased immutable semantic extension](../Vegas/Pending/PhaseSemanticProgress.lean),
[ready requests retained or permanently resolved](../Vegas/Pending/PhaseRequestProgress.lean),
[raw owned-event command frames](../Vegas/Pending/EventCommandFrame.lean),
[foreign physical binding isolation](../Vegas/Pending/PhaseSeedPhysicalIsolation.lean),
[physical environment request isolation](../Vegas/Pending/PhaseEnvironmentIsolation.lean),
[actual request-loss inclusion and expiry witnesses](../Vegas/Pending/PhaseReadyResolution.lean),
[the original protection-or-coin inclusion window](../Vegas/Pending/PhaseSeedResolutionWindow.lean),
[immutable timed emission words through future rounds](../Vegas/Pending/PhaseSeedEmissionPersistence.lean),
[earlier emissions constrained by actual later wait replies](../Vegas/Pending/PhaseSeedWaitingWindow.lean),
[protected surviving requests at the original clock](../Vegas/Pending/PhaseSeedProtectedClock.lean),
[derived callback tick openness and protected first-loss inclusion](../Vegas/Pending/PhaseSeedProtectedResolution.lean),
[first environment loss along the existing finite round evaluator](../Interaction/ReactiveRoundBoundary.lean),
[unique complete permitted packets at physical event addresses](../Vegas/Pending/PhaseCountUniqueness.lean),
[eventual accepting receipts for original protected envelopes](../Vegas/Pending/PhaseSeedProtectedReceipt.lean),
[original favorable ticks bounding surviving physical request time](../Vegas/Pending/PhaseSeedServiceTick.lean),
[actual predeadline request losses by accepting inclusion](../Vegas/Pending/PhaseTimelyResolution.lean),
[original coin-window attainment with the same supported continuation](../Vegas/Pending/PhaseSeedWindowReceipt.lean),
[unique original coordinate emission words](../Vegas/Pending/PhaseSeedEmissionUnique.lean),
[original inclusion windows required by actual selected inclusion](../Vegas/Pending/PhaseSeedWindowNecessary.lean),
[first new accepting receipts along finite physical continuations](../Interaction/ReactiveReceiptBoundary.lean),
[exact original-window receipt equivalence and Boolean continuation law](../Vegas/Pending/PhaseSeedWindowEquivalence.lean),
[actual coordinate emission-time bounds](../Vegas/Pending/PhaseSeedEmissionTimes.lean),
[immediate-send window upper bounds for arbitrary later adaptive sending](../Vegas/Pending/PhaseSeedAdaptiveWindow.lean),
[original local-prior window marginals under the actual owner Bayes law](../Vegas/Pending/PhaseSeedWindowBayes.lean),
[authentic response and future receipt laws under that actual posterior](../Vegas/Pending/PhaseSeedPosteriorResponse.lean),
[receipt independence from full current control and all other original seeds](../Vegas/Pending/PhaseSeedReceiptProduct.lean),
[hidden value swaps through saved states and retired attempts](../Vegas/Pending/PhaseValueSwap.lean),
[actual phased handler and environment swap commutation](../Vegas/Pending/PhaseSwapApplication.lean),
[complete physical execution and private recall swap replay](../Vegas/Pending/PhaseReactiveValueSwap.lean),
[signed packet, evidence normalization and counted-menu swap transport](../Vegas/Pending/PhaseSwapMenu.lean),
[complete actual observer recall fixed by invisible value changes](../Vegas/Pending/PhaseSwapInformation.lean),
[actual phase admission guards for private-value replay](../Vegas/Pending/PhaseSwapAdmission.lean),
[foreign private-pair observer equality for every graph and execution mode](../Vegas/Pending/PhaseOwnerPairs.lean),
[exact counted-response normalization and canonical binding evidence](../Vegas/Pending/PhaseResponseNormalization.lean),
[clear normalization with no retry generation or retired archive](../Vegas/Pending/PhaseClearHistory.lean),
[accepted handles, stores and action words retained by clear physical steps](../Vegas/Pending/PhaseClearNativeProgress.lean),
[their retention across actual clear initialized trace prefixes](../Vegas/Pending/PhaseClearTraceProgress.lean),
[unfinished head-phase persistence at clear transitions](../Vegas/Pending/PhaseClearPhasePersistence.lean),
[backward closure of actual admitted-call swap guards](../Vegas/Pending/PhaseSwapGuard.lean),
[same-scheduler physical transition support replay under those guards](../Vegas/Pending/PhaseSwapTransition.lean),
[involutive counted-history symmetry and complete focal information transport](../Vegas/Pending/PhaseSwapSymmetry.lean),
[actual guarded full-information-fiber bijections](../Vegas/Pending/PhaseSwapFiber.lean),
[exact initialized joint laws for computed-field and prepared-handle swaps](../Vegas/Pending/PhaseSwapInitialLaw.lean),
[default-graph foreign-owner swap information adapter](../Vegas/Game/PhaseOwnerSwapInformation.lean),
[actual singleton menus after an own packet](../Vegas/Pending/PhaseSentMenu.lean),
[all-candidate local seed transcript constraints](../Interaction/ReactiveAddressedQueryTranscript.lean),
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

Clear phase/native transport:
[Message Network Map](../Interaction/MessageNetworkMap.lean),
[Phase Packet Address](../Vegas/Pending/PhasePacketAddress.lean),
[Phase Native Projection](../Vegas/Pending/PhaseNativeProjection.lean),
[Phase Native Cursor](../Vegas/Pending/PhaseNativeCursor.lean),
[Phase Native Response](../Vegas/Pending/PhaseNativeResponse.lean),
[Phase Native Handle](../Vegas/Pending/PhaseNativeHandle.lean),
[Phase Native Scheduler](../Vegas/Pending/PhaseNativeScheduler.lean),
[Phase Native Inclusion](../Vegas/Pending/PhaseNativeInclusion.lean),
[Phase Native Environment](../Vegas/Pending/PhaseNativeEnvironment.lean),
[Phase Native Failure Record](../Vegas/Pending/PhaseNativeFailureRecord.lean),
[Phase Native Environment Execution](../Vegas/Pending/PhaseNativeEnvironmentExecution.lean),
[Phase Native Trace](../Vegas/Pending/PhaseNativeTrace.lean),
[Phase Native Player Input](../Vegas/Pending/PhaseNativePlayerInput.lean).
These modules transport actual clear count-clean traces, full recalls, arbitrary scheduler commands and local policy kernels. They do not assert a joint source law.

Directed binding repair:
[Phase Binding Shadow](../Vegas/Pending/PhaseBindingShadow.lean),
[Phase Binding Repair Observation](../Vegas/Pending/PhaseBindingRepairObservation.lean),
[Phase Raw Binding Repair](../Vegas/Pending/PhaseRawBindingRepair.lean),
[Phase Binding Shadow Step](../Vegas/Pending/PhaseBindingShadowStep.lean),
[Phase Binding Preparation Repair](../Vegas/Pending/PhaseBindingPreparationRepair.lean),
[Phase Binding Repair Inclusion](../Vegas/Pending/PhaseBindingRepairInclusion.lean),
[Phase Binding Repair Completion](../Vegas/Pending/PhaseBindingRepairCompletion.lean),
[Phase Binding Repair Projection](../Vegas/Pending/PhaseBindingRepairProjection.lean),
[Phase Binding Repair Frame](../Vegas/Pending/PhaseBindingRepairFrame.lean),
[Phase Binding Repair Normalize](../Vegas/Pending/PhaseBindingRepairNormalize.lean),
[Phase Binding Native Response](../Vegas/Pending/PhaseBindingNativeResponse.lean),
[Phase Binding Count Transport](../Vegas/Pending/PhaseBindingCountTransport.lean),
[Phase Binding Checkpoint Frame](../Vegas/Pending/PhaseBindingCheckpointFrame.lean),
[Phase Binding Native Inclusion](../Vegas/Pending/PhaseBindingNativeInclusion.lean),
[Phase Binding Raw Inclusion](../Vegas/Pending/PhaseBindingRawInclusion.lean),
[Phase Binding Delayed Repair](../Vegas/Pending/PhaseBindingDelayedRepair.lean),
[Phase Binding Repair Trace](../Vegas/Pending/PhaseBindingRepairTrace.lean),
[Phase Binding Repair Observation Step](../Vegas/Pending/PhaseBindingRepairObservationStep.lean),
[Phase Binding Repair Menu](../Vegas/Pending/PhaseBindingRepairMenu.lean).
The live and saved checkpoint frames support actual normalization, binding inclusion and observation steps. Whole arbitrary-suffix repair and remaining pending-read guards require separate adapters.

Chronological source conditioning:
[Commit Recovery Nonmissing Law](../Vegas/Game/CommitRecoveryNonmissingLaw.lean),
[Commit Recovery Nonmissing Reach](../Vegas/Game/CommitRecoveryNonmissingReach.lean),
[Commit Recovery Nonmissing Position](../Vegas/Game/CommitRecoveryNonmissingPosition.lean),
[Commit Recovery Nonmissing Source](../Vegas/Game/CommitRecoveryNonmissingSource.lean),
[Commit Recovery Nonmissing Conditioning](../Vegas/Game/CommitRecoveryNonmissingConditioning.lean),
[Commit Recovery Nonmissing Belief](../Vegas/Game/CommitRecoveryNonmissingBelief.lean).
The original auxiliary runner factors through nonmissing conditional kernels with a static clear-prefix scalar. Its exact full-fiber Bayes identity is source-side; native conditional likelihoods require further transport.

Compiler action and commitment-window adapters:
[Event Source Policy Law](../Vegas/Compile/EventSourcePolicyLaw.lean),
[Commit Recovery Compiled Policy](../Vegas/Game/CommitRecoveryCompiledPolicy.lean),
[Commit Recovery Commit Window](../Vegas/Source/CommitRecoveryCommitWindow.lean).
Successful full-view decoding transports the entire compiled action law; actual intended information witnesses connect the auxiliary law. The nonmissing source runner remains clear throughout its real commitment window.

Intended source counterparts:
[Intended No Debt](../Vegas/Source/IntendedNoDebt.lean),
[Commit Recovery Intended Information](../Vegas/Game/CommitRecoveryIntendedInformation.lean),
[Commit Recovery Intended Policy Law](../Vegas/Game/CommitRecoveryIntendedPolicyLaw.lean),
[Recovery Source Checkpoint](../Vegas/Game/RecoverySourceCheckpoint.lean),
[Recovery Intended Binding Checkpoint](../Vegas/Game/RecoveryIntendedBindingCheckpoint.lean),
[Protocol Suffix](../Vegas/Source/ProtocolSuffix.lean),
[Commit Prefix Intended Lift](../Vegas/Source/CommitPrefixIntendedLift.lean).
Exact syntactic source origins and preserved entry cells build initialized intended binding information from a saved intended entry and admissible own bindings. These two on-path invariants are explicit obligations.

Source windows and native response masses:
[Commit Recovery Window Law](../Vegas/Game/CommitRecoveryWindowLaw.lean),
[Commit Recovery Belief Window](../Vegas/Game/CommitRecoveryBeliefWindow.lean),
[Commit Recovery Choice Floor](../Vegas/Game/CommitRecoveryChoiceFloor.lean),
[Phase Binding Response Ratio](../Vegas/Game/PhaseBindingResponseRatio.lean),
[Event Source Position](../Vegas/Compile/EventSourcePosition.lean),
[Phase Binding Waiting Law](../Vegas/Game/PhaseBindingWaitingLaw.lean).
Full source information fibers retain their original posterior across clear commitment windows. Finite source choice floors give local native response ratios; same-event canonical-plus-slot WAIT atoms agree. Raw-noise menu terms and whole-history likelihoods need further transport.

Paired kernels and compiled response adapters:
[Event Graph Disclosure Action](../Vegas/Compile/EventGraphDisclosureAction.lean),
[Phase Native Paired Transition](../Vegas/Pending/PhaseNativePairedTransition.lean),
[Phase Native Control Law](../Vegas/Pending/PhaseNativeControlLaw.lean),
[Phase Compiled Binding Response](../Vegas/Game/PhaseCompiledBindingResponse.lean),
[Phase Compiled Opening Response](../Vegas/Game/PhaseCompiledOpeningResponse.lean).
Both physical transition marginals and policy kernels are coupled with the exact failure record. Compiled response adapters preserve whole responses, and disclosing compiler policies publish TRUE without a decode premise.

Operational replay and supported execution:
[Recovery Commit Checkpoint](../Vegas/Game/RecoveryCommitCheckpoint.lean),
[Recovery Commit Prefix Witness](../Vegas/Game/RecoveryCommitPrefixWitness.lean),
[Recovery Ready Commit Witness](../Vegas/Game/RecoveryReadyCommitWitness.lean),
[Reveal Recovery Residual](../Vegas/Game/RevealRecoveryResidual.lean),
[Recovery Reveal Checkpoint](../Vegas/Game/RecoveryRevealCheckpoint.lean),
[Recovery Sample Checkpoint](../Vegas/Game/RecoverySampleCheckpoint.lean),
[Recovery Settled Commit Checkpoint](../Vegas/Game/RecoverySettledCommitCheckpoint.lean),
[Reactive Frontier Execution](../Vegas/Pending/ReactiveFrontierExecution.lean),
[Source Service Reactive Law](../Vegas/Game/SourceServiceReactiveLaw.lean),
[Source Service Reactive Audit](../Vegas/Game/SourceServiceReactiveAudit.lean),
[Reactive Consistent History](../Interaction/ReactiveConsistentHistory.lean),
[Phase Binding Checkpoint Submission](../Vegas/Pending/PhaseBindingCheckpointSubmission.lean),
[Phase Binding Foreign Response](../Vegas/Pending/PhaseBindingForeignResponse.lean),
[Phase Opening Acceptance](../Vegas/Pending/PhaseOpeningAcceptance.lean),
[Phase Binding Repaired Response](../Vegas/Pending/PhaseBindingRepairedResponse.lean),
[Phase Binding Opening Read](../Vegas/Pending/PhaseBindingOpeningRead.lean),
[Phase Binding Inert Response](../Vegas/Pending/PhaseBindingInertResponse.lean),
[Phase Binding Opening Response](../Vegas/Pending/PhaseBindingOpeningResponse.lean),
[Phase Binding Clock Replay](../Vegas/Pending/PhaseBindingClockReplay.lean),
[Phase Binding Response Aliases](../Vegas/Pending/PhaseBindingResponseAliases.lean),
[Phase Binding Silent Response](../Vegas/Pending/PhaseBindingSilentResponse.lean).
Response and clock replay retain both semantic checkpoints and exact private recall. Selected-command expiry hypotheses and exact consistent-history support are reusable execution adapters. Whole arbitrary-history repair and native/source joint probability remain separate obligations.

Original memory and compiled observations:
[Reactive Intention Recall](../Vegas/Pending/ReactiveIntentionRecall.lean),
[Reactive Disclosing Recall](../Vegas/Pending/ReactiveDisclosingRecall.lean),
[Phase Original Observation](../Vegas/Pending/PhaseOriginalObservation.lean),
[Phase Compiled Observation](../Vegas/Game/PhaseCompiledObservation.lean),
[Phase Compiled Binding Memory](../Vegas/Game/PhaseCompiledBindingMemory.lean).
Supported disclosing memories fix the entire physical configuration at genuine clear histories. The compiled physical binding adapter derives its graph decoder match; intended source playedness remains separate.

Guard admission and retained source reads:
[Protocol Suffix Menu](../Vegas/Source/ProtocolSuffixMenu.lean),
[Commit Prefix Read Stability](../Vegas/Compile/CommitPrefixReadStability.lean),
[Compiled Commit Partial View](../Vegas/Game/CompiledCommitPartialView.lean),
[Commit Prefix Admission](../Vegas/Compile/CommitPrefixAdmission.lean),
[Phase Commit Read Stability](../Vegas/Game/PhaseCommitReadStability.lean).
Saved whole intendedness and admitted own prefixes imply local source guard acceptance and phase-close intendedness including future guard satisfiability. Actual clear trace prefixes preserve the required reads after completion.

Exact historical policy inputs:
[Reactive Recorded Response](../Interaction/ReactiveRecordedResponse.lean),
[Reactive Seed Binding Outcome](../Vegas/Pending/ReactiveSeedBindingOutcome.lean),
[Phase Swap Information](../Vegas/Pending/PhaseSwapInformation.lean),
[Phase Continuing Binding](../Vegas/Game/PhaseContinuingBinding.lean).
Remembered responses retain the actual earlier trace prefix and exact own input word. Continuing source policies emit at clear unsent bindings and exclude silent same-coordinate earlier responses in consistent recall.

Actual application-command replay:
[Phase Binding Rejected Replay](../Vegas/Pending/PhaseBindingRejectedReplay.lean),
[Phase Binding Sample Replay](../Vegas/Pending/PhaseBindingSampleReplay.lean),
[Phase Binding Expiry Replay](../Vegas/Pending/PhaseBindingExpiryReplay.lean),
[Phase Binding Expiry Coupling](../Vegas/Pending/PhaseBindingExpiryCoupling.lean),
[Phase Binding Environment Trace](../Vegas/Pending/PhaseBindingEnvironmentTrace.lean),
[Phase Binding Application Replay](../Vegas/Pending/PhaseBindingApplicationReplay.lean).
Both real command marginals are coupled through saved/live repair frames with the same scheduler. Missing and public-gate rejected inclusions also replay; successful inclusion and whole-history dispatch remain separate.

Binding WAIT products and quantitative noise:
[Phase Binding Response Ratio](../Vegas/Game/PhaseBindingResponseRatio.lean),
[Phase Binding Waiting Law](../Vegas/Game/PhaseBindingWaitingLaw.lean),
[Commit Recovery Missing Floor](../Vegas/Game/CommitRecoveryMissingFloor.lean),
[Phase Waiting Mass](../Vegas/Game/PhaseWaitingMass.lean),
[Phase Binding Waiting Ratio](../Vegas/Game/PhaseBindingWaitingRatio.lean),
[Phase Waiting Prefix](../Vegas/Game/PhaseWaitingPrefix.lean),
[Phase Repair Noise](../Vegas/Game/PhaseRepairNoise.lean).
Actual own-play WAIT factors give player-reach cross bounds, retaining all complementary factors and unequal raw menus. The same genuine source floors instantiate send ratios, WAIT ratios and a positive vanishing raw-noise schedule.

Authentic source choices and local admission:
[Commit Prefix Admitted Action](../Vegas/Compile/CommitPrefixAdmittedAction.lean),
[Phase Source Policy](../Vegas/Game/PhaseSourcePolicy.lean),
[Phase Recorded Binding Meaning](../Vegas/Pending/PhaseRecordedBindingMeaning.lean),
[Phase Binding Response Origin](../Vegas/Pending/PhaseBindingResponseOrigin.lean),
[Phase Source Binding Origin](../Vegas/Game/PhaseSourceBindingOrigin.lean),
[Recovery Commit Prefix Witness](../Vegas/Game/RecoveryCommitPrefixWitness.lean),
[Recovery Intended Binding Checkpoint](../Vegas/Game/RecoveryIntendedBindingCheckpoint.lean),
[Phase Binding Source Admission](../Vegas/Game/PhaseBindingSourceAdmission.lean).
Actual surviving accepted bindings retain their original supported callback and typed meaning. Copied intended choices derive guard admission at the exact filled predecessor, conditional on saved intendedness and earlier own admission; the actual canonical-history and static-prefix consumers below derive those hypotheses.

Exact chosen source checkpoint successors:
[Commit Recovery Non Commit Intended](../Vegas/Source/CommitRecoveryNonCommitIntended.lean),
[Compiled Commit Completion](../Vegas/Game/CompiledCommitCompletion.lean),
[Recovery Settled Commit Checkpoint](../Vegas/Game/RecoverySettledCommitCheckpoint.lean),
[Recovery Reveal Checkpoint](../Vegas/Game/RecoveryRevealCheckpoint.lean),
[Recovery Sample Checkpoint](../Vegas/Game/RecoverySampleCheckpoint.lean),
[Recovery Checkpoint Normalization](../Vegas/Game/RecoveryCheckpointNormalization.lean).
Clear completed attempts equal physical prefix completion. The chosen commitment, sample and reveal successors retain whole intendedness under the stated admission/clarity hypotheses; the actual clear canonical-history consumer below supplies admission and threads the chosen checkpoint.

All counted packet inclusion cases:
[Phase Binding Admitted Include](../Vegas/Pending/PhaseBindingAdmittedInclude.lean),
[Phase Binding Inclusion Frame](../Vegas/Pending/PhaseBindingInclusionFrame.lean),
[Phase Binding Opening Inclusion](../Vegas/Pending/PhaseBindingOpeningInclusion.lean),
[Phase Binding Counted Opening](../Vegas/Pending/PhaseBindingCountedOpening.lean),
[Phase Binding Foreign Inclusion](../Vegas/Pending/PhaseBindingForeignInclusion.lean),
[Phase Binding Rejected Inclusion](../Vegas/Pending/PhaseBindingRejectedInclusion.lean),
[Phase Binding Counted Foreign](../Vegas/Pending/PhaseBindingCountedForeign.lean),
[Phase Binding Counted Inclusion](../Vegas/Pending/PhaseBindingCountedInclusion.lean),
[Phase Binding Include Dispatcher](../Vegas/Pending/PhaseBindingIncludeDispatcher.lean),
[Phase Binding Inclusion Trace](../Vegas/Pending/PhaseBindingInclusionTrace.lean).
The actual same-scheduler include command extends paired directed histories across all packet branches. Submitted-binding records and own-binding memory are established and preserved by the whole-history consumer below.

Exact directed opening response factors:
[Reactive Uniform Menu](../Interaction/ReactiveUniformMenu.lean),
[Phase Opening Coverage](../Vegas/Pending/PhaseOpeningCoverage.lean),
[Phase Opening Policy](../Vegas/Pending/PhaseOpeningPolicy.lean),
[Phase Source Policy Law](../Vegas/Game/PhaseSourcePolicyLaw.lean),
[Phase Source Slot Policy Law](../Vegas/Game/PhaseSourceSlotPolicyLaw.lean),
[Phase Compiled Opening Response](../Vegas/Game/PhaseCompiledOpeningResponse.lean),
[Phase Sent Menu](../Vegas/Pending/PhaseSentMenu.lean),
[Phase Opening Binding Prefix](../Vegas/Pending/PhaseOpeningBindingPrefix.lean),
[Phase Opening Waiting Law](../Vegas/Game/PhaseOpeningWaitingLaw.lean),
[Phase Binding Inert Response](../Vegas/Pending/PhaseBindingInertResponse.lean),
[Phase Opening Menu Shape](../Vegas/Pending/PhaseOpeningMenuShape.lean),
[Phase Opening Menu Symmetry](../Vegas/Pending/PhaseOpeningMenuSymmetry.lean),
[Phase Opening Response Symmetry](../Vegas/Game/PhaseOpeningResponseSymmetry.lean).
Actual clear binding endpoints force prior opening success. Directed opening callbacks have equal entire response laws, including exactly equal counted raw-noise menus; the whole-prefix product consumer below composes these factors; native Bayes transport remains separate.

Actual intended source histories:
[Trace Prefix](../GameTheoryExtensions/Protocol/TracePrefix.lean),
[Commit Prefix Snoc](../Vegas/Source/CommitPrefixSnoc.lean),
[Commit Prefix Completion Snoc](../Vegas/Compile/CommitPrefixCompletionSnoc.lean),
[Phase Resolution](../Vegas/Pending/PhaseResolution.lean),
[Phase Semantic Progress](../Vegas/Pending/PhaseSemanticProgress.lean),
[Phase Service Progress](../Vegas/Pending/PhaseServiceProgress.lean),
[Phase Attempt Checkpoint](../Vegas/Pending/PhaseAttemptCheckpoint.lean),
[Phase Binding Stamp History](../Vegas/Pending/PhaseBindingStampHistory.lean),
[Phase Binding Response Origin](../Vegas/Pending/PhaseBindingResponseOrigin.lean),
[Phase Source Binding Origin](../Vegas/Game/PhaseSourceBindingOrigin.lean),
[Recovery Ready Commit Witness](../Vegas/Game/RecoveryReadyCommitWitness.lean),
[Recovery Intended Binding Checkpoint](../Vegas/Game/RecoveryIntendedBindingCheckpoint.lean),
[Phase Binding Source Admission](../Vegas/Game/PhaseBindingSourceAdmission.lean),
[Phase Completed Binding Admission](../Vegas/Game/PhaseCompletedBindingAdmission.lean),
[Phase Commit Prefix Admission](../Vegas/Game/PhaseCommitPrefixAdmission.lean),
[Phase Raw Commit Admission](../Vegas/Game/PhaseRawCommitAdmission.lean),
[Recovery Initial Checkpoint](../Vegas/Game/RecoveryInitialCheckpoint.lean),
[Phase Clear Settlement](../Vegas/Pending/PhaseClearSettlement.lean),
[Recovery Intended Normalization](../Vegas/Game/RecoveryIntendedNormalization.lean),
[Phase Intended Checkpoint Step](../Vegas/Game/PhaseIntendedCheckpointStep.lean),
[Phase Intended Checkpoint History](../Vegas/Game/PhaseIntendedCheckpointHistory.lean).
Static source-prefix induction reconstructs admission at authentic callbacks. Actual clear canonical histories retain one whole intended saved source checkpoint through genuine raw completion and chosen normalization.

Whole directed history repair and exact counterfactual reach:
[Phase Binding Clear Counts](../Vegas/Pending/PhaseBindingClearCounts.lean),
[Phase Binding Submitted Preservation](../Vegas/Pending/PhaseBindingSubmittedPreservation.lean),
[Phase Binding Submitted Repair](../Vegas/Pending/PhaseBindingSubmittedRepair.lean),
[Phase Binding Submitted Raw Repair](../Vegas/Pending/PhaseBindingSubmittedRawRepair.lean),
[Phase Binding Idle Menu](../Vegas/Pending/PhaseBindingIdleMenu.lean),
[Reactive Environment Mass](../Interaction/ReactiveEnvironmentMass.lean),
[Phase Binding Sample Replay](../Vegas/Pending/PhaseBindingSampleReplay.lean),
[Phase Binding Activation Mass](../Vegas/Pending/PhaseBindingActivationMass.lean),
[Phase Binding Reach](../Vegas/Pending/PhaseBindingReach.lean),
[Phase Binding Sample Mass](../Vegas/Pending/PhaseBindingSampleMass.lean),
[Phase Binding Environment Mass](../Vegas/Pending/PhaseBindingEnvironmentMass.lean),
[Phase Binding Counterfactual Step](../Vegas/Pending/PhaseBindingCounterfactualStep.lean),
[Phase Binding Response Dispatcher](../Vegas/Pending/PhaseBindingResponseDispatcher.lean),
[Phase Binding Environment Dispatcher](../Vegas/Pending/PhaseBindingEnvironmentDispatcher.lean),
[Phase Binding History Repair](../Vegas/Pending/PhaseBindingHistoryRepair.lean),
[Phase Binding Response Witness](../Vegas/Pending/PhaseBindingResponseWitness.lean),
[Phase Repair Sending Witness](../Vegas/Game/PhaseRepairSendingWitness.lean),
[Phase Repair Callback Witness](../Vegas/Game/PhaseRepairCallbackWitness.lean),
[Phase Repair History Witness](../Vegas/Game/PhaseRepairHistoryWitness.lean).
Actual response and environment steps construct both genuine histories, retain submitted/own binding provenance and derive exact repair-owner counterfactual reach equality from real command atoms. The compiled driver derives chronological callback categories; whole native/source law and Bayes transport remain separate.

Whole-prefix and marked raw-binding contributions:
[Phase Waiting Prefix](../Vegas/Game/PhaseWaitingPrefix.lean),
[Phase Repair Own Play](../Vegas/Game/PhaseRepairOwnPlay.lean),
[Phase Repair Response Factor](../Vegas/Game/PhaseRepairResponseFactor.lean),
[Phase Repair Prefix Likelihood](../Vegas/Game/PhaseRepairPrefixLikelihood.lean),
[Phase Raw Binding Contribution](../Vegas/Game/PhaseRawBindingContribution.lean),
[Phase Marked Repair Likelihood](../Vegas/Game/PhaseMarkedRepairLikelihood.lean).
Actual chronological own-play products derive send and WAIT bounds using one genuine source floor. A selected raw-mixture binding send retains an additional noise factor; source canonical failures remain in the unmarked factors. The marked-fiber consumers below bound finite preimages and normalized raw binding-send contributions; full native/source posterior identification remains open.

Actual intended binding inputs and source reveal geometry:
[Compiled Commit Partial View](../Vegas/Game/CompiledCommitPartialView.lean),
[Phase Binding Readiness](../Vegas/Pending/PhaseBindingReadiness.lean),
[Recovery Binding Prefix](../Vegas/Game/RecoveryBindingPrefix.lean),
[Recovery Ready Commit Witness](../Vegas/Game/RecoveryReadyCommitWitness.lean),
[Phase Binding Counterpart](../Vegas/Game/PhaseBindingCounterpart.lean),
[Phase Intended Binding Information](../Vegas/Game/PhaseIntendedBindingInformation.lean),
[Phase Intended Binding Response](../Vegas/Game/PhaseIntendedBindingResponse.lean),
[Recovery Ready Reveal Prefix](../Vegas/Game/RecoveryReadyRevealPrefix.lean).
Actual clear canonical histories derive complete intended binding information and both decoder equations. The compiled binding response consumer no longer asks for an independently supplied intended site. Ready source reveal prefixes are recovered without requiring independent publications to have completed.

Marked history repair and normalized opponent raw-binding contributions:
[Phase Repair Raw Sending Witness](../Vegas/Game/PhaseRepairRawSendingWitness.lean),
[Phase Repair Marked Records](../Vegas/Game/PhaseRepairMarkedRecords.lean),
[Phase Repair Marked History](../Vegas/Game/PhaseRepairMarkedHistory.lean),
[Finite Repair Mass](../GameTheoryExtensions/Analysis/Protocol/FiniteRepairMass.lean),
[Phase Marked Repair Mass](../Vegas/Game/PhaseMarkedRepairMass.lean),
[Phase Marked Binding Fiber](../Vegas/Game/PhaseMarkedBindingFiber.lean),
[Phase Binding Fiber Geometry](../Vegas/Game/PhaseBindingFiberGeometry.lean),
[Phase Opponent Raw Binding Mass](../Vegas/Game/PhaseOpponentRawBindingMass.lean),
[Phase Opponent Raw Binding Limit](../Vegas/Game/PhaseOpponentRawBindingLimit.lean),
[Phase Clear Profile Locality](../Vegas/Game/PhaseClearProfileLocality.lean),
[Phase Common Raw Binding Limit](../Vegas/Game/PhaseCommonRawBindingLimit.lean).
Actual marked repair derives same-information-fiber images and all before/after response pairings. Finite legal-history cardinality bounds repair preimages. Summing every opponent and position yields a normalized raw binding-send contribution tending to zero. Exact locality transfers the bound from the recipe to all actual common profiles with its clear-site clause. Canonical source failures, omissions and opening WAIT remain in the law; native/source posterior identification is separate.

Native recall consistency, original behavioral runs and first failure:
[Phase Native Consistency](../Vegas/Pending/PhaseNativeConsistency.lean),
[Phase Native Policy Consistency](../Vegas/Pending/PhaseNativePolicyConsistency.lean),
[Phase Native Policy Run](../Vegas/Pending/PhaseNativePolicyRun.lean),
[Phase Native Supported Play](../Vegas/Pending/PhaseNativeSupportedPlay.lean),
[Phase Native Control Run](../Vegas/Pending/PhaseNativeControlRun.lean),
[Phase Native Behavioral Run](../Vegas/Pending/PhaseNativeBehavioralRun.lean),
[Phase Native Failure Exit](../Vegas/Pending/PhaseNativeFailureExit.lean),
[Source Fresh Call Deadline](../Vegas/Game/SourceFreshCallDeadline.lean).
Complete clear owner recall transports policy consistency. Local law matching under prior consistency propagates prescribed native consistency by actual history induction. Both original finite-fuel behavioral laws have an exact coupling conditional on physical safety. First exclusion extracts an actual native public failure before rollback; the existing protected-inclusion engine excludes a still-ready acceptable fresh packet at its deadline. The canonical physical safety adapter below discharges that premise for the compiled service runtime.

Physical service contracts and authentic fresh calls:
[Phase Service Contract](../Vegas/Pending/PhaseServiceContract.lean),
[Phase Service Projection](../Vegas/Pending/PhaseServiceProjection.lean),
[Phase Binding Fresh Call](../Vegas/Game/PhaseBindingFreshCall.lean).
The physical contract retains all raw legal histories, original readiness stamps,
strict timing bounds and sole identifiers for each attempt-event coordinate.
Actual clear prefixes supply native pointwise service conditions without a
global reconstructed-native contract. An actual permitted binding response
emitted in its protected window supplies an original native fresh-call
certificate. The physical timing and binding-deadline adapters below derive
actual timely callbacks. The opening deadline and whole-execution safety adapters below complete the canonical case.


Actual compiled response matching and prescribed runs:
[Present Context Evaluation](../Vegas/Compile/PresentContextEvaluation.lean),
[Compiled Reveal Phase](../Vegas/Game/CompiledRevealPhase.lean),
[Compiled Reveal Present](../Vegas/Game/CompiledRevealPresent.lean),
[Compiled Ready Reveal](../Vegas/Game/CompiledReadyReveal.lean),
[Phase Intended Opening Success](../Vegas/Game/PhaseIntendedOpeningSuccess.lean),
[Phase Compiled Disclosure](../Vegas/Game/PhaseCompiledDisclosure.lean),
[Phase Intended Opening Response](../Vegas/Game/PhaseIntendedOpeningResponse.lean),
[Phase Compiled Sent Response](../Vegas/Game/PhaseCompiledSentResponse.lean),
[Phase Clear Request Address](../Vegas/Pending/PhaseClearRequestAddress.lean),
[Phase Recorded Request](../Vegas/Pending/PhaseRecordedRequest.lean),
[Phase Unsent Native Memory](../Vegas/Pending/PhaseUnsentNativeMemory.lean),
[Phase Canonical Freshness](../Vegas/Game/PhaseCanonicalFreshness.lean),
[Phase Compiled Response](../Vegas/Game/PhaseCompiledResponse.lean),
[Phase Compiled Run](../Vegas/Game/PhaseCompiledRun.lean).
Actual clear canonical histories derive successful guarded openings despite
partial publication holes. Complete physical/native response equality covers
every dispatcher branch. Native consistency and compiled ready independence
are derived, and the original finite-fuel coupling retains physical safety as
its operational premise.

Physical owner response timing and binding deadline safety:
[Phase Fresh Call Settlement](../Vegas/Game/PhaseFreshCallSettlement.lean),
[Phase Owner Opportunity](../Vegas/Pending/PhaseOwnerOpportunity.lean),
[Phase Owner Response](../Vegas/Pending/PhaseOwnerResponse.lean),
[Phase Sole Packet](../Vegas/Pending/PhaseSolePacket.lean),
[Phase Activation Response](../Vegas/Pending/PhaseActivationResponse.lean),
[Phase Binding Recall Conformance](../Vegas/Game/PhaseBindingRecallConformance.lean),
[Phase Binding Packet Callback](../Vegas/Game/PhaseBindingPacketCallback.lean),
[Phase Binding Deadline](../Vegas/Game/PhaseBindingDeadline.lean).
The original all-raw-history physical contract derives actual timely callbacks
at the original attempt and activation stamp. A remembered canonical binding
has its genuine earlier unsent callback. Protected inclusion and fresh-call
settlement rule out a ready binding at its deadline, including accepted failed
bindings. The opening and first-exclusion adapters below establish whole canonical safety.

Actual nonmissing binding and full source-block reference laws:
[Phase Binding Nonmissing Law](../Vegas/Game/PhaseBindingNonmissingLaw.lean),
[Phase Binding Nonmissing Reference](../Vegas/Game/PhaseBindingNonmissingReference.lean),
[Phase Binding Encoding Law](../Vegas/Pending/PhaseBindingEncodingLaw.lean),
[Phase Recovery Slot Atom](../Vegas/Game/PhaseRecoverySlotAtom.lean),
[Phase Binding Slot Symmetry](../Vegas/Pending/PhaseBindingSlotSymmetry.lean),
[Phase Binding Source Reference](../Vegas/Game/PhaseBindingSourceReference.lean),
[Commit Prefix Product](../Vegas/Source/CommitPrefixProduct.lean),
[Commit Prefix Conditioning](../Vegas/Source/CommitPrefixConditioning.lean),
[Protocol Suffix Policy](../Vegas/Source/ProtocolSuffixPolicy.lean),
[Phase Commit Block Reference](../Vegas/Game/PhaseCommitBlockReference.lean).
Actual callbacks derive the exact nonmissing source response and eligible-slot
atom law. A fixed saved entry supplies the complete maximal commitment block
as a product over owner words, preserving dependence within each owner's word
and retaining later-ranked foreign choices. Original omission flags and
mixtures over source entries are not removed by this reference law. Actual
native/source posterior identification remains separate.

Native frontiers and complete execution from physical safety:
[Phase Native Policy Preimage](../Vegas/Pending/PhaseNativePolicyPreimage.lean),
[Reactive Failure Free Expiry](../Vegas/Pending/ReactiveFailureFreeExpiry.lean),
[Reactive Frontier Execution](../Vegas/Pending/ReactiveFrontierExecution.lean),
[Source Service Reactive Law](../Vegas/Game/SourceServiceReactiveLaw.lean),
[Phase Native Frontier Law](../Vegas/Pending/PhaseNativeFrontierLaw.lean),
[Phase Native Round Law](../Vegas/Pending/PhaseNativeRoundLaw.lean),
[Reactive Initial Support](../Interaction/ReactiveInitialSupport.lean),
[Phase Native Initial Support](../Vegas/Pending/PhaseNativeInitialSupport.lean),
[Phase Native Initial Rounds](../Vegas/Pending/PhaseNativeInitialRounds.lean).
Under physical safety and actual actor-local law matching, every actual
prescribed-consistent native history has a clear physical preimage. Failure-free
expiry and completion at those consistent histories instantiate the existing
posterior-frontier engine; no global native completion contract is imposed.
The terminal-store theorem is pointwise at an original supported input.
Complete round projection and initial-support transport permit outer binding
of the original initial law without inferring a joint law from mixed marginals.
The source-service caller also supplies the weaker completion interface.


Original initialized source and terminal behavioral laws:
[Phase Compiled Source Law](../Vegas/Game/PhaseCompiledSourceLaw.lean),
[Reactive Terminal Evaluation](../Interaction/ReactiveTerminalEvaluation.lean),
[Phase Compiled Behavioral Law](../Vegas/Game/PhaseCompiledBehavioralLaw.lean).
The original physical and native round evaluators retain the original initial
draw jointly with the complete typed source readout and arbitrary realized
payoff vectors. Supported-input restriction is used before the original outer
initial-law bind. Local matching and ready independence are derived; physical
safety and the original physical completion contract remain explicit.
Terminal behavioral histories evaluate the same covered physical profile,
and their actual typed source readout has the corresponding source-run law.

Actual packet provenance and focal Bayes interventions:
[Phase Packet Callback](../Vegas/Pending/PhasePacketCallback.lean),
[Reactive Recall Replay](../Interaction/ReactiveRecallReplay.lean).
An actual owned packet supplies its genuine earlier legal supported callback,
exact request, complete recall decomposition and unsent condition. The replay
policy fixes all focal recorded choices on the actual information fiber with
unit own reach. Positive replayed information mass follows from the original
mass, and the existing counterfactual Bayes theorem gives exact belief equality.
This intervenes on focal raw sends; opponent full-block likelihood and actual
native/source Bayes identification remain separate obligations.


Canonical physical safety and contract-only source laws:
[Phase Opening Recall Conformance](../Vegas/Game/PhaseOpeningRecallConformance.lean),
[Phase Binding Deadline](../Vegas/Game/PhaseBindingDeadline.lean),
[Phase Opening Deadline](../Vegas/Game/PhaseOpeningDeadline.lean),
[Phase Canonical Operations](../Vegas/Game/PhaseCanonicalOperations.lean),
[Phase Canonical Expiry](../Vegas/Game/PhaseCanonicalExpiry.lean),
[Phase Canonical Safety](../Vegas/Game/PhaseCanonicalSafety.lean),
[Phase Canonical Source Law](../Vegas/Game/PhaseCanonicalSourceLaw.lean).
Actual remembered packets retain their genuine callbacks and original
protected emission windows. The physical all-raw-history service contract
rules out due canonical bindings and openings. Accepted operations preserve
clarity, and first-exclusion extraction proves every canonical-consistent
initialized counted history clear. The compiled service runtime's original
setup/readout/payoff joint laws and terminal source/base-payoff/randomized
settlement laws derive safety internally; supported terminal histories exclude
and charge no player. No global reconstructed native contract is imposed.

The same completed assessment and canonical execution law:
[Phase Source Dispatch Limit](../Vegas/Game/PhaseSourceDispatchLimit.lean),
[Phase Source Completion Law](../Vegas/Game/PhaseSourceCompletionLaw.lean),
[Phase Source Completion Outcome](../Vegas/Game/PhaseSourceCompletionOutcome.lean),
[Phase Canonical Completion](../Vegas/Game/PhaseCanonicalCompletion.lean),
[Phase Completion Initial Law](../Vegas/Game/PhaseCompletionInitialLaw.lean).
Every actual clear callback has a convergent entire canonical finite strategy,
including no-request and silent branches. Support-local behavioral congruence
gives the same common limit's full finite-fuel and terminal history laws.
One actual fully mixed Bayes sequence, its consistent limit and optimal whole
continuations after public exclusion retain those laws. Under the original
physical service bounds, that same completion has the source readout/base
payoff and actual randomized settlement law, with supported exclusion/charge
zero. Immutable source input cells recover the original setup draw on actual
pure-input histories. The same completed assessment retains that original
draw jointly with readout, base payoffs and randomized settlement through the
original outer initial-law bind. Native/source Bayes and clear-site rationality remain separate; this is
not a native sequential equilibrium theorem.

Full-word source readout and actual callback prediction:
[Commit Prefix Readout](../Vegas/Source/CommitPrefixReadout.lean),
[Commit Prefix Policy Readout](../Vegas/Source/CommitPrefixPolicyReadout.lean),
[Recovery Commit Prefix Support](../Vegas/Game/RecoveryCommitPrefixSupport.lean),
[Phase Binding Response Factor](../Vegas/Game/PhaseBindingResponseFactor.lean),
[Recovery Binding Word Prediction](../Vegas/Game/RecoveryBindingWordPrediction.lean).
The existing complete chronological word retains later foreign and repeated
owner choices while recovering the addressed earlier view/result joint law.
Actual checkpoint attempts derive positive support in the same nonmissing
prefix law without intendedness or successful-binding premises. The callback
adapter derives its filled view and predicts its next conditional raw action.
The entire canonical/slot response factors through the original omission flag
and the nonmissing typed-result/slot encoder. Actual raw noise, the observed
physical recall and the joint saved-entry mixture still require posterior
identification.

Actual local deviation commands:
[Phase Binding Menu Shape](../Vegas/Pending/PhaseBindingMenuShape.lean),
[Phase Binding Deviation Move](../Vegas/Game/PhaseBindingDeviationMove.lean),
[Phase Expiry Exclusion](../Vegas/Pending/PhaseExpiryExclusion.lean).
A genuine legal nonsilent binding derives its exact globally fresh bounded
prepared slot and a legal auxiliary nonmissing move with the actual physical
typed result, including failure. Due expiry of an actual request puts its owner
in permanent exclusion through normalization and rollback, enabling the
existing arbitrary-continuation floor theorem. Silence can later send;
these local command facts do not supply source continuation values or Bayes.

Owned-word physical members and actual response conditioning:
[Commit Prefix Word](../Vegas/Source/CommitPrefixWord.lean),
[Phase Binding Word Kernel](../Vegas/Pending/PhaseBindingWordKernel.lean),
[Phase Binding Word History](../Vegas/Pending/PhaseBindingWordHistory.lean),
[Recovery Binding Word Realization](../Vegas/Game/RecoveryBindingWordRealization.lean),
[Phase Commit Word Policy](../Vegas/Game/PhaseCommitWordPolicy.lean).
The addressed selector uses only one owner's complete source view. Its physical
member is globally legal for the counted menu, and actual initialized unsent
binding histories discharge the channel guard. The full canonical/slot
response is the member mixture under the same owned-word posterior, with the
original omission law retained. SEND updates condition on the exact typed
result, including failure; a positive WAIT leaves the word posterior unchanged.
These are local member laws; accumulated recall and mixed-entry native/source
posterior correspondence remain separate obligations.

Complete words mixed over their original entries:
[Commit Prefix Mixture](../Vegas/Source/CommitPrefixMixture.lean).
An arbitrary entry law remains inside the full chronological word joint law.
Reading the earlier owned view and next result retains the original entry tag.
Conditioning that same joint on the owned view gives its actual entry posterior
and the original next source kernel. No product over entries or native/source
posterior identity is assumed or concluded.

Whole-profile private-word execution:
[Reactive Profile Mixture](../Interaction/ReactiveProfileMixture.lean),
[Phase Commit Word Posterior](../Vegas/Game/PhaseCommitWordPosterior.lean),
[Commit Prefix Entry Kernel](../Vegas/Source/CommitPrefixEntryKernel.lean),
[Commit Prefix Word Recall](../Vegas/Source/CommitPrefixWordRecall.lean).
The existing scheduler runner retains the full sampled member profile jointly
with its execution; the behavioral realization reconstructs that joint from
final own-recall posteriors. Arbitrary outer entry tags remain joint. Each
owner can draw a source word from its observable entry view while reconstructing
the original correlated entry/full-word law. Actual supported binding callbacks
derive their own posterior update witnesses. Supported source effective own
histories determine full views and the same source posterior. Native record
decoding and full source/native posterior transport remain separate.

All-value binding observations:
[Phase Binding Observation](../Vegas/Pending/PhaseBindingObservation.lean),
[Phase Binding Completion Symmetry](../Vegas/Pending/PhaseBindingCompletionSymmetry.lean).
Typed binding results, including failure, have identical complete emitted
envelopes at a fixed fresh handle. Their joint external response law and
random-slot external channel integrate out the typed-result distribution.
The native handler accepts both arbitrary private preparations under its actual
ready/timely/fresh premises and retains an all-value shadow; clear phase
normalization preserves saved, current and retired external views. Whole
physical inclusion-history coupling and arbitrary allocator value comparison
remain separate obligations.

Actual callback values and finite branching:
[Phase Callback Continuation](../Vegas/Game/PhaseCallbackContinuation.lean),
[Phase Local Value Continuation](../Vegas/Game/PhaseLocalValueContinuation.lean),
[Phase Finite Nature](../Vegas/Pending/PhaseFiniteNature.lean),
[Phase Source Finite History](../Vegas/Game/PhaseSourceFiniteHistory.lean).
Every actual callback lottery has its exact original full physical finish law
and bounded payoff expectation. Its actual assessment local value averages
that law over the original information-fiber belief. Silence retains later
callbacks and resets; no source continuation identity is assumed or concluded.
The finite initial prior, finite leaks and finite scheduler branches derive
phase finite nature and bounded counted history finiteness. Timing and service
opportunity alone do not imply those branching properties.
