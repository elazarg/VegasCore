/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.Compiler
import Vegas.Compile.ConditionalExecution
import Vegas.Compile.ConditionalPublicationSite
import Vegas.Compile.ConditionalOpeningController
import Vegas.Compile.ConditionalPublication
import Vegas.Compile.ConditionalResolution
import Vegas.Compile.PublicChoice
import Vegas.Compile.PublicChoiceSite
import Vegas.Compile.PublicChoiceExecution
import Vegas.Compile.PublicChoiceValidation
import Vegas.Compile.PublicChoiceController
import Vegas.Compile.ApplicationImage
import Vegas.Compile.ApplicationImageSamples
import Vegas.Compile.ApplicationSampleLaw
import Vegas.Compile.ApplicationImageBindings
import Vegas.Compile.ApplicationImagePrivacy
import Vegas.Compile.WindowedPrivacy
import Vegas.Compile.WindowedPolicyPrivacy
import Vegas.Compile.WindowedReplayPrivacy
import Vegas.Compile.WindowedMessageOrigins
import Vegas.Compile.ApplicationPolicyAddresses
import Vegas.Compile.ApplicationBindingOrigins
import Vegas.Compile.ApplicationAcceptedPrefix
import Vegas.Compile.ApplicationImageInvariants
import Vegas.Compile.ApplicationPlan
import Vegas.Compile.ApplicationService
import Vegas.Compile.ApplicationPlanCoverage
import Vegas.Compile.ApplicationPlanAllocation
import Vegas.Compile.ApplicationPlanOrigin
import Vegas.Compile.ApplicationGuardSoundness
import Vegas.Compile.BindingResolution
import Vegas.Compile.ConditionalOpeningValidation
import Vegas.Compile.ConditionalImage
import Vegas.Compile.ConditionalImageRefinement
import Vegas.Compile.PublicChoiceImage
import Vegas.Compile.SampleImage
import Vegas.Compile.SampleImageRefinement
import Vegas.Compile.ApplicationImageController
import Vegas.Compile.ConditionalImageController
import Vegas.Compile.ApplicationImageReadout
import Vegas.Compile.ApplicationImageRegistration
import Vegas.Compile.ApplicationImageBindingInclusion
import Vegas.Compile.ApplicationImageProvenance
import Vegas.Compile.ApplicationImageCoverage
import Vegas.Compile.ApplicationImageReadoutAvailability
import Vegas.Compile.SourceReadoutAvailability
import Vegas.Compile.BindingImageController
import Vegas.Compile.BindingImageExecution
import Vegas.Compile.ApplicationSampleExecution
import Vegas.Compile.PublicChoiceImageExecution
import Vegas.Compile.PublicChoicePhaseExecution
import Vegas.Compile.PublicChoiceSourceCoupling
import Vegas.Compile.BindingSourceCoupling
import Vegas.Compile.BindingPhaseExecution
import Vegas.Compile.ConditionalSourceCoupling
import Vegas.Compile.ConditionalExpirationSourceCoupling
import Vegas.Compile.ConditionalSnapshot
import Vegas.Compile.ConditionalPhaseExecution
import Vegas.Compile.ApplicationPolicy
import Vegas.Compile.ApplicationProfileContinuation
import Vegas.Compile.ApplicationContinuationReadout
import Vegas.Compile.ApplicationInitialReads
import Vegas.Compile.ApplicationForwardCheckpoint
import Vegas.Compile.ApplicationSampleForward
import Vegas.Compile.ApplicationBindingForward
import Vegas.Compile.ApplicationPublicChoiceForward
import Vegas.Compile.ApplicationOwnerPhase
import Vegas.Compile.ApplicationConditionalOwner
import Vegas.Compile.ApplicationConditionalForward
import Vegas.Compile.ApplicationForwardLaw
import Vegas.Compile.ApplicationChoiceTimeouts
import Vegas.Compile.ApplicationTimeoutForwardLaw
import Vegas.Compile.PublicResolution
import Vegas.Compile.ApplicationBindingDefault
import Vegas.Compile.ApplicationBindingTimeouts
import Vegas.Compile.BindingTimeoutCompilation
import Vegas.Compile.ApplicationBindingTimeoutRefinement
import Vegas.Compile.PublicChoiceResolution
import Vegas.Compile.ApplicationMessageRequirement
import Vegas.Compile.ApplicationWithholding
import Vegas.Compile.ApplicationPolicyFreshness
import Vegas.Compile.ApplicationCacheSeparation
import Vegas.Compile.ApplicationPolicyCache
import Vegas.Compile.ApplicationPhaseCaches
import Vegas.Compile.ApplicationPolicyLocality
import Vegas.Compile.ApplicationPolicyBindings
import Vegas.Compile.ApplicationPolicyProvenance
import Vegas.Compile.ApplicationImageRefinement
import Vegas.Compile.BindingImageRefinement
import Vegas.Compile.ApplicationImageOutcome
import Vegas.Compile.ApplicationImageStateRefinement
import Vegas.Compile.ApplicationSourcePublicAgreement
import Vegas.Compile.PublicationStateRefinement
import Vegas.Compile.ApplicationPlanRefinement
import Vegas.Compile.ApplicationTimeoutRefinement
import Vegas.Compile.ApplicationSourceOutcome
import Vegas.Compile.ApplicationPlanOutcome
import Vegas.Compile.SourceChoiceController
import Vegas.Compile.PublicGuard
import Vegas.Compile.DecisionSite
import Vegas.Compile.FieldMap
import Vegas.Compile.SourceAdequacy
import Vegas.Compile.SourceLaw
import Vegas.Compile.SourceExecution
import Vegas.Compile.SourceExecutionGraph
import Vegas.Compile.ApplicationOrder
import Vegas.Compile.ApplicationOrderTimeouts
import Vegas.Compile.ApplicationOrderPrefix
import Vegas.Compile.ApplicationCompletion
import Vegas.Compile.ApplicationDeadlines
import Vegas.Compile.ApplicationPlanDeadlines
import Vegas.Compile.ApplicationDeadlineInvariants
import Vegas.Compile.ApplicationImageClock
import Vegas.Compile.WindowedApplication
import Vegas.Compile.WindowedExpiry
import Vegas.Compile.WindowedExpiryResolution
import Vegas.Compile.WindowedRelayResolution
import Vegas.Compile.WindowedExpiryService
import Vegas.Compile.WindowedBlockService
import Vegas.Compile.WindowedDeliveryService
import Vegas.Compile.WindowedService
import Vegas.Compile.WindowedDeliveryAlignment
import Vegas.Compile.WindowedDeliveryProvenance
import Vegas.Compile.WindowedDeliveryAdmission
import Vegas.Compile.WindowedDeliveryReadiness
import Vegas.Compile.WindowedDeliveryPhase
import Vegas.Compile.WindowedDeliveryPrefix
import Vegas.Compile.WindowedDeliverySample
import Vegas.Compile.WindowedDeliverySampleCaches
import Vegas.Compile.WindowedDeliverySampleCheckpoint
import Vegas.Compile.WindowedDeliveryBindingCheckpoint
import Vegas.Compile.WindowedDeliveryPublicChoice
import Vegas.Compile.WindowedDeliveryPublicChoiceCheckpoint
import Vegas.Compile.WindowedDeliveryConditional
import Vegas.Compile.WindowedDeliveryConditionalCheckpoint
import Vegas.Compile.WindowedDeliveryIsolation
import Vegas.Compile.WindowedDeliveryPrivacy
import Vegas.Compile.WindowedPendingAdmission
import Vegas.Compile.WindowedReactionPrivacy
import Vegas.Compile.WindowedBlockAlignment
import Vegas.Compile.WindowedBlockDeterminism
import Vegas.Compile.WindowedOwnedBlock
import Vegas.Compile.WindowedOwnedPlayers
import Vegas.Compile.WindowedGatedExecution
import Vegas.Compile.WindowedOwnedPrivacy
import Vegas.Compile.WindowedOwnedCheckpoint
import Vegas.Compile.WindowedBlockPredraw
import Vegas.Compile.WindowedBlockIsolation
import Vegas.Compile.WindowedOwnerFrame
import Vegas.Compile.WindowedBindingAdmission
import Vegas.Compile.WindowedActivationFreshness
import Vegas.Compile.WindowedBlockSample
import Vegas.Compile.WindowedBlockSettlement
import Vegas.Compile.WindowedBlockProgress
import Vegas.Compile.WindowedBlockSourceCoupling
import Vegas.Compile.WindowedBindingSettlement
import Vegas.Compile.WindowedBindingBlock
import Vegas.Compile.WindowedConditionalBlock
import Vegas.Compile.WindowedConditionalCheckpoint
import Vegas.Compile.WindowedPublicChoiceBlock
import Vegas.Compile.WindowedCheckpoint
import Vegas.Compile.ApplicationBlockFallbacks
import Vegas.Compile.WindowedSourcePrefix
import Vegas.Compile.ApplicationPrefixShape
import Vegas.Compile.WindowedSourceCoverage
import Vegas.Compile.WindowedBindingAction
import Vegas.Compile.WindowedBindingPairing
import Vegas.Compile.WindowedBindingSubmission
import Vegas.Compile.WindowedNormalSuffix
import Vegas.Compile.WindowedBindingPrivacy
import Vegas.Compile.WindowedPublicChoiceReadiness
import Vegas.Compile.WindowedPublicChoiceSubmission
import Vegas.Compile.WindowedPublicChoiceInversion
import Vegas.Compile.WindowedConditionalInversion
import Vegas.Compile.WindowedSubmitWaitPairing
import Vegas.Compile.WindowedPublicChoicePrivacy
import Vegas.Compile.WindowedBindingCheckpoint
import Vegas.Compile.WindowedPublicChoiceCheckpoint
import Vegas.Compile.WindowedBindingExecution
import Vegas.Compile.WindowedBindingLocality
import Vegas.Compile.WindowedBindingReadiness
import Vegas.Compile.WindowedSampleCaches
import Vegas.Compile.WindowedBlockCaches
import Vegas.Compile.WindowedReferenceCaches
import Vegas.Compile.WindowedSampleCheckpoint
import Vegas.Compile.WindowedSamplePrivacy
import Vegas.Compile.WindowedForeignProvenance
import Vegas.Compile.WindowedBindingProvenance
import Vegas.Compile.WindowedBlockProvenance
import Vegas.Compile.WindowedContinuationReadout
import Vegas.Compile.WindowedConditionalOwner
import Vegas.Compile.ConditionalHead
import Vegas.Compile.ConditionalDisposition
import Vegas.Compile.WindowedConditionalCached
import Vegas.Compile.WindowedConditionalReadiness
import Vegas.Compile.WindowedConditionalSubmission
import Vegas.Compile.WindowedConditionalAdmission
import Vegas.Compile.WindowedConditionalInclusion
import Vegas.Compile.WindowedConditionalPrivacy
import Vegas.Compile.WindowedConditionalBlockPrivacy
import Vegas.Compile.WindowedSourcePrivacy
import Vegas.Compile.WindowedSourceInformation
import Vegas.Compile.WindowedPublicAction
import Vegas.Compile.WindowedDecisionCheckpoints
import Vegas.Compile.WindowedSourcePolicy
import Vegas.Compile.WindowedPolicyContinuation
import Vegas.Compile.WindowedSourceDecisionCoverage
import Vegas.Compile.WindowedPublicChoiceLaw
import Vegas.Compile.WindowedBindingLaw
import Vegas.Compile.WindowedBlockLaw
import Vegas.Compile.WindowedFocalBindingLaw
import Vegas.Compile.WindowedFocalPublicLaw
import Vegas.Compile.WindowedConditionalContinuation
import Vegas.Compile.WindowedDeviationLaw
import Vegas.Compile.WindowedMixedDeviation
import Vegas.Compile.WindowedReferenceLaw
import Vegas.Compile.WindowedConditionalLaw
import Vegas.Compile.WindowedBindingOwner
import Vegas.Compile.WindowedPublicChoiceOwner
import Vegas.Compile.WindowedReadoutProjection
import Vegas.Compile.WindowedBlockResolution
import Vegas.Compile.ApplicationRelayHistory
import Vegas.Compile.WindowedProjection
import Vegas.Compile.WindowedExecutionProjection
import Vegas.Compile.WindowedPolicyProjection
import Vegas.Compile.ApplicationDeadlineIndependence
import Vegas.Compile.ApplicationDeadlinePolicies
import Vegas.Compile.WindowedApplicationDeadline
import Vegas.Compile.WindowedApplicationInvariants
import Vegas.Compile.WindowedSourceSafety
import Vegas.Compile.WindowedApplicationCoverage
import Vegas.Compile.WindowedForwardLaw
import Vegas.Compile.WindowedSampleLaw
import Vegas.Compile.ApplicationPlanSampleLaw
import Vegas.Compile.WindowedExpiryStability
import Vegas.Compile.ApplicationResolvedBindings
import Vegas.Compile.ApplicationSampleFrames
import Vegas.Compile.ApplicationOrderPhase
import Vegas.Compile.ApplicationOrderCheckpoint
import Vegas.Compile.ApplicationOrderRefinement
import Vegas.Compile.SourceExecutionOutcome
import Vegas.Compile.SourceOutcome
import Vegas.Compile.SourceObservation
import Vegas.Compile.SourcePolicy
import Vegas.Compile.SealedMessages
import Vegas.Compile.SealedDecode
import Vegas.Compile.SealedExecution
import Vegas.Compile.SealedRules
import Vegas.Compile.SealedDecodeLaws
import Vegas.Compile.SealedRefinement
import Vegas.Compile.SealedSource
import Vegas.Compile.SealedTimeoutRefinement

/-!
# Compilation: checked Vegas programs and runtime components

`Compiler` lowers a `GraphProgram` / `WFProgram` into a canonical
`EventGraph.Graph` with typed fields, causal dependencies, guarded commit
nodes, exact finite laws, and terminal payoff projections.
Structural application plans generate binding, chance, and publication instructions.
Arbitrary supported public-message executions refine reachable graph states;
completed runs have the public outcome of a written-order source execution.
The generated serial reference execution finishes with the independent source
public-outcome law, under explicit initial-read and binding-origin conditions.
The fixed windowed block service covers sequential source prefixes and completes
under arbitrary unilateral replacement, with certified fallback and relay conditions.
For pure raw replacements, source-view information preservation yields consistent
decision kernels and a total source policy assembled along the original syntax.
Every actual focal source edge selects its recorded action through this root
policy. Exact block laws compose into the original source evaluator's joint
completion/public-output law with only the focal source policy replaced.
Predrawing finite executions extends this law to arbitrary randomized raw
replacements as finite mixtures of source deviations. The native operational
game consequently transports public-outcome bounds independently of the
deviator's preferences. The reference-profile law for this same block service
preserves the original source profile without changing any coordinate.
The pending-message delivery service has complete binding, public-choice, and
conditional (including copied-conditional) block successors under its explicit
unchanged-relay and provenance premises. Whole-prefix extraction, randomized
deviation transport, and adaptive scheduling remain separate obligations.
-/
