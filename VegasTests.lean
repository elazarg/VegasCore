/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.Language
import VegasTests.GuardValidation
import VegasTests.CoreFinite
import VegasTests.PendingSource
import VegasTests.PendingExecution
import VegasTests.PendingOutcome
import VegasTests.PendingReplay
import VegasTests.PendingPolicies
import VegasTests.PendingSnapshots
import VegasTests.PendingRelease
import VegasTests.PendingReleaseExamples
import VegasTests.PendingChoiceLock
import VegasTests.PendingWithholding
import VegasTests.PendingWithholdingSource
import VegasTests.PendingTimeout
import VegasTests.PendingTimeoutPolicies
import VegasTests.PendingTimeoutSource
import VegasTests.PendingTimeoutHiding
import VegasTests.SealedCompiler
import VegasTests.PendingDisclosureIncentive
import VegasTests.PendingStages
import VegasTests.SourceGraph
import VegasTests.SourceQuitPrefix
import VegasTests.SourceRestriction
import VegasTests.SealedPolicy
import VegasTests.SealedReplay
import VegasTests.SealedResolution
import VegasTests.SealedResolutionPolicy
import VegasTests.SealedPhaseCount
import VegasTests.SealedPolicyDeadline
import VegasTests.SealedRounds
import VegasTests.SealedPublicOutcome
import VegasTests.SealedPublicSettlement
import VegasTests.SealedPayout
import VegasTests.SealedProfilePayout
import VegasTests.SealedCandidates
import VegasTests.SealedCandidateReady
import VegasTests.SealedCandidateDeadline
import VegasTests.SealedCandidatePrefix
import VegasTests.SealedPublicUtility
import VegasTests.SealedResolutionReadBound
import VegasTests.SealedSourceExtraction
import VegasTests.GraphPublicPrefix
import VegasTests.GraphRestriction
import VegasTests.SealedResolutionCylinder
import VegasTests.GraphMessages
import VegasTests.GraphMessagePolicies
import VegasTests.FailureGame
import VegasTests.ResultExpressions
import VegasTests.SourceSemantics
import VegasTests.SourceSetup

/-! # Regression tests for source, graph, and public-message execution

The full failure-aware source and typed graph have mixed-feature execution
tests. Candidate-backend tests concern the restricted `WFProgram` theorem;
they do not establish the full typed host's pending-message strategic law.
-/
