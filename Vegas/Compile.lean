/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.Compiler
import Vegas.Compile.FieldMap
import Vegas.Compile.RevealAccounting
import Vegas.Compile.SourceView
import Vegas.Compile.SourceChoice
import Vegas.Compile.SourceLaw
import Vegas.Compile.DecisionSite
import Vegas.Compile.SourcePolicy
import Vegas.Compile.SourceBacktranslation
import Vegas.Compile.SourceDisclosureReads
import Vegas.Compile.SourceExecutionLaw
import Vegas.Compile.SourceExecutionGraph
import Vegas.Compile.SourceExecutionOutcome
import Vegas.Compile.SourceOutcomeExecution
import Vegas.Compile.SourceCorrespondence
import Vegas.Compile.SealedMessages
import Vegas.Compile.SealedReadOrigin
import Vegas.Compile.SealedDecode
import Vegas.Compile.SealedExecution
import Vegas.Compile.SealedRules
import Vegas.Compile.SealedResolutionAdmission
import Vegas.Compile.SealedDecodeLaws
import Vegas.Compile.SealedRefinement
import Vegas.Compile.SealedSource
import Vegas.Compile.SealedCompiler
import Vegas.Compile.SealedView
import Vegas.Compile.SealedPolicy
import Vegas.Compile.SealedResolutionPolicy
import Vegas.Compile.SealedCandidatePolicy
import Vegas.Compile.SealedCandidateInputs
import Vegas.Compile.SealedCandidateReadBound
import Vegas.Compile.SealedCandidateReplay
import Vegas.Compile.SealedCandidateSourceExtraction
import Vegas.Compile.SealedCandidateHonestRound
import Vegas.Compile.SealedCandidateSettlement
import Vegas.Compile.SealedResolutionClosure
import Vegas.Compile.SealedResolvedStore
import Vegas.Compile.SealedResolvedReads
import Vegas.Compile.SealedPublicOutcome
import Vegas.Compile.SealedSettlement
import Vegas.Compile.SealedPolicyProgress
import Vegas.Compile.SealedPhaseCount
import Vegas.Compile.SealedPolicyDeadline
import Vegas.Compile.SealedTermination
import Vegas.Compile.SealedResolutionPrivacy
import Vegas.Compile.SealedResolutionReadBound
import Vegas.Compile.SealedResolutionReplay
import Vegas.Compile.SealedResolutionCylinder
import Vegas.Compile.SealedAssignedReplay
import Vegas.Compile.SealedHonestCompletion
import Vegas.Compile.SealedSourceExtraction
import Vegas.Compile.SealedDisclosureRun
import Vegas.Compile.SealedSourceRealization
import Vegas.Compile.SealedSourceAssignment
import Vegas.Compile.SealedSourceRestriction
import Vegas.Compile.SealedHonestSource
import Vegas.Compile.SealedHonestCylinder
import Vegas.Compile.SealedHonestLikelihood
import Vegas.Compile.SealedHonestNative
import Vegas.Compile.SealedHonestRound
import Vegas.Compile.SealedSourceCylinder
import Vegas.Compile.SealedNativeLikelihood
import Vegas.Compile.SealedContinuation
import Vegas.Compile.SealedRandomizedCoupling
import Vegas.Compile.SealedRoundCoupling
import Vegas.Compile.SealedStoppingCoupling
import Vegas.Compile.SealedSourceInputs
import Vegas.Compile.SealedViewAgreement
import Vegas.Compile.SealedReplay
import Vegas.Compile.SealedPublication
import Vegas.Compile.SealedPolicyKnowledge
import Vegas.Compile.SealedTimeoutRefinement

/-!
# Compilation: the active sealed-message edge

`Compiler` lowers a checked `WFProgram` to a canonical event graph with typed
fields, causal dependencies, guarded commit nodes, finite laws, and terminal
payoff projections. `SealedCompiler` then emits one explicit sealed-message
rule for each graph node, retaining commitments and openings as separate
protocol phases. The refinement theorems cover arbitrary finite native actions,
including malformed submissions, replay, delivery, inclusion, and withholding:
every resulting prefix decodes to a reachable graph state, and a terminal state
reconstructs a written-order source execution.

The non-resolving runtime policy game has the same support-level source
guarantee. The generic GameTheory `MixtureSimulationOn` interface expresses a
stronger exact-outcome edge through an honest law and finite-mixture
backtranslation for considered unilateral deviations; it is not by itself an
instantiated compiler result or a constructed exact post-timeout
backtranslation.

`SealedHonestRound` discharges the original all-compiled source law for the
resolving pending-message driver under periodic service and the checked timeout
window. The unilateral coupling retains the exact source-mixture and native
marginals. The round game's concrete utility simulation uses conditional
timeout utility comparisons in addition to normal utility agreement; their
program-specific incentive analysis remains an explicit obligation.
`SealedPublicOutcome` reconstructs every completed public settlement, including
after defaults, as the public values and payout of a legal source execution.
That support witness may change private choices and does not replace the
commitment-preserving witness in the strategic coupling.

`SealedCandidateHonestRound` proves the written-source payout law for the
candidate-service instantiation of the shared stopped driver. Completion and
absence of timeouts follow from deadline-relative service. Arbitrary candidate
selection and unopenable commitments are not covered by the unilateral coupling
for the registered-site service.
`SealedCandidateSourceExtraction` constructs a written-source replacement from
acceptance-time replay and proves consistency of its complete source runs.
The joint law identifying these replays with the original native execution
remains separate from that source-policy construction.
-/
