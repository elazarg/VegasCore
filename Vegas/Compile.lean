/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.Compiler
import Vegas.Compile.FieldMap
import Vegas.Compile.SourceView
import Vegas.Compile.SourceLaw
import Vegas.Compile.DecisionSite
import Vegas.Compile.SourcePolicy
import Vegas.Compile.SourceBacktranslation
import Vegas.Compile.SourceDisclosureReads
import Vegas.Compile.SourceExecutionLaw
import Vegas.Compile.SourceExecutionGraph
import Vegas.Compile.SourceExecutionOutcome
import Vegas.Compile.SourceCorrespondence
import Vegas.Compile.SealedMessages
import Vegas.Compile.SealedDecode
import Vegas.Compile.SealedExecution
import Vegas.Compile.SealedRules
import Vegas.Compile.SealedDecodeLaws
import Vegas.Compile.SealedRefinement
import Vegas.Compile.SealedSource
import Vegas.Compile.SealedCompiler
import Vegas.Compile.SealedView
import Vegas.Compile.SealedPolicy
import Vegas.Compile.SealedResolutionPolicy
import Vegas.Compile.SealedResolutionPrivacy
import Vegas.Compile.SealedResolutionReadBound
import Vegas.Compile.SealedResolutionReplay
import Vegas.Compile.SealedResolutionCylinder
import Vegas.Compile.SealedSourceExtraction
import Vegas.Compile.SealedSourceRealization
import Vegas.Compile.SealedSourceAssignment
import Vegas.Compile.SealedSourceRestriction
import Vegas.Compile.SealedSourceCylinder
import Vegas.Compile.SealedNativeLikelihood
import Vegas.Compile.SealedContinuation
import Vegas.Compile.SealedRandomizedCoupling
import Vegas.Compile.SealedSourceInputs
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

The runtime policy game has the same support-level source guarantee. Exact
strategic preservation is exposed through `SealedCompilation.StrategicCertificate`:
the target runtime must supply its honest outcome law and finite-mixture
backtranslation for considered unilateral deviations. Nash and epsilon-Nash
transfer then follow by direct delegation to the runtime-independent
GameTheory theorem. A concrete pending-message backtranslation remains an
explicit research obligation rather than an implicit claim.
-/
