/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.Compiler
import Vegas.Compile.SealedMessages
import Vegas.Compile.SealedDecode
import Vegas.Compile.SealedExecution
import Vegas.Compile.SealedRules
import Vegas.Compile.SealedDecodeLaws
import Vegas.Compile.SealedRefinement
import Vegas.Compile.SealedSource
import Vegas.Compile.SealedCompiler
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
