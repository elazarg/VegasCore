/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedResolutionTermination
import Vegas.Compile.SealedResolutionAdmission
import Vegas.Compile.SealedResolutionPolicy

/-! # Termination of compiled sealed resolution

The compiler's fragment certificate discharges the resolution runtime's two
program-admission premises. Thus arbitrary player and wire policies terminate
from the canonical initial state within the finite bound determined by the
compiled graph and timeout window. No roster coverage or wire-service premise
is required.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- The resolving runtime for a checked compiled source completes within
`nodeCount * (window + 1)` rounds, under arbitrary policies. -/
theorem resolvingRuntime_runRounds_complete
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (principals : List Player) (serviceSlots : Nat)
    (players : Player →
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy)
    (environment :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.WirePolicy)
    (next :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hnext : next ∈
      ((compilation.supported.resolvingRuntime nullValue window).runRounds
        principals serviceSlots players environment
        ((ToEventGraph.compile source.core).graph.nodeCount * (window + 1))
        (MessageApplication.PolicyExecution.initial _
          (MessageApplication.State.initial _
            (compilation.supported.resolvingRuntime nullValue window).initial))).support) :
    (compilation.supported.resolvingRuntime nullValue window).complete
      next.native.application.visible = true := by
  apply (compilation.supported.resolvingRuntime nullValue window).runRounds_complete
    (fun node rule hrule =>
      compilation.supported.compile_rule_kind_ne_disabled hrule)
    (fun node rule hrule prerequisite hprerequisite =>
      compilation.supported.compile_rule_requires_lt hrule hprerequisite)
    principals serviceSlots players environment
    (MessageApplication.PolicyExecution.initial _
      (MessageApplication.State.initial _
        (compilation.supported.resolvingRuntime nullValue window).initial)) next
    (Interaction.SealedResolution.PublicState.ClockBounded.initial _)
  simpa [SealedFragment.resolvingRuntime, SealedFragment.compile,
    EventGraph.Graph.nodeOrder] using hnext

end Vegas.SealedCompilation
