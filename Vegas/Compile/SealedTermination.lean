/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedResolutionTermination
import Interaction.SealedCandidateRounds
import Interaction.SealedCandidateBinding
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

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- The resolving runtime for a checked compiled source completes at every
budget of at least `nodeCount * (window + 1)` rounds, under arbitrary policies.
Extra budget preserves the same early-stopping result. -/
theorem resolvingRuntime_runRounds_complete
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (principals : List Player) (serviceSlots : Nat)
    (players : Player →
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy)
    (environment :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.WirePolicy)
    (total : Nat)
    (hbound : (ToEventGraph.compile source.core).graph.nodeCount * (window + 1) ≤ total)
    (next :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hnext : next ∈
      ((compilation.supported.resolvingRuntime nullValue window).roundDriver.runRounds
        principals serviceSlots players environment
        total
        (MessageApplication.PolicyExecution.initial _
          (MessageApplication.State.initial _
            (compilation.supported.resolvingRuntime nullValue window).initial))).support) :
    (compilation.supported.resolvingRuntime nullValue window).complete
      next.native.application.visible = true := by
  let runtime := compilation.supported.resolvingRuntime nullValue window
  apply runtime.runRounds_complete runtime.handle_records
    (fun node rule hrule => compilation.supported.compile_rule_kind_ne_disabled hrule)
    (fun node rule hrule prerequisite hprerequisite =>
      compilation.supported.compile_rule_requires_lt hrule hprerequisite)
    principals serviceSlots players environment total ?_
    (MessageApplication.PolicyExecution.initial _
      (MessageApplication.State.initial _ runtime.initial)) next
    (SealedResolution.PublicState.ClockBounded.initial _) hnext
  simpa [runtime, SealedFragment.resolvingRuntime, SealedFragment.compile,
    EventGraph.Graph.nodeOrder] using hbound

/-- The candidate runtime for a checked compiled source completes at every
budget of at least `nodeCount * (window + 1)` rounds, under arbitrary policies.
Extra budget preserves the same early-stopping result. -/
theorem candidateRuntime_runRounds_complete
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (principals : List Player) (serviceSlots : Nat)
    (players : Player →
      (compilation.supported.resolvingRuntime
        nullValue window).candidateApplication.PlayerPolicy)
    (environment :
      (compilation.supported.resolvingRuntime nullValue window).candidateApplication.WirePolicy)
    (total : Nat)
    (hbound : (ToEventGraph.compile source.core).graph.nodeCount * (window + 1) ≤ total)
    (next :
      (compilation.supported.resolvingRuntime
        nullValue window).candidateApplication.PolicyExecution)
    (hnext : next ∈
      ((compilation.supported.resolvingRuntime nullValue window).candidateRoundDriver.runRounds
        principals serviceSlots players environment
        total
        (MessageApplication.PolicyExecution.initial _
          (MessageApplication.State.initial _
            (compilation.supported.resolvingRuntime nullValue window).candidateInitial))).support) :
    (compilation.supported.resolvingRuntime nullValue window).complete
      next.native.application.visible = true := by
  let runtime := compilation.supported.resolvingRuntime nullValue window
  apply runtime.runRounds_complete runtime.candidateHandle_records
    (fun node rule hrule => compilation.supported.compile_rule_kind_ne_disabled hrule)
    (fun node rule hrule prerequisite hprerequisite =>
      compilation.supported.compile_rule_requires_lt hrule hprerequisite)
    principals serviceSlots players environment total ?_
    (MessageApplication.PolicyExecution.initial _
      (MessageApplication.State.initial _ runtime.candidateInitial)) next
    (SealedResolution.PublicState.ClockBounded.initial _) hnext
  simpa [runtime, SealedFragment.resolvingRuntime, SealedFragment.compile,
    EventGraph.Graph.nodeOrder] using hbound

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.candidateRuntime_runRounds_complete'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.candidateRuntime_runRounds_complete
