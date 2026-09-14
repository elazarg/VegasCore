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

/-! # Termination of certified graph resolution

A graph fragment certificate discharges the resolution runtime's two
program-admission premises. Thus arbitrary player and wire policies terminate
from the canonical initial state within the finite bound determined by the
graph and timeout window. No roster coverage or wire-service premise
is required.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- The resolving runtime for a certified graph fragment completes at every
budget of at least `nodeCount * (window + 1)` rounds, under arbitrary policies.
Extra budget preserves the same early-stopping result. -/
theorem resolvingRuntime_runRounds_complete
    (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat)
    (principals : List Player) (serviceSlots : Nat)
    (players : Player →
      (supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy)
    (environment :
      (supported.resolvingRuntime nullValue window).messageApplication.WirePolicy)
    (total : Nat)
    (hbound : G.nodeCount * (window + 1) ≤ total)
    (next :
      (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hnext : next ∈
      ((supported.resolvingRuntime nullValue window).roundDriver.runRounds
        principals serviceSlots players environment
        total
        (MessageApplication.PolicyExecution.initial _
          (MessageApplication.State.initial _
            (supported.resolvingRuntime nullValue window).initial))).support) :
    (supported.resolvingRuntime nullValue window).complete
      next.native.application.visible = true := by
  let runtime := supported.resolvingRuntime nullValue window
  apply runtime.runRounds_complete runtime.handle_records
    (fun node rule hrule => supported.compile_rule_kind_ne_disabled hrule)
    (fun node rule hrule prerequisite hprerequisite =>
      supported.compile_rule_requires_lt hrule hprerequisite)
    principals serviceSlots players environment total ?_
    (MessageApplication.PolicyExecution.initial _
      (MessageApplication.State.initial _ runtime.initial)) next
    (SealedResolution.PublicState.ClockBounded.initial _) hnext
  simpa [runtime, SealedFragment.resolvingRuntime, SealedFragment.compile,
    EventGraph.Graph.nodeOrder] using hbound

/-- The candidate runtime for a certified graph fragment completes at every
budget of at least `nodeCount * (window + 1)` rounds, under arbitrary policies.
Extra budget preserves the same early-stopping result. -/
theorem candidateRuntime_runRounds_complete
    (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat)
    (principals : List Player) (serviceSlots : Nat)
    (players : Player →
      (supported.resolvingRuntime
        nullValue window).candidateApplication.PlayerPolicy)
    (environment :
      (supported.resolvingRuntime nullValue window).candidateApplication.WirePolicy)
    (total : Nat)
    (hbound : G.nodeCount * (window + 1) ≤ total)
    (next :
      (supported.resolvingRuntime
        nullValue window).candidateApplication.PolicyExecution)
    (hnext : next ∈
      ((supported.resolvingRuntime nullValue window).candidateRoundDriver.runRounds
        principals serviceSlots players environment
        total
        (MessageApplication.PolicyExecution.initial _
          (MessageApplication.State.initial _
            (supported.resolvingRuntime nullValue window).candidateInitial))).support) :
    (supported.resolvingRuntime nullValue window).complete
      next.native.application.visible = true := by
  let runtime := supported.resolvingRuntime nullValue window
  apply runtime.runRounds_complete runtime.candidateHandle_records
    (fun node rule hrule => supported.compile_rule_kind_ne_disabled hrule)
    (fun node rule hrule prerequisite hprerequisite =>
      supported.compile_rule_requires_lt hrule hprerequisite)
    principals serviceSlots players environment total ?_
    (MessageApplication.PolicyExecution.initial _
      (MessageApplication.State.initial _ runtime.candidateInitial)) next
    (SealedResolution.PublicState.ClockBounded.initial _) hnext
  simpa [runtime, SealedFragment.resolvingRuntime, SealedFragment.compile,
    EventGraph.Graph.nodeOrder] using hbound

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.candidateRuntime_runRounds_complete'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.candidateRuntime_runRounds_complete
