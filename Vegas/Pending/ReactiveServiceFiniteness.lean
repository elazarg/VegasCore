/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveServiceEvaluation
import Interaction.ReactiveRoundsFiniteness

/-! # Finitely branching service plans

With a finitely branching leak rule and network policy, a fixed service plan
run by finitely branching players has a finitely supported execution law.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem interactionStep_support_finite (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) [leaks.FiniteSupport]
    {players : Player → (runtime.reactiveApplication leaks).Policy}
    (finite : ∀ who, ReactiveApplication.Policy.FiniteSupport _ (players who))
    (network : runtime.NetworkPolicy leaks) [network.FiniteSupport]
    (instruction : ServiceInstruction graph)
    (execution : (runtime.reactiveApplication leaks).Execution) :
    (runtime.interactionStep leaks players network instruction execution).support.Finite :=
  bind_support_finite (runtime.interactionInstruction_support_finite leaks network _ _ _)
    fun command _ => (runtime.reactiveApplication leaks).dispatch_support_finite finite command
      execution

theorem runInteractionPlan_support_finite (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) [leaks.FiniteSupport]
    {players : Player → (runtime.reactiveApplication leaks).Policy}
    (finite : ∀ who, ReactiveApplication.Policy.FiniteSupport _ (players who))
    (network : runtime.NetworkPolicy leaks) [network.FiniteSupport] :
    ∀ (plan : List (ServiceInstruction graph))
      (execution : (runtime.reactiveApplication leaks).Execution),
      (runtime.runInteractionPlan leaks players network plan execution).support.Finite
  | [], _ => by simp [runInteractionPlan]
  | instruction :: rest, execution =>
      bind_support_finite
        (runtime.interactionStep_support_finite leaks finite network instruction execution)
        fun next _ => runInteractionPlan_support_finite runtime leaks finite network rest next

/-- A service plan with no discretionary network turns has finite execution
support even when the unused network policy has infinite support. Player
responses and pending observations still need finite support. -/
theorem runInteractionPlan_support_finite_of_no_wire (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) [leaks.FiniteSupport]
    {players : Player → (runtime.reactiveApplication leaks).Policy}
    (finite : ∀ who, ReactiveApplication.Policy.FiniteSupport _ (players who))
    (network : runtime.NetworkPolicy leaks) (plan : List (ServiceInstruction graph))
    (reserved : ServiceInstruction.wire ∉ plan)
    (execution : (runtime.reactiveApplication leaks).Execution) :
    (runtime.runInteractionPlan leaks players network plan execution).support.Finite := by
  induction plan generalizing execution with
  | nil => simp [runInteractionPlan]
  | cons instruction rest ih =>
      have current : instruction ≠ .wire := by
        intro same
        exact reserved (by simp [same])
      have remaining : ServiceInstruction.wire ∉ rest := by
        intro member
        exact reserved (List.mem_cons_of_mem _ member)
      apply bind_support_finite
      · exact bind_support_finite
          (runtime.interactionInstruction_support_finite_of_not_wire leaks network _ _
            instruction current)
          fun command _ =>
            (runtime.reactiveApplication leaks).dispatch_support_finite finite command execution
      · exact fun next _ => ih remaining next

end Vegas.EventGraphRuntime
