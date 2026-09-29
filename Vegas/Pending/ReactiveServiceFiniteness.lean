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

end Vegas.EventGraphRuntime
