/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRoster

/-! # Policy independent service commands
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

theorem servicePlan_players_eq
    (left right : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks)
    (plan : List (ServiceInstruction (graph setup)))
    (noWire : ServiceInstruction.wire ∉ plan)
    (noPlayers : ∀ who, ServiceInstruction.player who ∉ plan)
    (execution : (application setup leaks).Execution) :
    (runtime setup).runInteractionPlan leaks left network plan execution =
      (runtime setup).runInteractionPlan leaks right network plan execution := by
  induction plan generalizing execution with
  | nil => rfl
  | cons instruction rest ih =>
      have step : (runtime setup).interactionStep leaks left network instruction execution =
          (runtime setup).interactionStep leaks right network instruction execution := by
        cases instruction with
        | player who => exact False.elim (noPlayers who (by simp))
        | wire => exact False.elim (noWire (by simp))
        | sample event | tick | expire event =>
            simp only [EventGraphRuntime.interactionStep, EventGraphRuntime.interactionInstruction,
              PMF.pure_bind, ReactiveApplication.dispatch,
              ReactiveApplication.Command.actor?]
            apply bind_congr_on_support _
            intro next _
            rfl
        | includeLatest event owner =>
            unfold EventGraphRuntime.interactionStep EventGraphRuntime.interactionInstruction
            simp only [PMF.pure_bind]
            unfold EventGraphRuntime.reactiveLatest
            split <;> rfl
      simp only [EventGraphRuntime.runInteractionPlan, step]
      apply bind_congr_on_support _
      intro next _
      exact ih (fun member => noWire (List.mem_cons_of_mem _ member))
        (fun who member => noPlayers who (List.mem_cons_of_mem _ member)) next

end Vegas
