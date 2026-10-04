/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRosterEvaluation
import Interaction.ReactiveRestrictedContinuation

/-! # Initialized restricted service evaluation
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

variable [Fintype Player]

theorem roster_restrict_complete_state
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (menu : (application setup leaks).ResponseMenu)
    (players : Player → (application setup leaks).Policy)
    (covered : ∀ who, menu.Admissible (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) who (players who)) :
    ((menu.information (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).runBehavioral
      (fun who => menu.restrictPolicy (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network) who (players who))
      (2 * (rosterPlan setup rosters).length + 1)).map History.state =
      ((initialLaw setup).bind fun state =>
        (runtime setup).runInteractionPlan leaks players network (rosterPlan setup rosters)
          (ReactiveApplication.Execution.initial (application setup leaks) state)).map
        (fun final => some ⟨0, none, final⟩) := by
  rw [InformationModel.runBehavioral, menu.run_restrict_eq_finish _ _ _ players covered
    _ _ (by rfl)]
  have plan := roster_roundsFrom setup leaks rosters network players
    (rosterPlan setup rosters).length (Nat.le_refl _)
  rw [List.take_length] at plan
  rw [← plan]
  simp only [ReactiveApplication.finish, ReactiveApplication.roundsFrom, PMF.map_bind]
  rfl

end Vegas
