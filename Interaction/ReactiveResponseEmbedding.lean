/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveResponseMenu

/-! # Exact continuation laws for an explicit response-menu instance

Embedding is playerwise and leaves observations and responses unchanged. From
every legal instance history, its complete continuation history law is the
unrestricted runtime law under the embedded policies. This includes the actual
remaining time, arbitrary private observations and off-path instance histories.
It does not cover policies choosing outside the supplied menus.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (menu : app.ResponseMenu)
  (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)

def embedPolicy (who : Principal)
    (policy : (menu.information initial horizon scheduler).BehavioralPolicy who) :
    (app.information initial horizon scheduler).BehavioralPolicy who := fun info =>
  (policy info).map (menu.rawChoice initial horizon scheduler who info)

variable [Fintype Principal]

theorem behavioralJoint_embed
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (history : (menu.protocol initial horizon scheduler).History)
    (running : ¬ app.terminal history.state) :
    (app.information initial horizon scheduler).behavioralJoint
        (fun who => menu.embedPolicy initial horizon scheduler who (profile who))
        (menu.toRawTrace initial horizon scheduler history.trace) running =
      ((menu.information initial horizon scheduler).behavioralJoint profile
        history.trace running).map fun joint =>
          ⟨joint.1, menu.legal_raw initial horizon scheduler joint.2⟩ := by
  rcases history with ⟨state, trace⟩
  cases trace <;>
    simp only [InformationModel.behavioralJoint, embedPolicy, FinDist.pi_map, FinDist.map_comp] <;>
    rfl

/-- The map retains the complete history, rather than just public outcomes. -/
theorem run_embed
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (fuel : Nat) (history : (menu.protocol initial horizon scheduler).History) :
    ((menu.information initial horizon scheduler).runBehavioralFrom profile fuel history).map
        (menu.toRawHistory initial horizon scheduler) =
      (app.information initial horizon scheduler).runBehavioralFrom
        (fun who => menu.embedPolicy initial horizon scheduler who (profile who)) fuel
        (menu.toRawHistory initial horizon scheduler history) := by
  induction fuel generalizing history with
  | zero => exact FinDist.map_pure _ _
  | succ fuel ih =>
      by_cases stopped : app.terminal history.state
      · rw [InformationModel.runBehavioralFrom_of_terminal _ _ _ stopped,
          InformationModel.runBehavioralFrom_of_terminal _ _ _ stopped, FinDist.map_pure]
      · rw [InformationModel.runBehavioralFrom_succ_of_not_terminal _ _ _ stopped,
          InformationModel.runBehavioralFrom_succ_of_not_terminal _ _ _ stopped]
        simp only [toRawHistory]
        rw [menu.behavioralJoint_embed initial horizon scheduler profile history stopped]
        rw [FinDist.map_bind, FinDist.bind_map]
        apply FinDist.bind_congr
        intro joint _
        rw [FinDist.map_bindOnSupport]
        apply FinDist.bindOnSupport_congr
        intro target realized
        exact ih (history.extend joint.2 realized)

end Interaction.ReactiveApplication.ResponseMenu
