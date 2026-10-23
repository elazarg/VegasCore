/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveResponseEvaluation

/-! # Behavioral play of a response menu as the canonical kernel

The law of the states that behavioral play of a response menu reaches from a
history is the iterate of the canonical control kernel of the decoded profile,
started at that history's state
(`Interaction.ReactiveApplication.ResponseMenu.run_map_state_eq_iterate`).
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}

namespace ResponseMenu

variable [Fintype Principal] (menu : app.ResponseMenu) (initial : PMF app.State)
  (horizon : Nat) (scheduler : app.Scheduler)

/-- The states behavioral play of a response menu reaches are those the
canonical kernel of the decoded profile reaches. -/
theorem run_map_state_eq_iterate
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (fuel : Nat) (history : (menu.protocol initial horizon scheduler).History) :
    ((menu.information initial horizon scheduler).runBehavioralFrom profile fuel history).map
        ExecutionProtocol.History.state =
      (fun law => law.bind (app.controlStep initial horizon scheduler
        (menu.decodeProfile initial horizon scheduler profile)))^[fuel]
        (PMF.pure history.state) := by
  have encoded : (fun who => app.encodePolicy
      (menu.decodeProfile initial horizon scheduler profile who)) =
        fun who => menu.embedPolicy initial horizon scheduler who (profile who) := by
    funext who
    exact app.encode_decodePolicy _
  calc
    _ = (((menu.information initial horizon scheduler).runBehavioralFrom profile fuel history).map
          (menu.toRawHistory initial horizon scheduler)).map
            ExecutionProtocol.History.state := by
      rw [PMF.map_comp]
      rfl
    _ = ((app.information initial horizon scheduler).runBehavioralFrom
          (fun who => menu.embedPolicy initial horizon scheduler who (profile who)) fuel
          (menu.toRawHistory initial horizon scheduler history)).map
            ExecutionProtocol.History.state := by
      rw [menu.run_embed]
    _ = _ := by
      rw [← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom
        (app.information initial horizon scheduler) (app.singleMover initial horizon scheduler),
        ← encoded, app.run_map_state]
      rfl

end ResponseMenu

end Interaction.ReactiveApplication
