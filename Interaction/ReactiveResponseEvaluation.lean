/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveResponseEmbedding
import Interaction.ReactiveRounds

/-! # Complete native evaluation of finite-menu behavioral profiles -/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)

def decodeProfile
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who) :
    Principal → app.Policy :=
  fun who => app.decodePolicy (menu.embedPolicy initial horizon scheduler who (profile who))

theorem decodeProfile_update
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (who : Principal)
    (alternative : (menu.information initial horizon scheduler).BehavioralPolicy who) :
    menu.decodeProfile initial horizon scheduler (GameTheory.Profile.update
        (sig := (menu.information initial horizon scheduler).behavioralSignature)
          profile who alternative) =
      Function.update (menu.decodeProfile initial horizon scheduler profile) who
        (app.decodePolicy (menu.embedPolicy initial horizon scheduler who alternative)) := by
  funext other past view
  by_cases same : other = who
  · subst other
    simp only [decodeProfile, GameTheory.Profile.update, Function.update_self]
  · simp only [decodeProfile, GameTheory.Profile.update, Function.update_of_ne same]

variable [Fintype Principal]

theorem run_eq_finish
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (fuel : Nat) (history : (menu.protocol initial horizon scheduler).History)
    (enough : app.rank horizon history.state ≤ fuel) :
    ((menu.information initial horizon scheduler).runBehavioralFrom profile fuel history).map
        History.state =
      app.finish initial horizon scheduler (menu.decodeProfile initial horizon scheduler profile)
        history.state := by
  have encoded : (fun who => app.encodePolicy
      (menu.decodeProfile initial horizon scheduler profile who)) =
        fun who => menu.embedPolicy initial horizon scheduler who (profile who) := by
    funext who
    exact app.encode_decodePolicy _
  calc
    _ = (((menu.information initial horizon scheduler).runBehavioralFrom profile fuel history).map
          (menu.toRawHistory initial horizon scheduler)).map History.state := by
      rw [FinDist.map_comp]
      rfl
    _ = ((app.information initial horizon scheduler).runBehavioralFrom
          (fun who => menu.embedPolicy initial horizon scheduler who (profile who)) fuel
          (menu.toRawHistory initial horizon scheduler history)).map History.state := by
      rw [menu.run_embed]
    _ = _ := by
      rw [← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom
        (app.information initial horizon scheduler) (app.singleMover initial horizon scheduler),
        ← encoded, app.run_map_state]
      exact app.iterate_eq_finish initial horizon scheduler _ fuel _ enough

end Interaction.ReactiveApplication.ResponseMenu
