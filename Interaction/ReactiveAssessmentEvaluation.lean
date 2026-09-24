/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveResponseEvaluation
import GameTheory.Protocol.BehavioralAssessment

/-! # Assessment continuation values in the bounded interaction evaluator -/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)

theorem context_value_finish
    (assessment : (menu.information initial horizon scheduler).BehavioralAssessment)
    (who : Principal) (site : (menu.information initial horizon scheduler).InformationSite who)
    (payoff : app.ProtocolState → ℝ)
    (alternative : (menu.information initial horizon scheduler).BehavioralPolicy who) :
    (assessment.continuationContext site (fun history => payoff history.state)
      (2 * horizon + 1)).value alternative =
      (assessment.belief who site).expect (fun history =>
        (app.finish initial horizon scheduler
          (menu.decodeProfile initial horizon scheduler
            (Profile.update
            (sig := (menu.information initial horizon scheduler).behavioralSignature)
              assessment.strategy who alternative)) history.1.state).expect payoff) := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value, FinDist.expect_bind]
  apply FinDist.expect_congr
  intro history _
  have bound := app.trace_bound initial horizon scheduler
    (menu.toRawTrace initial horizon scheduler history.1.trace)
  have law := menu.run_eq_finish initial horizon scheduler
    (Profile.update
            (sig := (menu.information initial horizon scheduler).behavioralSignature)
      assessment.strategy who alternative) (2 * horizon + 1) history.1 (by omega)
  have value := congrArg (fun law : FinDist app.ProtocolState => law.expect payoff) law
  rw [FinDist.expect_map] at value
  exact value

theorem context_value_of_known_state
    (assessment : (menu.information initial horizon scheduler).BehavioralAssessment)
    (who : Principal) (site : (menu.information initial horizon scheduler).InformationSite who)
    (payoff : app.ProtocolState → ℝ)
    (alternative : (menu.information initial horizon scheduler).BehavioralPolicy who)
    (state : app.ProtocolState)
    (known : ∀ history : (menu.information initial horizon scheduler).InformationHistory who site.1,
      history.1.state = state) :
    (assessment.continuationContext site (fun history => payoff history.state)
      (2 * horizon + 1)).value alternative =
      (app.finish initial horizon scheduler
        (menu.decodeProfile initial horizon scheduler
          (Profile.update
            (sig := (menu.information initial horizon scheduler).behavioralSignature)
            assessment.strategy who alternative)) state).expect payoff := by
  rw [menu.context_value_finish initial horizon scheduler assessment who site payoff alternative]
  calc
    _ = (assessment.belief who site).expect (fun _ =>
        (app.finish initial horizon scheduler
          (menu.decodeProfile initial horizon scheduler
            (Profile.update
            (sig := (menu.information initial horizon scheduler).behavioralSignature)
              assessment.strategy who alternative)) state).expect payoff) := by
      apply FinDist.expect_congr
      intro history _
      rw [known history]
    _ = _ := FinDist.expect_const ..

end Interaction.ReactiveApplication.ResponseMenu
