/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveResponseEvaluation
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Terminal behavioral histories and the original scheduler-round evaluator -/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

/-- Evaluating a finite-menu behavioral profile to terminal histories has the
same complete state law as finishing its decoded physical profile. -/
theorem terminal_run_eq_finish
    (certificate : (menu.protocol initial horizon scheduler).WellFoundedHistories)
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (history : (menu.protocol initial horizon scheduler).History) :
    ((menu.information initial horizon scheduler).runBehavioralTerminalFrom certificate
      profile history).map History.state =
      app.finish initial horizon scheduler (menu.decodeProfile initial horizon scheduler profile)
        history.state := by
  rw [(menu.information initial horizon scheduler).runBehavioralTerminalFrom_eq_remaining
    certificate profile
    (menu.bounded initial horizon scheduler)]
  apply menu.run_eq_finish initial horizon scheduler profile
  have bounded := app.trace_bound initial horizon scheduler
    (menu.toRawTrace initial horizon scheduler history.trace)
  rw [menu.toRawTrace_length initial horizon scheduler history.trace] at bounded
  omega

/-- Terminal behavioral play of a covered physical profile evaluates that
original profile, without requiring decoder equality at unreachable inputs. -/
theorem terminal_run_restrict_eq_finish
    (certificate : (menu.protocol initial horizon scheduler).WellFoundedHistories)
    (profile : Principal → app.Policy)
    (covered : ∀ who, menu.Admissible initial horizon scheduler who (profile who))
    (history : (menu.protocol initial horizon scheduler).History) :
    ((menu.information initial horizon scheduler).runBehavioralTerminalFrom certificate
      (fun who => menu.restrictPolicy initial horizon scheduler who (profile who)) history).map
        History.state = app.finish initial horizon scheduler profile history.state := by
  rw [(menu.information initial horizon scheduler).runBehavioralTerminalFrom_eq_remaining
    certificate _
    (menu.bounded initial horizon scheduler),
    menu.run_restrict_control_steps initial horizon scheduler profile covered]
  apply app.iterate_eq_finish
  have bounded := app.trace_bound initial horizon scheduler
    (menu.toRawTrace initial horizon scheduler history.trace)
  rw [menu.toRawTrace_length initial horizon scheduler history.trace] at bounded
  omega

end Interaction.ReactiveApplication.ResponseMenu
