module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Interaction.ReactiveMenuPolicy
public import Interaction.ReactiveRounds

@[expose] public section

/-! # Complete native evaluation of finite-menu behavioral profiles -/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

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

variable [Finite Principal]

/-- Complete behavioral history law within the supplied response menu. -/
def runFrom
    (profile : (who : Principal) →
      (menu.information initial horizon scheduler).BehavioralPolicy who)
    (history : (menu.protocol initial horizon scheduler).History) :=
  (menu.information initial horizon scheduler).runBehavioralFrom profile (2 * horizon + 1) history

/-- Complete response-menu play from initialization. -/
def run
    (profile : (who : Principal) →
      (menu.information initial horizon scheduler).BehavioralPolicy who) :=
  menu.runFrom initial horizon scheduler profile
    (menu.protocol initial horizon scheduler).initHistory

/-- The behavioral game of complete response-menu executions. -/
abbrev gameForm :=
  (menu.information initial horizon scheduler).toBehavioralGameForm (2 * horizon + 1)

/-- Complete menu evaluation agrees with the well-founded terminal law at
every legal history, including histories of unilateral alternatives. -/
theorem runFrom_eq_terminal
    (profile : (who : Principal) →
      (menu.information initial horizon scheduler).BehavioralPolicy who)
    (history : (menu.protocol initial horizon scheduler).History) :
    menu.runFrom initial horizon scheduler profile history =
      (menu.information initial horizon scheduler).runBehavioralTerminalFrom
        (menu.bounded initial horizon scheduler).wellFoundedHistories profile history :=
  (InformationModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
    (menu.information initial horizon scheduler)
    (menu.bounded initial horizon scheduler).wellFoundedHistories
    (menu.bounded initial horizon scheduler) profile history).symm

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
      rw [PMF.map_comp]
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

/-- Finite restriction evaluates the original physical policy at every legal
starting history and every prefix length. Global decoder agreement at
unreachable, inconsistent inputs is unnecessary. -/
theorem run_restrict_control_steps (profile : Principal → app.Policy)
    (covered : ∀ who, menu.Admissible initial horizon scheduler who (profile who))
    (fuel : Nat) (history : (menu.protocol initial horizon scheduler).History) :
    ((menu.information initial horizon scheduler).runBehavioralFrom
      (fun who => menu.restrictPolicy initial horizon scheduler who (profile who))
      fuel history).map History.state =
      (fun law => law.bind (app.controlStep initial horizon scheduler profile))^[fuel]
        (PMF.pure history.state) := by
  calc
    _ = (((menu.information initial horizon scheduler).runBehavioralFrom
        (fun who => menu.restrictPolicy initial horizon scheduler who (profile who))
        fuel history).map (menu.toRawHistory initial horizon scheduler)).map History.state := by
      rw [PMF.map_comp]
      rfl
    _ = _ := by
      rw [menu.run_restrict initial horizon scheduler profile covered,
        ← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom
          (app.information initial horizon scheduler) (app.singleMover initial horizon scheduler),
        app.run_map_state]
      rfl

/-- Complete menu play has exactly the physical continuation state law. -/
theorem runFrom_stateLaw
    (profile : (who : Principal) →
      (menu.information initial horizon scheduler).BehavioralPolicy who)
    (history : (menu.protocol initial horizon scheduler).History) :
    (menu.runFrom initial horizon scheduler profile history).map History.state =
      app.finish initial horizon scheduler (menu.decodeProfile initial horizon scheduler profile)
        history.state := by
  apply menu.run_eq_finish initial horizon scheduler profile (2 * horizon + 1) history
  have bound := app.trace_bound initial horizon scheduler
    (menu.toRawTrace initial horizon scheduler history.trace)
  omega

end Interaction.ReactiveApplication.ResponseMenu
