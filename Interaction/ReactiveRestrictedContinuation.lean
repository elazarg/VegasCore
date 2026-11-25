module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Interaction.ReactiveLocalContinuation
public import Interaction.ReactiveRoundReachability

@[expose] public section

/-! # Physical continuations of an admissible finite response restriction

A local alternative is a finite-menu law, followed by the original physical
policy. Coverage is needed at actual legal histories only. The representation's
fallback at inconsistent private inputs is irrelevant to these laws.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Finite Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

theorem run_restrict_eq_finish (players : Principal → app.Policy)
    (covered : ∀ who, menu.Admissible initial horizon scheduler who (players who))
    (fuel : Nat) (history : (menu.protocol initial horizon scheduler).History)
    (enough : app.rank horizon history.state ≤ fuel) :
    ((menu.information initial horizon scheduler).runBehavioralFrom
      (fun who => menu.restrictPolicy initial horizon scheduler who (players who))
      fuel history).map History.state =
      app.finish initial horizon scheduler players history.state := by
  let : Fintype Principal := Fintype.ofFinite Principal
  rw [menu.run_restrict_control_steps initial horizon scheduler players covered]
  exact app.iterate_eq_finish initial horizon scheduler players fuel history.state enough

/-- The initialized finite-menu protocol realizes the complete physical round law. -/
theorem run_restrict_eq_roundsFrom (players : Principal → app.Policy)
    (covered : ∀ who, menu.Admissible initial horizon scheduler who (players who)) :
    ((menu.information initial horizon scheduler).runBehavioral
      (fun who => menu.restrictPolicy initial horizon scheduler who (players who))
      (2 * horizon + 1)).map History.state =
      (app.roundsFrom initial scheduler players horizon).map app.finished := by
  have physical := menu.run_restrict_eq_finish initial horizon scheduler players covered
    (2 * horizon + 1) (menu.protocol initial horizon scheduler).initHistory le_rfl
  refine physical.trans ?_
  simp only [ReactiveApplication.finish, ReactiveApplication.roundsFrom, PMF.map_bind]
  rfl

end Interaction.ReactiveApplication.ResponseMenu
