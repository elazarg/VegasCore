/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveLocalContinuation

/-! # Physical continuations of an admissible finite response restriction

A local alternative is a finite-menu law, followed by the original physical
policy. Coverage is needed at actual legal histories only. The representation's
fallback at inconsistent private inputs is irrelevant to these laws.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
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
  rw [menu.run_restrict_control_steps initial horizon scheduler players covered]
  exact app.iterate_eq_finish initial horizon scheduler players fuel history.state enough

end Interaction.ReactiveApplication.ResponseMenu
