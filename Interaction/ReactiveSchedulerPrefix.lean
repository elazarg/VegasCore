/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveStopping

/-! # Execution laws under finite-prefix scheduler agreement

Schedulers which agree throughout a range of command counts give the same
execution law in that range, for arbitrary raw player policies. Changes after
that range cannot change the initialized law at its end.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

theorem runRounds_eq_of_scheduler_agreement (first second : app.Scheduler)
    (players : Principal → app.Policy) (count : Nat) (execution : app.Execution)
    (agree : ∀ past view,
      execution.environmentRecall.length ≤ past.length →
      past.length < execution.environmentRecall.length + count →
      first past view = second past view) :
    app.runRounds first players count execution = app.runRounds second players count execution := by
  induction count generalizing execution with
  | zero => rfl
  | succ count ih =>
      have current : app.round first players execution = app.round second players execution := by
        unfold round
        rw [agree _ _ le_rfl (by omega)]
      simp only [runRounds, current]
      apply bind_congr_on_support
      intro next supported
      have cursor := app.round_environmentRecall_length second players execution next supported
      apply ih
      intro past view lower upper
      apply agree past view <;> omega

end Interaction.ReactiveApplication
