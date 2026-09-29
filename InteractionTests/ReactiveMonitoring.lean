/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveMonitoring

/-! # Reporting a premature packet without restricting later observations

The watcher samples a pending packet with probability one half. Other players
sample all pending identifiers. The application initially rejects the packet
and can subsequently accept its payload; the earlier failed receipt persists.
-/

noncomputable section

namespace InteractionTests.ReactiveMonitoring

open Interaction GameTheory.Math.Probability

private abbrev app : ReactiveApplication (Fin 3) where
  State := Bool
  Payload := Nat
  Submission := Nat
  EnvironmentCommand := Unit
  LocalObservation := Bool
  PublicObservation := Bool
  packet := fun _ _ _ => id
  submit state _ _ := state
  handle ready _ := if ready then some ready else none
  environment _ _ := PMF.pure true
  observePlayer ready _ := ready
  observePublic := id
  observePending who pending := if who = 2 then
    mix (1 / 2) (by norm_num) (by norm_num)
      (PMF.pure (pending.map Message.id).toFinset) (PMF.pure ∅)
    else PMF.pure (pending.map Message.id).toFinset

private def sent : app.Execution :=
  (ReactiveApplication.Execution.initial app false).respond app 0 ⟨some (.submit 7)⟩

private def message : Message (Fin 3) Nat := ⟨(0, 0), 7⟩

private theorem sampling_half :
    ((app.observePending 2 sent.network.pending).toOuterMeasure
      {selected | (0, 0) ∈ selected}).toReal =
      (1 / 2 : ℝ) := by
  change ((mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure {(0, 0)}) (PMF.pure ∅)).toOuterMeasure _).toReal = _
  rw [← expect_indicator,
    expect_mix _ _ _ _ _ _ (payoffIntegrable_pure _ _) (payoffIntegrable_pure _ _),
    expect_pure, expect_pure]
  norm_num

/-- All future policies and commands, including a later change to acceptance,
leave at least one-half probability of the original rejection receipt. -/
theorem half_detection_after_arbitrary_continuation
    (players : Fin 3 → app.Policy) (reports : players 2 = app.reportFirstUnpublished)
    (scheduler : app.Scheduler) (count : Nat) :
    (1 / 2 : ℝ) ≤ (((app.reportInclusion players 2 sent).bind
      (app.runRounds scheduler players count)).toOuterMeasure
        {final | ((0, 0), false) ∈ final.receipts}).toReal := by
  rw [← sampling_half]
  apply app.sampling_rejected_receipt_lower players 2 sent (0, 0) message rfl (by decide)
    rfl (by simp [sent, ReactiveApplication.Execution.respond,
      ReactiveApplication.Execution.initial, MessageNetwork.empty, MessageNetwork.submit]) _ rfl
    scheduler count
  intro observed reached seen
  rw [reports]
  apply app.reportFirstUnpublished_after_activation sent 2 (0, 0) message rfl (by decide)
    _ _ observed reached seen
  · intro packet member
    cases member
  · intro packet member _
    have same : packet = message := List.mem_singleton.mp member
    exact congrArg Message.id same

/-- The ordinary recipient still learns the pending foreign packet. -/
theorem ordinary_pending_observation :
    app.observePending 1 sent.network.pending = PMF.pure {(0, 0)} ∧
      (sent.network.learn 1 {(0, 0)}).leaked 1 = [message] := ⟨rfl, rfl⟩

/-- The payload changes from rejected to accepted without changing its bytes.
The receipt theorem therefore cannot be replaced by a final-state validity test. -/
theorem rejection_is_phase_sensitive :
    app.handle false message = none ∧ app.handle true message = some true := ⟨rfl, rfl⟩

end InteractionTests.ReactiveMonitoring
