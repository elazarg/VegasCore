/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRounds
import Interaction.ReactiveTrafficState
import Interaction.ReactiveStopping

/-! # Physical continuations after the last player callback

If every supported scheduler command after a cursor is passive, future player
policies cannot affect the execution law and no additional authored input or
player recall is appended. Inclusion, public application steps and observations
remain unrestricted.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)
  (scheduler : app.Scheduler) (cursor : Nat)

/-- After a player's last callback, changing only that player's remaining
policy preserves the complete execution law. Other players may still act. -/
theorem continuation_policy_independent_of_unactivated (owner : Principal)
    (absent : ∀ past view, cursor ≤ past.length →
      ∀ command ∈ (scheduler past view).support, command.actor? app ≠ some owner)
    (first second : Principal → app.Policy)
    (others : ∀ who, who ≠ owner → first who = second who)
    (count : Nat) (execution : app.Execution)
    (later : cursor ≤ execution.environmentRecall.length) :
    app.runRounds scheduler first count execution =
      app.runRounds scheduler second count execution := by
  have roundEqual (before : app.Execution)
      (afterLast : cursor ≤ before.environmentRecall.length) :
      app.round scheduler first before = app.round scheduler second before := by
    unfold round dispatch
    apply bind_congr_on_support
    intro command selected
    have notOwner := absent _ _ afterLast command selected
    cases actor : command.actor? app with
    | none => rfl
    | some who =>
        have different : who ≠ owner := fun equal =>
          notOwner (actor.trans (congrArg some equal))
        apply congrArg ((before.environmentStep app command).bind)
        funext next
        change (first who (next.recall who) (next.observe app who)).map
          (next.respond app who) = _
        rw [others who different]
        rfl
  induction count generalizing execution with
  | zero => rfl
  | succ count ih =>
      rw [runRounds, runRounds, roundEqual execution later]
      apply bind_congr_on_support
      intro next reached
      apply ih
      have length := app.round_environmentRecall_length scheduler second execution next reached
      omega

variable
  (passive : ∀ past view, cursor ≤ past.length →
    ∀ command ∈ (scheduler past view).support, command.actor? app = none)

include passive

private theorem passive_round (players : Principal → app.Policy)
    (execution : app.Execution) (later : cursor ≤ execution.environmentRecall.length) :
    app.round scheduler players execution =
      (scheduler execution.environmentRecall (execution.observeEnvironment app)).bind
        (execution.environmentStep app) := by
  unfold round dispatch
  apply bind_congr_on_support
  intro command selected
  rw [passive _ _ later command selected]
  change (execution.environmentStep app command).bind PMF.pure = _
  exact PMF.bind_pure _

/-- Future player policies have no influence after the last callback. -/
theorem passive_continuation_policy_independent (first second : Principal → app.Policy)
    (count : Nat) (execution : app.Execution)
    (later : cursor ≤ execution.environmentRecall.length) :
    app.runRounds scheduler first count execution =
      app.runRounds scheduler second count execution := by
  induction count generalizing execution with
  | zero => rfl
  | succ count ih =>
      rw [runRounds, runRounds, passive_round app scheduler cursor passive first execution later,
        passive_round app scheduler cursor passive second execution later]
      apply bind_congr_on_support
      intro next reached
      apply ih
      have roundReached : next ∈ (app.round scheduler first execution).support := by
        rwa [passive_round app scheduler cursor passive first execution later]
      have length := app.round_environmentRecall_length scheduler first execution next roundReached
      omega

/-- Passive continuations retain exactly the previous authored inputs and
player recall, even while pending packets are included. -/
theorem passive_continuation_preserves_traffic (players : Principal → app.Policy)
    (count : Nat) (execution final : app.Execution)
    (later : cursor ≤ execution.environmentRecall.length)
    (reached : final ∈ (app.runRounds scheduler players count execution).support) :
    final.recall = execution.recall ∧ final.network.inputs = execution.network.inputs := by
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨rfl, rfl⟩
  | succ count ih =>
      obtain ⟨next, moved, continued⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have length := app.round_environmentRecall_length scheduler players execution next moved
      have nextLate : cursor ≤ next.environmentRecall.length := by omega
      have retained := ih next nextLate continued
      rw [passive_round app scheduler cursor passive players execution later] at moved
      obtain ⟨command, _, environment⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
      exact ⟨retained.1.trans (app.environmentStep_recall execution next command environment),
        retained.2.trans (app.environmentStep_inputs execution next command environment)⟩

end Interaction.ReactiveApplication
