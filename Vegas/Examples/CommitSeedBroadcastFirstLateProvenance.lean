/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastService
import Interaction.ReactiveResponseAccounting

/-! # Actual original clock-two callback placement and the original service bit -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private theorem originalClockFrom_add (start first second : Nat) :
    originalClockFrom start (first + second) =
      originalClockFrom start first + originalClockFrom (start + first) second := by
  induction first generalizing start with
  | zero => simp only [Nat.zero_add, originalClockFrom, Nat.add_zero]
  | succ first ih =>
      simp only [Nat.succ_add, originalClockFrom]
      rw [ih]
      simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Clock two in the original attempt places the physical command count
between the two initial clock advances and the advance to clock three. -/
theorem originalClock_two_bounds (count : Nat) (clock : originalClock count = 2) :
    5 ≤ count ∧ count ≤ 17 := by
  constructor
  · by_contra early
    have bounded : count < 5 := by omega
    interval_cases count <;> norm_num [originalClock, originalClockFrom, originalTick] at clock
  · by_contra late
    have before : 18 ≤ count := by omega
    have split := originalClockFrom_add 0 18 (count - 18)
    rw [Nat.add_sub_of_le before] at split
    have first : originalClockFrom 0 18 = 3 := by
      norm_num [originalClockFrom, originalTick]
    change originalClockFrom 0 count = 2 at clock
    rw [first] at split
    omega

private theorem pendingCommand_actor_none (identifier : MessageId Player)
    (view : app.EnvironmentView) : (pendingCommand identifier view).actor? app = none := by
  unfold pendingCommand
  split <;> rfl

private theorem earlyCommand_actor_none (owner : Player) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) : (earlyCommand owner past view).actor? app = none := by
  unfold earlyCommand
  split
  · rfl
  · split
    · rfl
    · exact pendingCommand_actor_none _ _

private theorem lateCommand_actor_none (owner : Player) (good : Bool) (clock : Nat)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) :
    (lateCommand owner good clock past view).actor? app = none := by
  unfold lateCommand
  by_cases eligible : ready owner (bindingEvent owner) view ∧
      (if good then 2 else 3) = clock
  · rw [ite_eq_left eligible]
    split
    · rfl
    · exact pendingCommand_actor_none _ _
  · rw [ite_eq_right eligible]
    rfl

private theorem pollCommand_activation (source owner : Player) (good wanted : Bool)
    (view : app.EnvironmentView)
    (selected : pollCommand source good wanted view = .activate owner) :
    good = wanted ∧ source = owner := by
  by_cases aligned : good = wanted
  · rw [pollCommand, ite_eq_left aligned] at selected
    unfold activateReady at selected
    split at selected
    · exact ⟨aligned, ReactiveApplication.Command.activate.inj selected⟩
    · cases selected
  · rw [pollCommand, ite_eq_right aligned] at selected
    cases selected

private theorem original_clock_two_command (seed : Seeds) (position : Nat)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) (owner : Player)
    (lower : 5 ≤ position) (upper : position ≤ 16)
    (selected : originalCommand seed position past view = .activate owner) :
    (position < 8 ∧ seed.2 owner = true) ∨
      (11 ≤ position ∧ position < 14 ∧ seed.2 owner = false) := by
  interval_cases position
  all_goals first
  | have literal : pollCommand (seed.1 (0 : Player))
        (seed.2 (seed.1 (0 : Player))) true view = .activate owner := selected
    obtain ⟨good, same⟩ := pollCommand_activation _ _ _ _ _ literal
    refine Or.inl ⟨by omega, ?_⟩
    rwa [same] at good
  | have literal : pollCommand (seed.1 (1 : Player))
        (seed.2 (seed.1 (1 : Player))) true view = .activate owner := selected
    obtain ⟨good, same⟩ := pollCommand_activation _ _ _ _ _ literal
    refine Or.inl ⟨by omega, ?_⟩
    rwa [same] at good
  | have literal : pollCommand (seed.1 (2 : Player))
        (seed.2 (seed.1 (2 : Player))) true view = .activate owner := selected
    obtain ⟨good, same⟩ := pollCommand_activation _ _ _ _ _ literal
    refine Or.inl ⟨by omega, ?_⟩
    rwa [same] at good
  | have literal : pollCommand (seed.1 (0 : Player))
        (seed.2 (seed.1 (0 : Player))) false view = .activate owner := selected
    obtain ⟨good, same⟩ := pollCommand_activation _ _ _ _ _ literal
    refine Or.inr ⟨by omega, by omega, ?_⟩
    rwa [same] at good
  | have literal : pollCommand (seed.1 (1 : Player))
        (seed.2 (seed.1 (1 : Player))) false view = .activate owner := selected
    obtain ⟨good, same⟩ := pollCommand_activation _ _ _ _ _ literal
    refine Or.inr ⟨by omega, by omega, ?_⟩
    rwa [same] at good
  | have literal : pollCommand (seed.1 (2 : Player))
        (seed.2 (seed.1 (2 : Player))) false view = .activate owner := selected
    obtain ⟨good, same⟩ := pollCommand_activation _ _ _ _ _ literal
    refine Or.inr ⟨by omega, by omega, ?_⟩
    rwa [same] at good
  | have actor := congrArg (ReactiveApplication.Command.actor? app) selected
    simp only [originalCommand] at actor
    first
    | rw [earlyCommand_actor_none] at actor
      cases actor
    | rw [lateCommand_actor_none] at actor
      cases actor

/-- At any actual raw original clock-two decision, the complete scheduler
transcript identifies whether the owner's independent original bit is good.
The owner need not observe that transcript. -/
theorem original_first_late_input_placement (seed : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seed)).Trace (some current))
    (owner : Player) (active : current.actor = some owner)
    (original : current.execution.application.attempt = originalAttempt)
    (clock : current.execution.application.current.native.clock = 2) :
    (6 ≤ current.execution.environmentRecall.length ∧
      current.execution.environmentRecall.length ≤ 8 ∧ seed.2 owner = true) ∨
    (12 ≤ current.execution.environmentRecall.length ∧
      current.execution.environmentRecall.length ≤ 14 ∧ seed.2 owner = false) := by
  obtain ⟨past, view, command, recalled, actor⟩ :=
    app.active_environment_entry initial horizon (family seed) current trace owner active
  have commandEq : command = .activate owner := by
    cases command <;> simp_all only [ReactiveApplication.Command.actor?,
      Option.some.injEq, reduceCtorEq]
  subst command
  have entryOriginal : view.application.attempt = originalAttempt :=
    earlier_original_attempt seed current trace original ⟨view, .activate owner⟩ (by
      rw [recalled]
      exact List.mem_append_right _ (List.mem_singleton_self _))
  have commands := family_commands seed current trace
  rw [recalled] at commands
  have chosen := (app.commandConsistent_snoc choose seed past ⟨view, .activate owner⟩).mp commands
  have selected : originalCommand seed past.length past view = .activate owner := by
    rw [choose_original seed past view entryOriginal] at chosen
    exact chosen.2
  have length : current.execution.environmentRecall.length = past.length + 1 := by
    rw [recalled, List.length_append, List.length_singleton]
  have clockIndex := (original_clock_index seed current trace original).symm.trans clock
  have bounded := originalClock_two_bounds _ clockIndex
  have beforeLower : 5 ≤ past.length := by
    by_contra early
    have four : past.length = 4 := by omega
    have impossible := selected
    rw [four] at impossible
    change (ReactiveApplication.Command.application .advanceClock : app.Command) =
      .activate owner at impossible
    cases impossible
  have placement := original_clock_two_command seed past.length past view owner beforeLower
    (by omega) selected
  rcases placement with ⟨high, good⟩ | ⟨low, high, bad⟩
  · exact Or.inl ⟨by omega, by omega, good⟩
  · exact Or.inr ⟨by omega, by omega, bad⟩

/-- The bad-service mark is a measurable function of the actual complete
physical history, although it is not determined by the owner's information. -/
theorem original_first_late_bad_iff (seed : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seed)).Trace (some current))
    (owner : Player) (active : current.actor = some owner)
    (original : current.execution.application.attempt = originalAttempt)
    (clock : current.execution.application.current.native.clock = 2) :
    seed.2 owner = false ↔ 12 ≤ current.execution.environmentRecall.length := by
  rcases original_first_late_input_placement seed current trace owner active original clock with
    ⟨lower, upper, good⟩ | ⟨lower, upper, bad⟩
  · rw [good]
    constructor
    · intro impossible
      cases impossible
    · omega
  · exact ⟨fun _ => lower, fun _ => bad⟩

end Vegas.Examples.CommitSeedBroadcast
