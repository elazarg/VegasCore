/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeGame
import Interaction.ReactiveRawRoundTrace
import Vegas.Examples.LateOpeningRuntimeServiceClock

/-! # Native continuation independence after Alice's last activation -/

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeBobTail

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeGame

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
local notation "S" => LateOpeningRuntimeService.scheduler weight nonnegative
local notation "E" => rawMenu.protocol initial LateOpeningRuntimeService.horizon S
local notation "M" => model weight nonnegative

private theorem scheduler_no_alice (execution : app.Execution)
    (late : 8 ≤ execution.environmentRecall.length) (command : app.Command)
    (selected : command ∈ (S execution.environmentRecall
      (execution.observeEnvironment app)).support) : command.actor? app ≠ some alice := by
  change command ∈ (stageChoice weight nonnegative execution.environmentRecall.length
    (execution.observeEnvironment app)).support at selected
  unfold stageChoice at selected
  split at selected
  all_goals try omega
  all_goals try {
    have same := (PMF.mem_support_pure_iff _ _).mp selected
    subst command
    solve
    | exact fun impossible => Option.noConfusion impossible
    | rw [(latestAuthor_passive bob (execution.observeEnvironment app)).1]
      decide
    | decide
    | split
      · rw [(latestAuthor_passive bob (execution.observeEnvironment app)).1]
        decide
      · decide
    | split <;> decide
  }
  rw [(lottery_passive weight nonnegative (execution.observeEnvironment app)
    command selected).1]
  decide

private def AfterAlice (state : app.ProtocolState) : Prop :=
  ∃ control, state = some control ∧ 8 ≤ control.execution.environmentRecall.length ∧
    control.actor ≠ some alice

private theorem afterAlice_step {state next : app.ProtocolState}
    (afterAlice : AfterAlice state) (joint : ∀ _who : Player, Option app.Action)
    (supported : next ∈ (app.transition initial LateOpeningRuntimeService.horizon S
      state joint).support) : AfterAlice next := by
  obtain ⟨control, rfl, late, absent⟩ := afterAlice
  cases actorEq : control.actor with
  | some _who =>
      simp only [ReactiveApplication.transition, actorEq, PMF.mem_support_pure_iff] at supported
      subst next
      refine ⟨_, rfl, ?_, by simp⟩
      simpa only [app.respond_environmentRecall] using late
  | none =>
      cases remainingEq : control.remaining with
      | zero =>
          simp only [ReactiveApplication.transition, actorEq, remainingEq,
            PMF.mem_support_pure_iff] at supported
          subst next
          exact ⟨control, rfl, late, absent⟩
      | succ remaining =>
          simp only [ReactiveApplication.transition, actorEq, remainingEq] at supported
          obtain ⟨command, selected, moved⟩ :=
            Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
          obtain ⟨execution, executed, rfl⟩ := PMF.support_map .. ▸ moved
          have absentNext := scheduler_no_alice weight nonnegative control.execution late
            command selected
          refine ⟨_, rfl, ?_, absentNext⟩
          unfold ReactiveApplication.Execution.environmentStep at executed
          obtain ⟨updated, _, rfl⟩ := PMF.support_map .. ▸ executed
          simp only [List.length_append, List.length_singleton]
          omega

private theorem afterAlice_reaches {first later : (E).History}
    (afterAlice : AfterAlice first.state) (reaches : (E).HistoryReaches first later) :
    AfterAlice later.state := by
  obtain ⟨fuel, reaches⟩ := reaches
  induction reaches with
  | refl => exact afterAlice
  | @step fuel history target joint legal reached supported rest ih =>
      apply ih
      exact afterAlice_step weight nonnegative afterAlice joint supported

/-- The full actual terminal history law after the final Alice activation depends
only on Bob's decision laws. Raw packets, scheduler draws and Bob's full recall
are retained; Alice's entire future policy can be changed. -/
theorem terminal_law_eq_of_bob_agreement
    (first second : ∀ who, (M).BehavioralPolicy who) (history : (E).History)
    (control : app.Control) (current : history.state = some control)
    (late : control.remaining ≤ 18)
    (absent : control.actor ≠ some alice)
    (bobAgreement : (first bob).AgreesAtDecisions (second bob)) :
    (M).runBehavioralTerminalFrom
        (rawMenu.bounded initial LateOpeningRuntimeService.horizon S).wellFoundedHistories
        first history =
      (M).runBehavioralTerminalFrom
        (rawMenu.bounded initial LateOpeningRuntimeService.horizon S).wellFoundedHistories
        second history := by
  have traced : (E).Trace (some control) := current ▸ history.trace
  have accounted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon S
    (rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon S traced)
  have lateCursor : 8 ≤ control.execution.environmentRecall.length := by
    change control.execution.environmentRecall.length + control.remaining = 26 at accounted
    omega
  apply (M).runBehavioralTerminalFrom_congr
  intro later reaches nonterminal who
  obtain ⟨laterControl, laterEq, _, laterAbsent⟩ :=
    afterAlice_reaches weight nonnegative ⟨control, current, lateCursor, absent⟩ reaches
  fin_cases who
  · apply (M).behavioral_eq_of_not_active _ _ later.trace
    change ¬ app.actor later.state = some alice
    simpa only [ReactiveApplication.actor, laterEq, Option.bind_some] using laterAbsent
  · exact bobAgreement.at_history later nonterminal

/-- Public clock three or later identifies only post-Alice Bob histories throughout
its complete legal information fiber, irrespective of reach or belief mass. -/
theorem tail_of_information
    (site : (M).InformationSite bob) (representative : (M).InformationHistory bob site.1)
    (control : app.Control) (current : representative.1.state = some control)
    (lateClock : 3 ≤ control.execution.application.clock)
    (history : (M).InformationHistory bob site.1) :
    ∃ later : app.Control, history.1.state = some later ∧ later.remaining ≤ 18 ∧
      later.actor = some bob := by
  have active := InformationModel.InformationSite.active (M) site history
  obtain ⟨later, stateEq, actor⟩ := app.control_of_active initial
    LateOpeningRuntimeService.horizon S (rawMenu.toRawHistory _ _ _ history.1) bob active
  change history.1.state = some later at stateEq
  have rawTrace := stateEq ▸ rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    S history.1.trace
  have representativeActive := InformationModel.InformationSite.active (M) site representative
  have representativeActor : control.actor = some bob := by
    change app.actor representative.1.state = some bob at representativeActive
    simpa only [ReactiveApplication.actor, current, Option.bind_some] using representativeActive
  have information := representative.2.trans history.2.symm
  change (rawMenu.signals _ _ _).infoOf bob representative.1.trace =
    (rawMenu.signals _ _ _).infoOf bob history.1.trace at information
  rw [rawMenu.info, rawMenu.info] at information
  change app.observe bob representative.1.state = app.observe bob history.1.state at information
  rw [current, stateEq] at information
  simp only [ReactiveApplication.observe, representativeActor, actor, ↓reduceIte] at information
  have sameView := congrArg Prod.snd (Option.some.inj information)
  have sameClock := congrArg (fun view : app.PlayerView =>
    view.application.publicView.clock) sameView
  change control.execution.application.clock = later.execution.application.clock at sameClock
  have clocked := clock_history weight nonnegative later rawTrace
  have cursorLate : 8 ≤ later.execution.environmentRecall.length := by
    by_contra tooEarly
    have early : later.execution.environmentRecall.length < 8 := by omega
    generalize later.execution.environmentRecall.length = cursor at clocked early
    have small : LateOpeningRuntimeService.clockAt cursor ≤ 2 := by
      interval_cases cursor <;> decide
    omega
  have accounted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon S rawTrace
  change later.execution.environmentRecall.length + later.remaining = 26 at accounted
  exact ⟨later, stateEq, by omega, actor⟩

/-- All whole-policy Bob alternatives have the same actual continuation context
when only Alice's strategy changes and Bob's reference belief is retained. -/
theorem continuation_context_eq
    (first second : (M).BehavioralAssessment) (site : (M).InformationSite bob)
    (representative : (M).InformationHistory bob site.1) (control : app.Control)
    (current : representative.1.state = some control)
    (lateClock : 3 ≤ control.execution.application.clock)
    (sameBelief : first.belief bob site = second.belief bob site)
    (payoff : (E).History → ℝ) :
    first.continuationContext
        (rawMenu.bounded initial LateOpeningRuntimeService.horizon S).wellFoundedHistories
        site payoff =
      second.continuationContext
        (rawMenu.bounded initial LateOpeningRuntimeService.horizon S).wellFoundedHistories
        site payoff := by
  change Context.mk _ payoff = Context.mk _ payoff
  apply congrArg (fun outcome => Context.mk outcome payoff)
  funext alternative
  rw [sameBelief]
  apply bind_congr_on_support
  intro history _
  obtain ⟨later, laterEq, late, actor⟩ :=
    tail_of_information weight nonnegative site representative control current lateClock history
  apply terminal_law_eq_of_bob_agreement weight nonnegative _ _ history.1 later laterEq late
    (by rw [actor]; decide)
  simp only [GameTheory.Profile.update_same]
  rfl

/-- Bob's reference whole-policy rationality transfers after Alice's last callback
while keeping his complete belief and decision laws. No Alice optimality or
cross-player consistency assertion is made. -/
theorem rationality_iff
    (first second : (M).BehavioralAssessment) (site : (M).InformationSite bob)
    (representative : (M).InformationHistory bob site.1) (control : app.Control)
    (current : representative.1.state = some control)
    (lateClock : 3 ≤ control.execution.application.clock)
    (sameBelief : first.belief bob site = second.belief bob site)
    (sameBob : (first.strategy bob).AgreesAtDecisions (second.strategy bob))
    (payoff : (E).History → ℝ) :
    first.IsSequentiallyRationalAt site
        (first.continuationContext
          (rawMenu.bounded initial LateOpeningRuntimeService.horizon S).wellFoundedHistories
          site payoff) ↔
      second.IsSequentiallyRationalAt site
        (second.continuationContext
          (rawMenu.bounded initial LateOpeningRuntimeService.horizon S).wellFoundedHistories
          site payoff) := by
  have contexts := continuation_context_eq weight nonnegative first second site representative
    control current lateClock sameBelief payoff
  have incumbentLaw :
      (second.continuationContext
        (rawMenu.bounded initial LateOpeningRuntimeService.horizon S).wellFoundedHistories
        site payoff).outcome (first.strategy bob) =
      (second.continuationContext
        (rawMenu.bounded initial LateOpeningRuntimeService.horizon S).wellFoundedHistories
        site payoff).outcome (second.strategy bob) := by
    change (second.belief bob site).bind _ = (second.belief bob site).bind _
    apply bind_congr_on_support
    intro history _
    apply (M).runBehavioralTerminalFrom_eq_of_agreesAtDecisions
    intro who
    by_cases owner : who = bob
    · subst who
      simpa only [GameTheory.Profile.update_same] using sameBob
    · simp only [GameTheory.Profile.update_of_ne _ _ owner]
      rfl
  unfold InformationModel.BehavioralAssessment.IsSequentiallyRationalAt
  rw [contexts]
  simp only [Context.IsLocallyOptimal, Context.HasValueAt, Context.extendedValue, incumbentLaw]

end Vegas.Examples.LateOpeningRuntimeBobTail
