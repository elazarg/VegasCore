/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.PrivateResolutionForkService
import Interaction.ReactiveTraceDepth

/-! # Actual clock and activation accounting for the public fork

The invariant covers every legal initialized raw trace. It identifies Bob's
single decision at clock three, with empty own recall and two actual Alice
responses. Packet acceptance and complete input-fiber inversion are separate.
-/

noncomputable section

namespace Vegas.PrivateResolutionFork

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability
open GameTheory.Protocol

def stageClock (history : List app.EnvironmentEntry) : Nat :=
  let stage := history.length
  if stage ≤ 4 then 0
  else if stage = 5 then if lastTick history then 1 else 0
  else if stage ≤ 7 then 1
  else if stage ≤ 8 then 2
  else if stage ≤ 12 then 3
  else if stage ≤ 16 then stage - 9 else 7

def visitCount (history : List app.EnvironmentEntry) (who : Player) : Nat :=
  if who = alice then
    if history.length ≤ 2 then 0
    else if history.length ≤ 4 then 1
    else if history.length = 5 then if lastTick history then 1 else 2 else 2
  else if history.length ≤ 10 then 0 else 1

theorem environment_graph_or_tick (execution next : app.Execution) (command : app.Command)
    (moved : next ∈ (execution.environmentStep app command).support) :
    (command = .application .advanceClock ∧
      next.application.config = execution.application.config ∧
      next.application.activatedAt = execution.application.activatedAt ∧
      next.application.clock = execution.application.clock + 1) ∨
      GraphStep execution.application next.application := by
  cases command with
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact Or.inr (GraphStep.refl _)
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      exact Or.inr (GraphStep.refl _)
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      exact Or.inr (graphStep_includePending (runtime setup) leaks execution id)
  | application command =>
      have supported := (applicationStep_facts execution next command moved).1
      cases command with
      | advanceClock =>
          simp only [environmentStep, PMF.mem_support_pure_iff _ _] at supported
          rw [supported]
          exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
      | executeSample event =>
          exact Or.inr (graphStep_executeSample (runtime setup) _ _ event supported)
      | expire event =>
          exact Or.inr (graphStep_expire (runtime setup) _ _ event supported)

private def tickCount : app.Command → Nat
  | .application .advanceClock => 1
  | _ => 0

private theorem environment_clock (execution next : app.Execution) (command : app.Command)
    (moved : next ∈ (execution.environmentStep app command).support) :
    next.application.clock = execution.application.clock + tickCount command := by
  rcases environment_graph_or_tick execution next command moved with ⟨tick, _, _, clock⟩ | step
  · rw [tick, clock]
    rfl
  · have clock : next.application.clock = execution.application.clock := by
      rcases step with ⟨_, same, _⟩ | ⟨_, _, _, _, same, _⟩ <;> exact same
    cases command with
    | application command =>
        cases command with
        | advanceClock =>
            have physical := (applicationStep_facts execution next _ moved).1
            simp only [environmentStep, PMF.mem_support_pure_iff _ _] at physical
            rw [physical] at clock
            change execution.application.clock + 1 = execution.application.clock at clock
            omega
        | executeSample | expire => exact clock
    | activate | wait | «include» => exact clock

theorem scheduler_support_four (history : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (command : app.Command) (four : history.length = 4)
    (selected : command ∈ (scheduler history view).support) :
    command = .activate alice ∨ command = .application .advanceClock := by
  simp only [scheduler, four, ite_true] at selected
  exact (mem_support_mix_pure_iff _ _ _ (by norm_num) (by norm_num)).mp selected

theorem scheduler_support_six (history : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (command : app.Command) (six : history.length = 6)
    (selected : command ∈ (scheduler history view).support) :
    command = (runtime setup).reactiveLatest leaks aliceResolution alice view ∨
      command = latestAliceWithhold view := by
  simp only [scheduler, six, Nat.reduceEqDiff, ite_false] at selected
  split at selected
  · exact (mem_support_mix_pure_iff _ _ _ (by norm_num) (by norm_num)).mp selected
  · exact Or.inl (PMF.mem_support_pure_iff _ _ |>.mp selected)

theorem scheduler_support_other (history : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (command : app.Command) (four : history.length ≠ 4) (six : history.length ≠ 6)
    (selected : command ∈ (scheduler history view).support) :
    command = stageCommand history.length history view := by
  simpa only [scheduler, four, six, false_and, ite_false, PMF.mem_support_pure_iff] using selected

private theorem stageClock_append (history : List app.EnvironmentEntry)
    (view : app.EnvironmentView) (command : app.Command) (beforeEnd : history.length < horizon)
    (selected : command ∈ (scheduler history view).support) :
    stageClock (history ++ [⟨view, command⟩]) = stageClock history + tickCount command := by
  by_cases four : history.length = 4
  · rcases scheduler_support_four history view command four selected with rfl | rfl <;>
      simp [stageClock, four, lastTick, tickCount]
  by_cases six : history.length = 6
  · rcases scheduler_support_six history view command six selected with rfl | rfl
    · unfold reactiveLatest
      split <;> simp [stageClock, six, tickCount]
    · unfold latestAliceWithhold
      split <;> simp [stageClock, six, tickCount]
  have chosen := scheduler_support_other history view command four six selected
  rw [chosen]
  generalize stageEq : history.length = stage at beforeEnd four six ⊢
  change stage < 17 at beforeEnd
  interval_cases stage
  all_goals try contradiction
  all_goals simp only [stageCommand]
  all_goals first
    | (unfold reactiveLatest; split <;> simp [stageClock, stageEq, tickCount])
    | (split <;> simp_all [stageClock, lastTick, tickCount])
    | simp [stageClock, stageEq, tickCount]

private theorem visitCount_append (history : List app.EnvironmentEntry)
    (view : app.EnvironmentView) (command : app.Command) (beforeEnd : history.length < horizon)
    (selected : command ∈ (scheduler history view).support) (who : Player) :
    visitCount (history ++ [⟨view, command⟩]) who = visitCount history who +
      if command.actor? app = some who then 1 else 0 := by
  by_cases four : history.length = 4
  · rcases scheduler_support_four history view command four selected with rfl | rfl <;>
      fin_cases who <;> simp [visitCount, four, lastTick, ReactiveApplication.Command.actor?]
  by_cases six : history.length = 6
  · rcases scheduler_support_six history view command six selected with rfl | rfl
    · unfold reactiveLatest
      split <;> fin_cases who <;>
        simp [visitCount, six, ReactiveApplication.Command.actor?]
    · unfold latestAliceWithhold
      split <;> fin_cases who <;>
        simp [visitCount, six, ReactiveApplication.Command.actor?]
  have chosen := scheduler_support_other history view command four six selected
  rw [chosen]
  generalize stageEq : history.length = stage at beforeEnd four six ⊢
  change stage < 17 at beforeEnd
  interval_cases stage
  all_goals try contradiction
  all_goals simp only [stageCommand]
  all_goals fin_cases who
  all_goals first
    | (unfold reactiveLatest; split <;>
        simp [visitCount, stageEq, ReactiveApplication.Command.actor?])
    | (split <;> simp_all [visitCount, lastTick, ReactiveApplication.Command.actor?])

private theorem selected_activation (history : List app.EnvironmentEntry)
    (view : app.EnvironmentView) (command : app.Command) (beforeEnd : history.length < horizon)
    (selected : command ∈ (scheduler history view).support) (who : Player)
    (active : command.actor? app = some who) :
    (history.length + 1 = 3 ∧ who = alice) ∨
      (history.length + 1 = 5 ∧ who = alice) ∨
      (history.length + 1 = 6 ∧ who = alice) ∨
      (history.length + 1 = 11 ∧ who = bob) := by
  by_cases four : history.length = 4
  · rcases scheduler_support_four history view command four selected with rfl | rfl
    · exact Or.inr (Or.inl ⟨by omega, (Option.some.inj active).symm⟩)
    · cases active
  by_cases six : history.length = 6
  · rcases scheduler_support_six history view command six selected with rfl | rfl
    · unfold reactiveLatest at active
      split at active <;> cases active
    · unfold latestAliceWithhold at active
      split at active <;> cases active
  have chosen := scheduler_support_other history view command four six selected
  rw [chosen] at active
  generalize stageEq : history.length = stage at beforeEnd four six active ⊢
  change stage < 17 at beforeEnd
  interval_cases stage
  all_goals try contradiction
  all_goals simp only [stageCommand] at active
  all_goals first
    | (unfold reactiveLatest at active; split at active <;> cases active)
    | (split at active <;> simp_all [ReactiveApplication.Command.actor?])
    | simp_all [ReactiveApplication.Command.actor?]

structure ClockPhase (control : app.Control) : Prop where
  clock : control.execution.application.clock = stageClock control.execution.environmentRecall
  counted : ∀ who, (control.execution.recall who).length +
    (if control.actor = some who then 1 else 0) = visitCount control.execution.environmentRecall who
  activation : ∀ who, control.actor = some who →
    (control.execution.environmentRecall.length = 3 ∧ who = alice) ∨
      (control.execution.environmentRecall.length = 5 ∧ who = alice) ∨
      (control.execution.environmentRecall.length = 6 ∧ who = alice) ∨
      (control.execution.environmentRecall.length = 11 ∧ who = bob)

def clockPhaseInvariant : app.ProtocolState → Prop
  | none => True
  | some control => ClockPhase control

private theorem clockPhase_initial (state : app.State)
    (supported : state ∈ (initialLaw setup).support) :
    ClockPhase ⟨horizon, none, ReactiveApplication.Execution.initial app state⟩ := by
  obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
  refine ⟨rfl, ?_, by simp⟩
  intro who
  simp [ReactiveApplication.Execution.initial, visitCount]

private theorem clockPhase_respond (control : app.Control) (phase : ClockPhase control)
    (who : Player) (active : control.actor = some who) (response : app.Action) :
    ClockPhase { control with
      actor := none
      execution := control.execution.respond app who response } := by
  obtain ⟨_, publicEq⟩ :=
    (runtime setup).reactive_respond_application leaks control.execution who response
  have clockEq := congrArg PublicView.clock publicEq
  dsimp only [State.publicView] at clockEq
  refine ⟨?_, ?_, by intro observer impossible; cases impossible⟩
  · rw [clockEq, app.respond_environmentRecall]
    exact phase.clock
  · intro observer
    have counted := phase.counted observer
    rw [active] at counted
    simpa only [app.respond_recall_length, app.respond_environmentRecall,
      Option.some.injEq, reduceCtorEq, ite_false, Nat.add_zero, eq_comm] using counted

private theorem clockPhase_environment (control : app.Control) (phase : ClockPhase control)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control))
    (remaining : Nat) (counted : control.remaining = remaining + 1)
    (inactive : control.actor = none) (next : app.Execution) (command : app.Command)
    (selected : command ∈ (scheduler control.execution.environmentRecall
      (control.execution.observeEnvironment app)).support)
    (moved : next ∈ (control.execution.environmentStep app command).support) :
    ClockPhase ⟨remaining, command.actor? app, next⟩ := by
  have appended := environmentStep_recall_append control.execution next command moved
  have length : next.environmentRecall.length = control.execution.environmentRecall.length + 1 := by
    rw [appended, List.length_append, List.length_singleton]
  have beforeEnd : control.execution.environmentRecall.length < horizon := by
    have budget := app.raw_trace_accounted (initialLaw setup) horizon scheduler trace
    change control.execution.environmentRecall.length + control.remaining = horizon at budget
    rw [counted] at budget
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [appended, stageClock_append _ _ command beforeEnd selected,
      environment_clock control.execution next command moved, phase.clock]
  · intro who
    have previous := phase.counted who
    rw [inactive] at previous
    simp only [reduceCtorEq, ite_false, Nat.add_zero] at previous
    rw [app.environmentStep_recall control.execution next command moved, appended,
      visitCount_append _ _ command beforeEnd selected who, ← previous]
  · intro who active
    have positions := selected_activation _ _ command beforeEnd selected who active
    simpa only [length] using positions

private theorem clockPhase_transition (before after : app.ProtocolState)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace before)
    (valid : clockPhaseInvariant before) (joint : Player → Option app.Action)
    (reached : after ∈ (app.transition (initialLaw setup) horizon scheduler before joint).support) :
    clockPhaseInvariant after := by
  cases before with
  | none =>
      obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ reached
      exact clockPhase_initial state supported
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          cases (PMF.mem_support_pure_iff _ _).mp reached
          exact clockPhase_respond _ valid who rfl _
      | none =>
          cases remaining with
          | zero =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              exact valid
          | succ remaining =>
              obtain ⟨command, selected, realized⟩ :=
                Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
              obtain ⟨next, moved, rfl⟩ := PMF.support_map .. ▸ realized
              exact clockPhase_environment _ valid trace remaining rfl rfl next command
                selected moved

theorem clockPhase_history : ∀ {state}
    (_trace : (app.protocol (initialLaw setup) horizon scheduler).Trace state),
    clockPhaseInvariant state
  | _, .start => trivial
  | _, .extend prior joint _ reached =>
      clockPhase_transition _ _ prior (clockPhase_history prior) joint reached

theorem bob_raw_decision_resources (control : app.Control)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control))
    (active : control.actor = some bob) :
    control.execution.environmentRecall.length = 11 ∧
      control.execution.application.clock = 3 ∧
      control.execution.recall bob = [] ∧
      (control.execution.recall alice).length = 2 ∧ trace.length = 14 := by
  have phase : ClockPhase control := clockPhase_history trace
  have stage : control.execution.environmentRecall.length = 11 := by
    rcases phase.activation bob active with ⟨_, same⟩ | ⟨_, same⟩ | ⟨_, same⟩ | ⟨same, _⟩
    · exact ((by decide : bob ≠ alice) same).elim
    · exact ((by decide : bob ≠ alice) same).elim
    · exact ((by decide : bob ≠ alice) same).elim
    · exact same
  have clock : control.execution.application.clock = 3 := by
    rw [phase.clock]
    simp [stageClock, stage]
  have empty : control.execution.recall bob = [] := by
    simpa [visitCount, stage, active] using phase.counted bob
  have aliceCount : (control.execution.recall alice).length = 2 := by
    simpa [visitCount, stage, active] using phase.counted alice
  refine ⟨stage, clock, empty, aliceCount, ?_⟩
  rw [app.trace_length_of_control (initialLaw setup) horizon scheduler control trace, stage]
  change 1 + 11 + ((control.execution.recall alice).length +
    (control.execution.recall bob).length) = 14
  rw [aliceCount, empty]
  rfl

end Vegas.PrivateResolutionFork
