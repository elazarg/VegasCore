/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeOptionalOpening
import Interaction.ReactiveResponseAccounting
import Interaction.ReactiveServiceInvariant

/-! # The complete information class of the optional receiver callback

The actual clock and own response count distinguish this callback from the
earlier binding callback at the same clock. One ready, timely and clean actual
representative therefore supplies those properties throughout its native
information class, including histories with arbitrary earlier raw actions.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeOptionalInformation

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeOptionalOpening

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

private def prefixActors : List (Option Player) :=
  [some alice, none, none, some alice, some bob, none,
    none, some alice, none, none, none, some bob, none]

private theorem prefix_actor (position : Nat) (early : position < 13)
    (view : app.EnvironmentView) (command : app.Command)
    (selected : command ∈ (stageChoice weight nonnegative position view).support) :
    some (command.actor? app) = prefixActors[position]? := by
  interval_cases position <;> simp only [stageChoice, PMF.mem_support_pure_iff] at selected
  all_goals try subst command
  all_goals first
    | exact congrArg some (latestAuthor_passive _ _).1
    | exact congrArg some (lottery_passive weight nonnegative view command selected).1
    | rfl

private def PrefixActors (execution : app.Execution) : Prop :=
  (execution.environmentRecall.take 13).map (fun entry => entry.command.actor? app) =
    prefixActors.take execution.environmentRecall.length

private theorem prefix_invariant :
    app.ServiceInvariant (LateOpeningRuntimeService.scheduler weight nonnegative) PrefixActors where
  respond execution who action valid := by
    simpa only [PrefixActors, app.respond_environmentRecall] using valid
  environment execution next command valid selected reached := by
    have advanced := app.environmentStep_environmentRecall execution next command reached
    unfold PrefixActors at valid ⊢
    rw [advanced, List.length_append, List.length_singleton]
    by_cases early : execution.environmentRecall.length < 13
    · rw [List.take_append, List.map_append, valid]
      have takeLast :
          ([⟨execution.observeEnvironment app, command⟩] : List app.EnvironmentEntry).take
            (13 - execution.environmentRecall.length) =
            [⟨execution.observeEnvironment app, command⟩] :=
        List.take_of_length_le (by simp only [List.length_singleton]; omega)
      rw [takeLast, List.map_cons, List.map_nil, List.take_add_one,
        ← prefix_actor weight nonnegative execution.environmentRecall.length early
          (execution.observeEnvironment app) command selected]
      rfl
    · rw [List.take_append_of_le_length (by omega)]
      have before : prefixActors.take execution.environmentRecall.length = prefixActors :=
        List.take_of_length_le (by change 13 ≤ execution.environmentRecall.length; omega)
      have after : prefixActors.take (execution.environmentRecall.length + 1) = prefixActors :=
        List.take_of_length_le (by change 13 ≤ execution.environmentRecall.length + 1; omega)
      rw [after]
      exact valid.trans before

private theorem prefix_history (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control)) :
    PrefixActors control.execution :=
  (prefix_invariant weight nonnegative).history initial LateOpeningRuntimeService.horizon
    (fun _ _ => rfl) trace

/-- At the first binding callback Bob has exactly one earlier response,
without restricting what that response emitted. -/
theorem binding_recall_length (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (active : control.actor = some bob)
    (cursor : control.execution.environmentRecall.length = 12) :
    (control.execution.recall bob).length = 1 := by
  have actors := prefix_history weight nonnegative control trace
  unfold PrefixActors at actors
  rw [List.take_of_length_le (by omega), cursor] at actors
  have count := congrArg (fun entries : List (Option Player) =>
    (entries.filterMap id).count bob) actors
  simp only [List.filterMap_map, Function.comp_def, id_eq] at count
  change (app.activationHistory control.execution).count bob = 2 at count
  have responded := app.response_count_history initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) control trace bob
  rw [active, count] at responded
  simp only [↓reduceIte] at responded
  omega

/-- At the optional callback Bob has exactly two earlier responses. The
conditional activation itself is counted from the actual final command. -/
theorem optional_recall_length (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (active : control.actor = some bob)
    (cursor : control.execution.environmentRecall.length = 14) :
    (control.execution.recall bob).length = 2 := by
  obtain ⟨past, view, command, advanced, actor⟩ := app.active_environment_entry initial
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      control trace bob active
  have length : past.length = 13 := by
    rw [advanced, List.length_append, List.length_singleton] at cursor
    omega
  have actors := prefix_history weight nonnegative control trace
  unfold PrefixActors at actors
  rw [advanced, List.length_append, List.length_singleton,
    List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)] at actors
  have full : prefixActors.take (past.length + 1) = prefixActors :=
    List.take_of_length_le (by change 13 ≤ past.length + 1; omega)
  rw [full] at actors
  have count := congrArg (fun entries : List (Option Player) =>
    (entries.filterMap id).count bob) actors
  simp only [List.filterMap_map, Function.comp_def, id_eq] at count
  change (past.filterMap (fun entry => entry.command.actor? app)).count bob = 2 at count
  have responded := app.response_count_history initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) control trace bob
  unfold ReactiveApplication.activationHistory at responded
  rw [active, advanced, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
    actor, List.count_append, count] at responded
  change (control.execution.recall bob).length + 1 = 2 + 1 at responded
  omega

theorem optional_remaining_same_information (decision : DecisionHistory weight nonnegative)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (active : control.actor = some bob)
    (sameRecall : decision.execution.recall bob = control.execution.recall bob)
    (sameView : decision.execution.observe app bob = control.execution.observe app bob) :
    control.remaining = 12 := by
  have accounted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) decision.trace
  change decision.execution.environmentRecall.length + 12 = 26 at accounted
  have atOptional : decision.execution.environmentRecall.length = 14 := by omega
  have remembered := optional_recall_length weight nonnegative ⟨12, some bob, decision.execution⟩
    decision.trace rfl atOptional
  have clock : decision.execution.application.clock = 3 := by
    rw [clock_history weight nonnegative _ decision.trace, atOptional]
    decide
  have sameClock := congrArg (fun view : app.PlayerView => view.application.publicView.clock)
    sameView
  change decision.execution.application.clock = control.execution.application.clock at sameClock
  have actualClock : LateOpeningRuntimeService.clockAt control.execution.environmentRecall.length =
      3 := (clock_history weight nonnegative control trace).symm.trans
        (sameClock.symm.trans clock)
  have slot := active_cursor weight nonnegative control trace bob active
  rcases slot with ⟨impossible, _⟩ | ⟨_, positions | ⟨position, _⟩⟩
  · cases impossible
  · simp only [Finset.mem_insert, Finset.mem_singleton] at positions
    rcases positions with position | position | position
    · rw [position] at actualClock
      exact ((by decide : LateOpeningRuntimeService.clockAt 5 ≠ 3) actualClock).elim
    · have earlier := binding_recall_length weight nonnegative control trace active position
      rw [sameRecall] at remembered
      omega
    · rw [position] at actualClock
      exact ((by decide : LateOpeningRuntimeService.clockAt 20 ≠ 3) actualClock).elim
  · have counted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) trace
    change control.execution.environmentRecall.length + control.remaining = 26 at counted
    omega

/-- Every actual hidden history of this information site has the same
selected answer and complete operational opening interface. -/
theorem decision_of_information
    (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      bob site.1)
    (decision : DecisionHistory weight nonnegative)
    (current : representative.1.state = some ⟨12, some bob, decision.execution⟩)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :
    ∃ result : DecisionHistory weight nonnegative,
      history.1.state = some ⟨12, some bob, result.execution⟩ ∧
      decision.execution.recall bob = result.execution.recall bob ∧
      decision.execution.observe app bob = result.execution.observe app bob ∧
      decision.answer = result.answer := by
  classical
  have active := InformationModel.InformationSite.active _ site history
  obtain ⟨control, stateEq, actor⟩ := app.control_of_active initial
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      (rawMenu.toRawHistory _ _ _ history.1) bob active
  change history.1.state = some control at stateEq
  have rawTrace := stateEq ▸ rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) history.1.trace
  have information := representative.2.trans history.2.symm
  change (rawMenu.signals _ _ _).infoOf bob representative.1.trace =
    (rawMenu.signals _ _ _).infoOf bob history.1.trace at information
  rw [rawMenu.info, rawMenu.info] at information
  change app.observe bob representative.1.state = app.observe bob history.1.state at information
  rw [current, stateEq] at information
  simp only [ReactiveApplication.observe, actor, ↓reduceIte] at information
  have sameRecall := congrArg Prod.fst (Option.some.inj information)
  have sameView := congrArg Prod.snd (Option.some.inj information)
  have remaining := optional_remaining_same_information weight nonnegative decision control rawTrace
    actor sameRecall sameView
  have sameControl : control = ⟨12, some bob, control.execution⟩ := by
    cases control
    simp only [ReactiveApplication.Control.mk.injEq] at actor remaining ⊢
    exact ⟨remaining, actor, trivial⟩
  have optionalTrace := sameControl ▸ rawTrace
  let result : DecisionHistory weight nonnegative :=
    ⟨control.execution, optionalTrace, decision.answer,
      (LateOpeningRuntimeBobInformation.bound_same_view _ _ sameView).symm.trans decision.bound,
      LateOpeningRuntimeBobInformation.ready_same_view _ _ sameView decision.ready,
      LateOpeningRuntimeBobInformation.timely_same_view _ _ sameView decision.timely,
      LateOpeningRuntimeBobInformation.clean_same_information _ _
        (app.history_inputRecall initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative) decision.trace)
        (app.history_inputRecall initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative) rawTrace)
        sameRecall sameView decision.clean⟩
  exact ⟨result, stateEq.trans (congrArg some sameControl), sameRecall, sameView, rfl⟩

def decisionOfInformation
    (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      bob site.1) (decision : DecisionHistory weight nonnegative)
    (current : representative.1.state = some ⟨12, some bob, decision.execution⟩)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :=
  (decision_of_information weight nonnegative site representative decision current history).choose

theorem decisionOfInformation_spec
    (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      bob site.1) (decision : DecisionHistory weight nonnegative)
    (current : representative.1.state = some ⟨12, some bob, decision.execution⟩)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :
    let result :=
      decisionOfInformation weight nonnegative site representative decision current history
    history.1.state = some ⟨12, some bob, result.execution⟩ ∧
      decision.execution.recall bob = result.execution.recall bob ∧
      decision.execution.observe app bob = result.execution.observe app bob ∧
      decision.answer = result.answer :=
  (decision_of_information weight nonnegative site representative decision current
    history).choose_spec

theorem canonical_same_information (first second : DecisionHistory weight nonnegative)
    (sameRecall : first.execution.recall bob = second.execution.recall bob)
    (sameView : first.execution.observe app bob = second.execution.observe app bob) :
    LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
      (first.execution.recall bob) (first.execution.observe app bob) bobRevealEvent true =
        LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
          (second.execution.recall bob) (second.execution.observe app bob) bobRevealEvent true := by
  rw [sameRecall, sameView]

end Vegas.Examples.LateOpeningRuntimeOptionalInformation
