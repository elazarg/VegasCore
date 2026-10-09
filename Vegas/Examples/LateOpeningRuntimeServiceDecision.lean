/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeServiceCompletion

/-! # The owner decision positions of the public two-late service

These facts classify every actual raw decision history. At Bob's extra
callback the first binding has already completed, as checked by the public
completion gate. Every protected response is followed by author-wide service.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeService

open SourceProgram EventGraph EventGraphRuntime Interaction
  GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource

def DecisionSlot (who : Player) (execution : app.Execution) : Prop :=
  (who = alice ∧ execution.environmentRecall.length ∈ ({1, 4, 8} : Finset Nat)) ∨
    (who = bob ∧ (execution.environmentRecall.length ∈ ({5, 12, 20} : Finset Nat) ∨
      (execution.environmentRecall.length = 14 ∧
        bobBindEvent ∈ execution.application.publicView.observation.completionOrder)))

private theorem activation_position (weight : ℝ) (nonnegative : 0 ≤ weight)
    (position : Nat) (view : app.EnvironmentView) (who : Player)
    (selected : (.activate who : app.Command) ∈
      (stageChoice weight nonnegative position view).support) :
    (who = alice ∧ position ∈ ({0, 3, 7} : Finset Nat)) ∨
      (who = bob ∧ (position ∈ ({4, 11, 19} : Finset Nat) ∨
        (position = 13 ∧ bobBindEvent ∈ view.application.observation.completionOrder))) := by
  by_cases inside : position < 26
  · interval_cases position
    all_goals simp only [stageChoice, PMF.mem_support_pure_iff] at selected
    case «0» | «3» | «7» | «4» | «11» | «19» =>
      cases ReactiveApplication.Command.activate.inj selected
      simp
    case «1» =>
      have passive := (latestAuthor_passive alice view).1
      rw [← selected] at passive
      cases passive
    case «5» | «12» | «20» =>
      have passive := (latestAuthor_passive bob view).1
      rw [← selected] at passive
      cases passive
    case «8» =>
      have passive := (lottery_passive weight nonnegative view _ selected).1
      cases passive
    case «13» =>
      split at selected
      · cases ReactiveApplication.Command.activate.inj selected
        exact Or.inr ⟨rfl, Or.inr ⟨rfl, by assumption⟩⟩
      · cases selected
    case «14» =>
      split at selected
      · have passive := (latestAuthor_passive bob view).1
        rw [← selected] at passive
        cases passive
      · cases selected
    all_goals cases selected
  · have idle : stageChoice weight nonnegative position view = PMF.pure .wait := by
      unfold stageChoice
      split <;> first | omega | rfl
    rw [idle, PMF.mem_support_pure_iff] at selected
    cases selected

private theorem activated_application (execution next : app.Execution) (who : Player)
    (reached : next ∈ (execution.environmentStep app (.activate who)).support) :
    next.application = execution.application := by
  obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
  obtain ⟨sample, _, rfl⟩ := PMF.support_map .. ▸ supported
  rfl

private theorem activation_slot (weight : ℝ) (nonnegative : 0 ≤ weight)
    (execution next : app.Execution) (command : app.Command) (who : Player)
    (selected : command ∈ (scheduler weight nonnegative execution.environmentRecall
      (execution.observeEnvironment app)).support)
    (reached : next ∈ (execution.environmentStep app command).support)
    (active : command.actor? app = some who) : DecisionSlot who next := by
  have equal : command = .activate who := by
    cases command with
    | activate actor =>
        cases Option.some.inj active
        rfl
    | «include» _ => cases active
    | application _ => cases active
    | wait => cases active
  subst command
  have located := activation_position weight nonnegative execution.environmentRecall.length
    (execution.observeEnvironment app) who selected
  have length : next.environmentRecall.length = execution.environmentRecall.length + 1 := by
    rw [environmentStep_recall_append execution next (.activate who) reached]
    simp only [List.length_append, List.length_singleton]
  unfold DecisionSlot
  rw [length, activated_application execution next who reached]
  rcases located with ⟨rfl, positions⟩ | ⟨rfl, positions | ⟨position, completed⟩⟩
  · refine Or.inl ⟨rfl, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at positions ⊢
    omega
  · refine Or.inr ⟨rfl, Or.inl ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at positions ⊢
    omega
  · exact Or.inr ⟨rfl, Or.inr ⟨by omega, completed⟩⟩

private def DecisionPhase : app.ProtocolState → Prop
  | none => True
  | some control => ∀ who, control.actor = some who → DecisionSlot who control.execution

private theorem decision_phase_history (weight : ℝ) (nonnegative : 0 ≤ weight) :
    ∀ {state} (_trace : (app.protocol initial horizon (scheduler weight nonnegative)).Trace state),
      DecisionPhase state
  | _, .start => trivial
  | _, @ExecutionProtocol.Trace.extend _ _ source target prior joint legal reached => by
      have valid := decision_phase_history weight nonnegative prior
      change target ∈ (app.transition initial horizon (scheduler weight nonnegative)
        source joint).support at reached
      cases source with
      | none =>
          obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
          intro who impossible
          cases impossible
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | some who =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              intro observer impossible
              cases impossible
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, selected, moved⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  intro who active
                  exact activation_slot weight nonnegative execution next command who
                    selected supported active

/-- Every legal raw owner decision lies at one of the advertised public
callback positions, including the binding-completion gate of the extra turn. -/
theorem active_cursor (weight : ℝ) (nonnegative : 0 ≤ weight) (control : app.Control)
    (trace : (app.protocol initial horizon (scheduler weight nonnegative)).Trace (some control))
    (who : Player) (active : control.actor = some who) : DecisionSlot who control.execution :=
  decision_phase_history weight nonnegative trace who active

/-- Bob's responses and Alice's clock-zero response receive immediate
author-wide service, independently of the raw submission they choose. -/
theorem protected_response_scheduler (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (app.protocol initial horizon (scheduler weight nonnegative)).Trace (some control))
    (who : Player) (active : control.actor = some who) (action : app.Action)
    (tracked : who = bob ∨ control.execution.application.clock = 0) :
    scheduler weight nonnegative (control.execution.respond app who action).environmentRecall
      ((control.execution.respond app who action).observeEnvironment app) =
        PMF.pure (latestAuthor who
          ((control.execution.respond app who action).observeEnvironment app)) := by
  have located := active_cursor weight nonnegative control trace who active
  have clock := clock_history weight nonnegative control trace
  rw [app.respond_environmentRecall]
  change stageChoice weight nonnegative control.execution.environmentRecall.length _ = _
  rcases located with ⟨rfl, positions⟩ | ⟨rfl, positions | ⟨position, completed⟩⟩
  · have zero : control.execution.application.clock = 0 := by
      rcases tracked with impossible | zero
      · exact (by decide : alice ≠ bob) impossible |>.elim
      · exact zero
    have position : control.execution.environmentRecall.length = 1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at positions
      rcases positions with position | position | position
      · exact position
      · rw [position, show clockAt 4 = 1 by decide] at clock
        omega
      · rw [position, show clockAt 8 = 2 by decide] at clock
        omega
    rw [position]
    rfl
  · simp only [Finset.mem_insert, Finset.mem_singleton] at positions
    rcases positions with position | position | position <;> rw [position] <;> rfl
  · rw [position]
    have visible := (runtime.reactive_respond_application leaks control.execution bob action).2
    let updated := control.execution.respond app bob action
    have afterCompleted :
        bobBindEvent ∈ updated.application.publicView.observation.completionOrder :=
      visible.symm ▸ completed
    let afterView := (control.execution.respond app bob action).observeEnvironment app
    have gate : bobBindEvent ∈ afterView.application.observation.completionOrder := afterCompleted
    simp only [stageChoice]
    split <;> rfl

end Vegas.Examples.LateOpeningRuntimeService
