/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveRecall
import Interaction.ReactiveInvariant
import Interaction.ReactiveServiceInvariant

/-! # Monotone application facts in remembered observations

Every remembered pre-response observation predates the current application
state. A monotone observable quantity therefore bounds all such observations,
at every legal history, without honesty or restrictions on private memory.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

theorem respond_entry_origin (execution : app.Execution) (who observer : Principal)
    (action : app.Action) (entry : app.PlayerEntry)
    (member : entry ∈ (execution.respond app who action).recall observer) :
    entry ∈ execution.recall observer ∨
      (observer = who ∧ entry.beforeView = execution.observe app who) := by
  by_cases same : observer = who
  · subst observer
    rcases action with ⟨transmission⟩
    cases transmission with
    | none =>
        simp only [Execution.respond, ↓reduceIte, List.mem_append, List.mem_singleton] at member
        rcases member with prior | rfl
        · exact Or.inl prior
        · exact Or.inr ⟨rfl, rfl⟩
    | some transmission =>
        simp only [Execution.respond, ↓reduceIte, List.mem_append, List.mem_singleton] at member
        all_goals rcases member with prior | rfl
        all_goals first | exact Or.inl prior | exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl (app.respond_recall_other execution who observer same action ▸ member)

/-- Every retained own response originates at a genuine earlier legal active
callback, with its exact original private before-view. -/
theorem recorded_response_prefix
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control))
    (who : Principal) (entry : app.PlayerEntry) (recorded : entry ∈ control.execution.recall who) :
    ∃ before : app.Control,
      Nonempty ((app.protocol initial horizon scheduler).Trace (some before)) ∧
      before.actor = some who ∧ entry.beforeView = before.execution.observe app who := by
  have origin : ∀ {state} (_history : (app.protocol initial horizon scheduler).Trace state),
      state.elim True (fun current => ∀ who entry, entry ∈ current.execution.recall who →
        ∃ before : app.Control,
          Nonempty ((app.protocol initial horizon scheduler).Trace (some before)) ∧
          before.actor = some who ∧ entry.beforeView = before.execution.observe app who) := by
    intro state history
    induction history with
    | start => trivial
    | @extend source target prior joint legal reached ih =>
        change target ∈ (app.transition initial horizon scheduler source joint).support at reached
        cases source with
        | none =>
            obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
            intro who entry member
            exact (List.not_mem_nil member).elim
        | some current =>
            rcases current with ⟨remaining, actor, execution⟩
            cases actor with
            | some acting =>
                cases (PMF.mem_support_pure_iff _ _).mp reached
                intro who entry member
                rcases app.respond_entry_origin execution acting who
                    ((joint acting).getD ⟨none⟩) entry member with earlier | fresh
                · exact ih who entry earlier
                · rcases fresh with ⟨same, viewed⟩
                  subst who
                  exact ⟨⟨remaining, some acting, execution⟩, ⟨prior⟩, rfl, viewed⟩
            | none =>
                cases remaining with
                | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
                | succ remaining =>
                    obtain ⟨command, _, moved⟩ :=
                      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                    obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                    intro who entry member
                    rw [app.environmentStep_recall execution next command supported] at member
                    exact ih who entry member
  exact origin trace who entry recorded

variable {Value : Type*} [Preorder Value]

def Execution.RecallBound (observed : app.LocalObservation → Value) (value : app.State → Value)
    (execution : app.Execution) : Prop :=
  ∀ who entry, entry ∈ execution.recall who →
    observed entry.beforeView.application ≤ value execution.application

theorem recallBoundInvariant (observed : app.LocalObservation → Value) (value : app.State → Value)
    (agrees : ∀ state who, observed (app.observePlayer state who) = value state)
    (monotone : ∀ lower, app.Invariant (fun state => lower ≤ value state))
    (scheduler : app.Scheduler) :
    app.ServiceInvariant scheduler (Execution.RecallBound app observed value) where
  respond execution who action valid := by
    have grows := (monotone (value execution.application)).respond execution who action le_rfl
    intro observer entry member
    rcases app.respond_entry_origin execution who observer action entry member with prior | fresh
    · exact (valid observer entry prior).trans grows
    · rw [fresh.2]
      change observed (app.observePlayer execution.application who) ≤ _
      rw [agrees]
      exact grows
  environment execution next command valid _ reached := by
    have grows := (monotone (value execution.application)).environmentStep
      execution next command le_rfl reached
    intro who entry member
    rw [app.environmentStep_recall execution next command reached] at member
    exact (valid who entry member).trans grows

theorem recallBound_history (observed : app.LocalObservation → Value) (value : app.State → Value)
    (agrees : ∀ state who, observed (app.observePlayer state who) = value state)
    (monotone : ∀ lower, app.Invariant (fun state => lower ≤ value state))
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control)) :
    control.execution.RecallBound app observed value :=
  (app.recallBoundInvariant observed value agrees monotone scheduler).history initial horizon
    (fun _ _ _ _ member => False.elim (List.not_mem_nil member)) trace

end Interaction.ReactiveApplication
