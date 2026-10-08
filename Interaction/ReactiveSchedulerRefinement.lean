/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveProtocol

/-! # Legal histories under scheduler support refinement

Removing supported scheduler commands removes possible raw histories without
changing their state, observations or available player actions. This transports
all-history operational service guarantees, not assessments or equilibria.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)
  (initial : PMF app.State) (horizon : Nat) (smaller larger : app.Scheduler)
  (included : ∀ past view, (smaller past view).support ⊆ (larger past view).support)

include included

/-- Restricting the scheduler support restricts each actual transition support. -/
theorem transition_support_subset_of_scheduler_support_subset
    (state : app.ProtocolState) (joint : Principal → Option app.Action) :
    (app.transition initial horizon smaller state joint).support ⊆
      (app.transition initial horizon larger state joint).support := by
  cases state with
  | none => exact Set.Subset.rfl
  | some control =>
      cases current : control.actor with
      | some who => simp only [transition, current]; exact Set.Subset.rfl
      | none =>
          cases remaining : control.remaining with
          | zero => simp only [transition, current, remaining]; exact Set.Subset.rfl
          | succ remaining =>
              simp only [transition, current, remaining, PMF.support_bind]
              intro next supported
              obtain ⟨command, chosen, reached⟩ := Set.mem_iUnion₂.mp supported
              exact Set.mem_iUnion₂.mpr ⟨command, included _ _ chosen, reached⟩

/-- Every legal raw trace under the refined scheduler is also legal under the
original scheduler, with the same realized controls and player responses. -/
def trace_of_scheduler_support_subset :
    ∀ {state}, (app.protocol initial horizon smaller).Trace state →
      (app.protocol initial horizon larger).Trace state
  | _, .start => .start
  | _, .extend prior joint legal reached =>
      .extend (trace_of_scheduler_support_subset prior)
        joint legal
        (app.transition_support_subset_of_scheduler_support_subset
          initial horizon smaller larger included _ _ reached)

omit [DecidableEq Principal] in
/-- A support-refined scheduler inherits finite nature from its original. -/
theorem finiteNature_of_scheduler_support_subset
    [app.FiniteNature initial larger] : app.FiniteNature initial smaller := by
  classical
  exact {
    toFiniteEnvironment := inferInstance
    initial_finite := FiniteNature.initial_finite (app := app) larger
    scheduler_finite := fun past view =>
      (FiniteNature.scheduler_finite initial past view).subset (included past view) }

end Interaction.ReactiveApplication
