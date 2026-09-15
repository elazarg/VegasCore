/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.BoundPublication

/-! # Failure-sensitive guard semantics

Small executable examples distinguish null-vacuous obligations from ordinary
payoff evaluation. Static guard support is semantic: enlarging it preserves
ordinary evaluation but can change which failed inputs discharge the guard.
-/

namespace InteractionTests.GuardFailure

open Interaction

private abbrev Value (_ : Bool) := Bool

/-- The subject must publish `true`; there are no other required inputs. -/
private def unary : PublicationGuard Value where
  subject := true
  dependencies := {true}
  subject_mem := by simp
  test values := values ⟨true, by simp⟩

/-- The same ordinary test, with another statically required component. -/
private def withDependency : PublicationGuard Value where
  subject := true
  dependencies := Finset.univ
  subject_mem := Finset.mem_univ _
  test values := values ⟨true, Finset.mem_univ _⟩

/-- The tests agree on every fully ordinary input assignment. -/
theorem ordinary_agreement (values : Bool → Bool) :
    unary.check (fun site => .value (values site)) =
      withDependency.check (fun site => .value (values site)) := by
  rw [PublicationGuard.check_values, PublicationGuard.check_values]
  rfl

private def failedDependency : PublicationStore Value :=
  fun site => if site then .pending else .failed

/-- A failed static dependency waives a relation; an absent dependency cannot.
Ordinary Boolean equivalence alone therefore does not permit this rewrite. -/
theorem support_changes_resolution :
    (GuardedPublication.mk [unary]).resolve failedDependency true (some false) true =
      .failed ∧
    (GuardedPublication.mk [withDependency]).resolve failedDependency true
      (some false) true = .value false := by
  decide

private def falseGuard : PublicationGuard (fun _ : Unit => Bool) where
  subject := ()
  dependencies := {()}
  subject_mem := by simp
  test _ := false

/-- Unsatisfiable ordinary guards have a defined failure outcome, for every
candidate, without an in-domain default. -/
theorem false_guard_forces_failure (candidate : Bool) :
    (GuardedPublication.mk [falseGuard]).resolve PublicationStore.empty ()
      (some candidate) () = .failed := by
  cases candidate <;> decide

/-- Failing an unopenable input discharges the dependent guard. No ordinary
Boolean is read from the unopenable binding, whose private status remains. -/
theorem unopenable_dependency :
    let protocol := GuardedPublication.mk [withDependency]
    let initial := ((BoundPublicationState.empty (Value := Value)).bind false .unopenable).bind
      true (.value false)
    let final := (initial.reveal protocol false true).reveal protocol true true
    final.publications false = .failed ∧
      final.publications true = .value false ∧
      final.bindings false = .unopenable := by
  decide

private def comparisonPayoff (left right : Publication Bool) : Int :=
  match left, right with
  | .value first, .value second => if first = second then 1 else 0
  | _, _ => -1

/-- Vacuous guard satisfaction never supplies a successful payoff comparison.
Failure handling is explicit settlement code. -/
theorem failed_value_is_not_a_winning_comparison (right : Publication Bool) :
    comparisonPayoff .failed right = -1 := by
  rfl

end InteractionTests.GuardFailure
