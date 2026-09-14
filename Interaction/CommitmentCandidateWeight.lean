/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.CommitmentCandidates
import GameTheoryExtensions.Math.Finset
import GameTheory.Math.Probability.FinDist

/-! # Products indexed by prepared candidate openings

Each openable tracked handle contributes one fixed factor. Fresh and permanently
unopenable handles contribute one. Acceptance preserves this product even when
it changes the catalog; only successful fresh preparation introduces a factor.
The catalog is a proof readout, not an additional runtime observation.
-/

noncomputable section

namespace Interaction.CommitmentCandidates

universe uPrincipal uSlot uValue

variable {Principal : Type uPrincipal} {Slot : Type uSlot} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Slot]

/-- Product of the fixed factors at openable tracked handles. -/
def preparationWeight (state : CommitmentCandidates Principal Slot Value)
    (handles : Finset (CommitmentHandle Principal Slot))
    (factor : CommitmentHandle Principal Slot → ℝ) : ℝ :=
  ∏ handle ∈ handles, if (state.lookup handle).opening?.isSome then factor handle else 1

omit [DecidableEq Principal] [DecidableEq Slot] in
@[simp] theorem preparationWeight_empty
    (handles : Finset (CommitmentHandle Principal Slot))
    (factor : CommitmentHandle Principal Slot → ℝ) :
    (empty : CommitmentCandidates Principal Slot Value).preparationWeight handles factor = 1 := by
  simp only [preparationWeight, lookup_empty, CommitmentCandidate.opening?, Option.isSome_none,
    Bool.false_eq_true, ↓reduceIte, Finset.prod_const_one]

/-- Successful fresh preparation introduces precisely one tracked factor;
attempts to prepare already fixed handles leave the product unchanged. -/
theorem preparationWeight_prepare [DecidableEq Value]
    (state : CommitmentCandidates Principal Slot Value)
    (handles : Finset (CommitmentHandle Principal Slot))
    (factor : CommitmentHandle Principal Slot → ℝ)
    (owner : Principal) (slot : Slot) (value : Value) :
    (state.prepare owner slot value).preparationWeight handles factor =
      state.preparationWeight handles factor *
        if (owner, slot) ∈ handles ∧ state.lookup (owner, slot) = .fresh
        then factor (owner, slot) else 1 := by
  cases hlookup : state.lookup (owner, slot) with
  | fresh =>
      simp only [and_true]
      apply Finset.prod_ite_of_single_activation
      · simp only [hlookup, CommitmentCandidate.opening?, Option.isSome_none]
      · simp only [lookup_prepare_self, hlookup, CommitmentCandidate.opening?, Option.isSome_some]
      · intro other hother
        rw [state.lookup_prepare_other owner slot value other hother]
  | openable stored | unopenable =>
      simp only [reduceCtorEq, and_false, ↓reduceIte, mul_one]
      have hsame : state.prepare owner slot value = state := by rw [prepare, hlookup]
      rw [hsame]

/-- Public acceptance creates no opening, so it introduces no probability
factor, including for a previously fresh handle. -/
theorem preparationWeight_accept (state : CommitmentCandidates Principal Slot Value)
    (handles : Finset (CommitmentHandle Principal Slot))
    (factor : CommitmentHandle Principal Slot → ℝ)
    (accepted : CommitmentHandle Principal Slot) :
    (state.accept accepted).preparationWeight handles factor =
      state.preparationWeight handles factor := by
  apply Finset.prod_congr rfl
  intro queried _
  have hopening : ((state.accept accepted).lookup queried).opening? =
      (state.lookup queried).opening? := by
    apply Option.ext
    intro value
    simp only [CommitmentCandidate.opening?_eq_some_iff,
      state.lookup_accept_openable_iff accepted queried value]
  rw [hopening]

end Interaction.CommitmentCandidates
