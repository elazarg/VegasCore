/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.IdealCommitments
import GameTheory.Math.Probability.FinDist

/-! # Products indexed by first registrations

An occupied handle contributes its fixed factor once. The private table is
used only as a proof readout: neither these factors nor their product are
runtime observations. Products may be zero, and no cancellation is required.
-/

noncomputable section

namespace Interaction.IdealCommitments

universe uPrincipal uSlot uValue

variable {Principal : Type uPrincipal} {Slot : Type uSlot} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Slot]

/-- The factors of the tracked handles that have already been registered. -/
def registrationWeight (state : IdealCommitments Principal Slot Value)
    (handles : Finset (CommitmentHandle Principal Slot))
    (factor : CommitmentHandle Principal Slot → ℝ) : ℝ :=
  ∏ handle ∈ handles, if (state.lookup handle).isSome then factor handle else 1

omit [DecidableEq Principal] [DecidableEq Slot] in
@[simp] theorem registrationWeight_empty
    (handles : Finset (CommitmentHandle Principal Slot))
    (factor : CommitmentHandle Principal Slot → ℝ) :
    (empty : IdealCommitments Principal Slot Value).registrationWeight handles factor = 1 := by
  simp only [registrationWeight, lookup_empty, Option.isSome_none, Bool.false_eq_true,
    ↓reduceIte, Finset.prod_const_one]

/-- A fresh seal introduces precisely one factor when its handle is tracked.
Repeated seals, including attempts with different values, leave the product
unchanged because the underlying service is write-once. -/
theorem registrationWeight_sealValue (state : IdealCommitments Principal Slot Value)
    (handles : Finset (CommitmentHandle Principal Slot))
    (factor : CommitmentHandle Principal Slot → ℝ)
    (owner : Principal) (slot : Slot) (value : Value) :
    (state.sealValue owner slot value).state.registrationWeight handles factor =
      state.registrationWeight handles factor *
        if (owner, slot) ∈ handles ∧ state.lookup (owner, slot) = none
        then factor (owner, slot) else 1 := by
  classical
  cases hlookup : state.lookup (owner, slot) with
  | some stored =>
      rw [seal_occupied state owner slot stored value hlookup]
      simp only [reduceCtorEq, and_false, ↓reduceIte, mul_one]
  | none =>
      have hnew := (state.seal_first owner slot value hlookup).2
      have hother : ∀ handle, handle ≠ (owner, slot) →
          (state.sealValue owner slot value).state.lookup handle = state.lookup handle := by
        intro handle hne
        apply state.seal_other owner handle.1 slot handle.2 value hlookup
        by_cases howner : handle.1 = owner
        · exact Or.inr (fun hslot => hne (Prod.ext howner hslot))
        · exact Or.inl howner
      by_cases hmem : (owner, slot) ∈ handles
      · simp only [hmem, and_self, ↓reduceIte]
        unfold registrationWeight
        rw [← Finset.mul_prod_erase handles _ hmem,
          ← Finset.mul_prod_erase handles
            (fun handle => if (state.lookup handle).isSome then factor handle else 1) hmem]
        simp only [hnew, Option.isSome_some, ↓reduceIte, hlookup,
          Option.isSome_none, Bool.false_eq_true, one_mul]
        rw [mul_comm]
        congr 1
        apply Finset.prod_congr rfl
        intro handle hhandle
        rw [hother handle (Finset.mem_erase.mp hhandle).1]
      · simp only [hmem, false_and, ↓reduceIte, mul_one, registrationWeight]
        apply Finset.prod_congr rfl
        intro handle hhandle
        rw [hother handle (fun heq => hmem (heq ▸ hhandle))]

end Interaction.IdealCommitments
