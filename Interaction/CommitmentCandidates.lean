/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.IdealCommitments

/-! # Write-once commitment candidate catalog

This runtime-general catalog records the immutable meaning of each
owner/candidate handle. A slot is a candidate identifier, independent of the
hosting program's source sites. Preparing a fresh handle makes it openable to one value.
Freezing a still-fresh handle records that it is permanently unopenable.
Neither operation changes a handle whose meaning is already fixed.

The catalog is an ideal state component, not a service, runner, or observation
interface. Authentication and policies belong to a hosting runtime.
-/

namespace Interaction

universe uPrincipal uSlot uValue

/-- A candidate is either private and fresh or has a permanently fixed meaning. -/
inductive CommitmentCandidate (Value : Type uValue) where
  | fresh
  | openable (value : Value)
  | unopenable
  deriving DecidableEq

/-- Extract an opening for proof-facing value constraints. Absence here does
not identify fresh and unopenable candidates operationally. -/
def CommitmentCandidate.opening? {Value : Type uValue} : CommitmentCandidate Value → Option Value
  | .openable value => some value
  | .fresh | .unopenable => none

@[simp] theorem CommitmentCandidate.opening?_eq_some_iff {Value : Type uValue}
    (candidate : CommitmentCandidate Value) (value : Value) :
    candidate.opening? = some value ↔ candidate = .openable value := by
  cases candidate <;> simp [opening?]

/-- Owner/slot-indexed meanings for commitment candidates. -/
structure CommitmentCandidates (Principal : Type uPrincipal) (Slot : Type uSlot)
    (Value : Type uValue) where
  table : Principal → Slot → CommitmentCandidate Value

namespace CommitmentCandidates

variable {Principal : Type uPrincipal} {Slot : Type uSlot} {Value : Type uValue}

/-- A catalog in which no handle has been prepared or accepted. -/
def empty : CommitmentCandidates Principal Slot Value where
  table := fun _ _ => .fresh

/-- Inspect the current meaning of a canonical owner/slot handle. -/
def lookup (state : CommitmentCandidates Principal Slot Value)
    (handle : CommitmentHandle Principal Slot) : CommitmentCandidate Value :=
  state.table handle.1 handle.2

/-- Prepare a value only when the authenticated owner/slot handle is fresh. -/
def prepare [DecidableEq Principal] [DecidableEq Slot]
    (state : CommitmentCandidates Principal Slot Value)
    (owner : Principal) (slot : Slot) (value : Value) :
    CommitmentCandidates Principal Slot Value :=
  match state.lookup (owner, slot) with
  | .fresh =>
      ⟨fun otherOwner otherSlot =>
        if otherOwner = owner ∧ otherSlot = slot then .openable value
        else state.table otherOwner otherSlot⟩
  | .openable _ | .unopenable => state

/-- Freeze a handle before exposure. A fresh handle becomes permanently
unopenable; an already fixed handle retains its existing meaning. -/
def freeze [DecidableEq Principal] [DecidableEq Slot]
    (state : CommitmentCandidates Principal Slot Value)
    (handle : CommitmentHandle Principal Slot) :
    CommitmentCandidates Principal Slot Value :=
  match state.lookup handle with
  | .fresh =>
      ⟨fun owner slot =>
        if (owner, slot) = handle then .unopenable else state.table owner slot⟩
  | .openable _ | .unopenable => state

theorem freeze_eq_self_of_not_fresh [DecidableEq Principal] [DecidableEq Slot]
    (state : CommitmentCandidates Principal Slot Value)
    (handle : CommitmentHandle Principal Slot) (fixed : state.lookup handle ≠ .fresh) :
    state.freeze handle = state := by
  cases h : state.lookup handle <;> simp_all [freeze]

theorem prepare_eq_self_of_not_fresh [DecidableEq Principal] [DecidableEq Slot]
    (state : CommitmentCandidates Principal Slot Value)
    (owner : Principal) (slot : Slot) (value : Value)
    (fixed : state.lookup (owner, slot) ≠ .fresh) :
    state.prepare owner slot value = state := by
  cases h : state.lookup (owner, slot) <;> simp_all [prepare]

/-- Check whether a handle was prepared with the claimed value. -/
def verify [DecidableEq Value] (state : CommitmentCandidates Principal Slot Value)
    (handle : CommitmentHandle Principal Slot) (claimed : Value) : Bool :=
  decide (state.lookup handle = .openable claimed)

@[simp] theorem lookup_empty (handle : CommitmentHandle Principal Slot) :
    (empty : CommitmentCandidates Principal Slot Value).lookup handle = .fresh := rfl

@[simp] theorem lookup_prepare_self [DecidableEq Principal] [DecidableEq Slot]
    (state : CommitmentCandidates Principal Slot Value)
    (owner : Principal) (slot : Slot) (value : Value) :
    (state.prepare owner slot value).lookup (owner, slot) =
      match state.lookup (owner, slot) with
      | .fresh => .openable value
      | .openable stored => .openable stored
      | .unopenable => .unopenable := by
  cases hlookup : state.table owner slot <;>
    simp [prepare, lookup, hlookup]

theorem lookup_prepare_other [DecidableEq Principal] [DecidableEq Slot]
    (state : CommitmentCandidates Principal Slot Value)
    (owner : Principal) (slot : Slot) (value : Value)
    (handle : CommitmentHandle Principal Slot) (hne : handle ≠ (owner, slot)) :
    (state.prepare owner slot value).lookup handle = state.lookup handle := by
  rcases handle with ⟨otherOwner, otherSlot⟩
  have hother : ¬(otherOwner = owner ∧ otherSlot = slot) := by
    rintro ⟨rfl, rfl⟩
    exact hne rfl
  cases hlookup : state.table owner slot <;>
    simp [prepare, lookup, hlookup, hother]

@[simp] theorem lookup_freeze_self [DecidableEq Principal] [DecidableEq Slot]
    (state : CommitmentCandidates Principal Slot Value)
    (handle : CommitmentHandle Principal Slot) :
    (state.freeze handle).lookup handle =
      match state.lookup handle with
      | .fresh => .unopenable
      | .openable value => .openable value
      | .unopenable => .unopenable := by
  cases handle with
  | mk owner slot =>
      cases hlookup : state.table owner slot <;>
        simp [freeze, lookup, hlookup]

theorem lookup_freeze_other [DecidableEq Principal] [DecidableEq Slot]
    (state : CommitmentCandidates Principal Slot Value)
    (accepted queried : CommitmentHandle Principal Slot) (hne : queried ≠ accepted) :
    (state.freeze accepted).lookup queried = state.lookup queried := by
  rcases accepted with ⟨acceptedOwner, acceptedSlot⟩
  rcases queried with ⟨queriedOwner, queriedSlot⟩
  have hother : ¬(queriedOwner = acceptedOwner ∧ queriedSlot = acceptedSlot) := by
    rintro ⟨rfl, rfl⟩
    exact hne rfl
  cases hlookup : state.table acceptedOwner acceptedSlot <;>
    simp [freeze, lookup, hlookup, hother]

theorem verify_eq_true_iff [DecidableEq Value]
    (state : CommitmentCandidates Principal Slot Value)
    (handle : CommitmentHandle Principal Slot) (claimed : Value) :
    state.verify handle claimed = true ↔ state.lookup handle = .openable claimed := by
  simp [verify]

/-- Preparing any candidate cannot change an already fixed handle. -/
theorem lookup_prepare_eq_of_not_fresh [DecidableEq Principal] [DecidableEq Slot]
    (state : CommitmentCandidates Principal Slot Value)
    (handle : CommitmentHandle Principal Slot) (owner : Principal) (slot : Slot) (value : Value)
    (hfixed : state.lookup handle ≠ .fresh) :
    (state.prepare owner slot value).lookup handle = state.lookup handle := by
  by_cases heq : handle = (owner, slot)
  · subst handle
    cases hlookup : state.lookup (owner, slot) with
    | fresh => exact (hfixed hlookup).elim
    | openable stored => simp [lookup_prepare_self, hlookup]
    | unopenable => simp [lookup_prepare_self, hlookup]
  · exact state.lookup_prepare_other owner slot value handle heq

/-- Freezing any candidate cannot change an already fixed handle. -/
theorem lookup_freeze_eq_of_not_fresh [DecidableEq Principal] [DecidableEq Slot]
    (state : CommitmentCandidates Principal Slot Value)
    (handle accepted : CommitmentHandle Principal Slot)
    (hfixed : state.lookup handle ≠ .fresh) :
    (state.freeze accepted).lookup handle = state.lookup handle := by
  by_cases heq : handle = accepted
  · subst handle
    cases hlookup : state.lookup accepted with
    | fresh => exact (hfixed hlookup).elim
    | openable value => simp [lookup_freeze_self, hlookup]
    | unopenable => simp [lookup_freeze_self, hlookup]
  · exact state.lookup_freeze_other accepted handle heq

/-- Freezing always leaves its canonical handle with a fixed meaning. -/
theorem lookup_freeze_ne_fresh [DecidableEq Principal] [DecidableEq Slot]
    (state : CommitmentCandidates Principal Slot Value)
    (handle : CommitmentHandle Principal Slot) :
    (state.freeze handle).lookup handle ≠ .fresh := by
  cases hlookup : state.lookup handle <;>
    simp [lookup_freeze_self, hlookup]

@[simp] theorem freeze_idempotent [DecidableEq Principal] [DecidableEq Slot]
    (state : CommitmentCandidates Principal Slot Value)
    (handle : CommitmentHandle Principal Slot) :
    (state.freeze handle).freeze handle = state.freeze handle :=
  (state.freeze handle).freeze_eq_self_of_not_fresh handle (state.lookup_freeze_ne_fresh handle)

/-- Freezing any handle preserves every verification result, including when
the frozen handle was fresh and therefore had no opening. -/
theorem verify_freeze [DecidableEq Principal] [DecidableEq Slot] [DecidableEq Value]
    (state : CommitmentCandidates Principal Slot Value)
    (accepted queried : CommitmentHandle Principal Slot) (claimed : Value) :
    (state.freeze accepted).verify queried claimed = state.verify queried claimed := by
  unfold verify
  by_cases heq : queried = accepted
  · subst queried
    cases hlookup : state.lookup accepted <;>
      simp [lookup_freeze_self, hlookup]
  · rw [state.lookup_freeze_other accepted queried heq]

/-- An openable value after preparation was either already present or was
supplied by this exact owner/slot preparation. -/
theorem lookup_prepare_openable_origin [DecidableEq Principal] [DecidableEq Slot]
    (state : CommitmentCandidates Principal Slot Value)
    (owner : Principal) (slot : Slot) (submitted : Value)
    (handle : CommitmentHandle Principal Slot) (value : Value)
    (hlookup : (state.prepare owner slot submitted).lookup handle = .openable value) :
    state.lookup handle = .openable value ∨ handle = (owner, slot) ∧ submitted = value := by
  by_cases heq : handle = (owner, slot)
  · subst handle
    rw [lookup_prepare_self] at hlookup
    cases hprior : state.lookup (owner, slot) with
    | fresh =>
        simp only [hprior, CommitmentCandidate.openable.injEq] at hlookup
        exact Or.inr ⟨rfl, hlookup⟩
    | openable prior =>
        simp only [hprior, CommitmentCandidate.openable.injEq] at hlookup
        exact Or.inl (congrArg CommitmentCandidate.openable hlookup)
    | unopenable => simp only [hprior] at hlookup; contradiction
  · exact Or.inl ((state.lookup_prepare_other owner slot submitted handle heq).symm.trans hlookup)

/-- Acceptance creates no opening, including when it makes a fresh candidate
permanently unopenable. -/
theorem lookup_freeze_openable_iff [DecidableEq Principal] [DecidableEq Slot]
    (state : CommitmentCandidates Principal Slot Value)
    (accepted queried : CommitmentHandle Principal Slot) (value : Value) :
    (state.freeze accepted).lookup queried = .openable value ↔
      state.lookup queried = .openable value := by
  by_cases heq : queried = accepted
  · subst queried
    rw [lookup_freeze_self]
    cases state.lookup accepted <;> simp
  · rw [state.lookup_freeze_other accepted queried heq]

/-- Preparing a fresh handle and then accepting it retains its opening. -/
theorem lookup_freeze_prepare [DecidableEq Principal] [DecidableEq Slot]
    (state : CommitmentCandidates Principal Slot Value)
    (owner : Principal) (slot : Slot) (value : Value)
    (hfresh : state.lookup (owner, slot) = .fresh) :
    ((state.prepare owner slot value).freeze (owner, slot)).lookup (owner, slot) =
      .openable value := by
  rw [lookup_freeze_self, lookup_prepare_self, hfresh]

/-- Two distinct fresh handles can be prepared independently. -/
theorem lookup_prepare_distinct [DecidableEq Principal] [DecidableEq Slot]
    (state : CommitmentCandidates Principal Slot Value)
    (first second : CommitmentHandle Principal Slot) (firstValue secondValue : Value)
    (hne : first ≠ second) (hfirst : state.lookup first = .fresh)
    (hsecond : state.lookup second = .fresh) :
    let prepared := (state.prepare first.1 first.2 firstValue).prepare
      second.1 second.2 secondValue
    prepared.lookup first = .openable firstValue ∧
      prepared.lookup second = .openable secondValue := by
  rcases first with ⟨firstOwner, firstSlot⟩
  rcases second with ⟨secondOwner, secondSlot⟩
  have hfirstPrepared : (state.prepare firstOwner firstSlot firstValue).lookup
      (firstOwner, firstSlot) = .openable firstValue := by
    simp [lookup_prepare_self, hfirst]
  have hsecondFresh : (state.prepare firstOwner firstSlot firstValue).lookup
      (secondOwner, secondSlot) = .fresh := by
    rw [state.lookup_prepare_other firstOwner firstSlot firstValue
      (secondOwner, secondSlot) hne.symm, hsecond]
  constructor
  · exact (state.prepare firstOwner firstSlot firstValue).lookup_prepare_eq_of_not_fresh
      (firstOwner, firstSlot) secondOwner secondSlot secondValue
      (by rw [hfirstPrepared]; simp) |>.trans hfirstPrepared
  · simp [lookup_prepare_self, hsecondFresh]

/-- Once a fresh handle is accepted as unopenable, no later preparation can
revive it, even when preparing that same owner and slot. -/
theorem lookup_prepare_freeze_of_fresh [DecidableEq Principal] [DecidableEq Slot]
    (state : CommitmentCandidates Principal Slot Value)
    (handle : CommitmentHandle Principal Slot) (owner : Principal) (slot : Slot) (value : Value)
    (hfresh : state.lookup handle = .fresh) :
    ((state.freeze handle).prepare owner slot value).lookup handle = .unopenable := by
  have haccepted : (state.freeze handle).lookup handle = .unopenable := by
    simp [lookup_freeze_self, hfresh]
  rw [(state.freeze handle).lookup_prepare_eq_of_not_fresh handle owner slot value
    (by rw [haccepted]; simp), haccepted]

end CommitmentCandidates

namespace IdealCommitments

variable {Principal : Type uPrincipal} {Slot : Type uSlot} {Value : Type uValue}

/-- Embed a preparation table into the candidate catalog. Unoccupied handles
are fresh, not accepted as unopenable. -/
def candidates (state : IdealCommitments Principal Slot Value) :
    CommitmentCandidates Principal Slot Value where
  table owner slot := (state.table owner slot).elim .fresh .openable

@[simp] theorem candidates_lookup (state : IdealCommitments Principal Slot Value)
    (handle : CommitmentHandle Principal Slot) :
    state.candidates.lookup handle = (state.lookup handle).elim .fresh .openable := rfl

/-- Preparing the same owner-scoped handle commutes with the embedding,
including repeated preparations. -/
theorem candidates_sealValue [DecidableEq Principal] [DecidableEq Slot]
    (state : IdealCommitments Principal Slot Value)
    (owner : Principal) (slot : Slot) (value : Value) :
    (state.sealValue owner slot value).state.candidates =
      state.candidates.prepare owner slot value := by
  cases hlookup : state.table owner slot with
  | some stored => simp [sealValue, CommitmentCandidates.prepare, hlookup, candidates,
      CommitmentCandidates.lookup]
  | none =>
      simp only [sealValue, hlookup, CommitmentCandidates.prepare, candidates_lookup,
        lookup, Option.elim_none]
      unfold candidates
      congr 1
      funext otherOwner otherSlot
      by_cases hsame : otherOwner = owner ∧ otherSlot = slot <;> simp [hsame]

/-- A prepared candidate needs no further catalog update at acceptance. -/
theorem candidates_freeze [DecidableEq Principal] [DecidableEq Slot]
    (state : IdealCommitments Principal Slot Value)
    (handle : CommitmentHandle Principal Slot) (hprepared : (state.lookup handle).isSome) :
    state.candidates.freeze handle = state.candidates := by
  cases hlookup : state.lookup handle with
  | none => simp [hlookup] at hprepared
  | some value => simp [CommitmentCandidates.freeze, hlookup]

@[simp] theorem candidates_verify [DecidableEq Value]
    (state : IdealCommitments Principal Slot Value)
    (handle : CommitmentHandle Principal Slot) (claimed : Value) :
    state.candidates.verify handle claimed = state.verify ⟨handle, claimed⟩ := by
  apply Bool.eq_iff_iff.mpr
  cases hlookup : state.lookup handle <;>
    simp [CommitmentCandidates.verify, IdealCommitments.verify, hlookup]

end IdealCommitments

end Interaction
