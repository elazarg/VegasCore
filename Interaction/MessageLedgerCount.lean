/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageNetwork

/-! # Processed identifiers per author

The modeled network never includes an identifier twice, but a deployed chain
may deliver duplicate transactions, and inclusion here does not itself check
whether an identifier was already included. A contract processes each
identifier once, so the number of an author's calls it has processed is the
number of distinct identifiers of that author on the ledger, whether each call
was accepted or rejected. An implementation keeps this number as the author's
nonce. When the ledger holds no repeated identifier it is the plain count of
the author's ledger entries (`Interaction.Message.distinctAuthoredCount_eq_countP`).
-/

namespace Interaction.Message

variable {Principal Payload : Type} [DecidableEq Principal]

/-- The number of distinct identifiers authored by `who` on `ledger`. -/
def distinctAuthoredCount (ledger : List (Message Principal Payload)) (who : Principal) : Nat :=
  ((ledger.map Message.id).toFinset.filter fun id => id.1 = who).card

@[simp] theorem distinctAuthoredCount_nil (who : Principal) :
    distinctAuthoredCount ([] : List (Message Principal Payload)) who = 0 := rfl

/-- A copy of an identifier already on the ledger is not counted again. -/
theorem distinctAuthoredCount_cons_of_mem (ledger : List (Message Principal Payload))
    (message : Message Principal Payload) (who : Principal)
    (published : message.id ∈ ledger.map Message.id) :
    distinctAuthoredCount (message :: ledger) who = distinctAuthoredCount ledger who := by
  unfold distinctAuthoredCount
  rw [List.map_cons, List.toFinset_cons, Finset.insert_eq_of_mem (List.mem_toFinset.mpr published)]

/-- A new identifier counts once for its author and not for anyone else. -/
theorem distinctAuthoredCount_cons_of_not_mem (ledger : List (Message Principal Payload))
    (message : Message Principal Payload) (who : Principal)
    (fresh : message.id ∉ ledger.map Message.id) :
    distinctAuthoredCount (message :: ledger) who =
      distinctAuthoredCount ledger who + if message.sender = who then 1 else 0 := by
  unfold distinctAuthoredCount
  rw [List.map_cons, List.toFinset_cons, Finset.filter_insert]
  have absent : message.id ∉ (ledger.map Message.id).toFinset.filter fun id => id.1 = who :=
    fun member => fresh (List.mem_toFinset.mp (Finset.mem_filter.mp member).1)
  by_cases same : message.sender = who
  · have authored : message.id.1 = who := same
    simp only [authored, ↓reduceIte, same]
    exact Finset.card_insert_of_notMem absent
  · have authored : ¬ message.id.1 = who := same
    simp only [authored, ↓reduceIte, same, Nat.add_zero]

theorem distinctAuthoredCount_append (first second : List (Message Principal Payload))
    (who : Principal) :
    distinctAuthoredCount (first ++ second) who =
      ((((first.map Message.id).toFinset ∪ (second.map Message.id).toFinset).filter
        fun id => id.1 = who).card) := by
  unfold distinctAuthoredCount
  rw [List.map_append, List.toFinset_append]

/-- Appending a copy of an identifier already on the ledger leaves every count
unchanged. -/
theorem distinctAuthoredCount_append_of_mem (ledger : List (Message Principal Payload))
    (message : Message Principal Payload) (who : Principal)
    (published : message.id ∈ ledger.map Message.id) :
    distinctAuthoredCount (ledger ++ [message]) who = distinctAuthoredCount ledger who := by
  rw [distinctAuthoredCount_append]
  unfold distinctAuthoredCount
  congr 2
  apply Finset.union_eq_left.mpr
  intro id member
  simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
    insert_empty_eq, Finset.mem_singleton] at member
  subst member
  exact List.mem_toFinset.mpr published

/-- Appending a new identifier counts once for its author. -/
theorem distinctAuthoredCount_append_of_not_mem (ledger : List (Message Principal Payload))
    (message : Message Principal Payload) (who : Principal)
    (fresh : message.id ∉ ledger.map Message.id) :
    distinctAuthoredCount (ledger ++ [message]) who =
      distinctAuthoredCount ledger who + if message.sender = who then 1 else 0 := by
  rw [← distinctAuthoredCount_cons_of_not_mem ledger message who fresh,
    distinctAuthoredCount_append]
  unfold distinctAuthoredCount
  rw [List.map_cons, List.toFinset_cons, Finset.union_comm]
  simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil, insert_empty_eq]
  rw [Finset.singleton_union]

/-- Appending a new identifier of `who` advances `who`'s count by one. -/
theorem distinctAuthoredCount_append_self (ledger : List (Message Principal Payload))
    (message : Message Principal Payload)
    (fresh : message.id ∉ ledger.map Message.id) :
    distinctAuthoredCount (ledger ++ [message]) message.sender =
      distinctAuthoredCount ledger message.sender + 1 := by
  rw [distinctAuthoredCount_append_of_not_mem ledger message _ fresh]
  simp only [↓reduceIte]

/-- Another author's envelope never changes `who`'s count, whether or not it
is a copy. -/
theorem distinctAuthoredCount_append_other (ledger : List (Message Principal Payload))
    (message : Message Principal Payload) (who : Principal) (other : message.sender ≠ who) :
    distinctAuthoredCount (ledger ++ [message]) who = distinctAuthoredCount ledger who := by
  by_cases published : message.id ∈ ledger.map Message.id
  · exact distinctAuthoredCount_append_of_mem ledger message who published
  · rw [distinctAuthoredCount_append_of_not_mem ledger message who published]
    simp only [other, ↓reduceIte, Nat.add_zero]

/-- Without repeated identifiers, the distinct count is the plain count of the
author's ledger entries. -/
theorem distinctAuthoredCount_eq_countP (ledger : List (Message Principal Payload))
    (who : Principal) (nodup : (ledger.map Message.id).Nodup) :
    distinctAuthoredCount ledger who = ledger.countP (fun message => message.sender = who) := by
  induction ledger with
  | nil => rfl
  | cons message rest ih =>
      rw [List.map_cons, List.nodup_cons] at nodup
      rw [distinctAuthoredCount_cons_of_not_mem rest message who nodup.1, ih nodup.2,
        List.countP_cons]
      simp only [decide_eq_true_eq]

/-- Copies only inflate the plain count. -/
theorem distinctAuthoredCount_le_countP (ledger : List (Message Principal Payload))
    (who : Principal) :
    distinctAuthoredCount ledger who ≤ ledger.countP (fun message => message.sender = who) := by
  induction ledger with
  | nil => exact Nat.le_refl 0
  | cons message rest ih =>
      rw [List.countP_cons]
      by_cases published : message.id ∈ rest.map Message.id
      · rw [distinctAuthoredCount_cons_of_mem rest message who published]
        omega
      · rw [distinctAuthoredCount_cons_of_not_mem rest message who published]
        simp only [decide_eq_true_eq]
        split <;> omega

/-- When `who`'s identifiers on the ledger are exactly its serials below
`count`, the distinct count is `count`, however many copies are included. -/
theorem distinctAuthoredCount_eq_of_serials (ledger : List (Message Principal Payload))
    (who : Principal) (count : Nat)
    (below : ∀ message ∈ ledger, message.sender = who → message.id.2 < count)
    (present : ∀ serial < count, (who, serial) ∈ ledger.map Message.id) :
    distinctAuthoredCount ledger who = count := by
  unfold distinctAuthoredCount
  have same : ((ledger.map Message.id).toFinset.filter fun id => id.1 = who) =
      (Finset.range count).image (fun serial => (who, serial)) := by
    ext ⟨author, serial⟩
    simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_image, Finset.mem_range,
      Prod.mk.injEq]
    constructor
    · rintro ⟨member, rfl⟩
      obtain ⟨message, inside, identified⟩ := List.mem_map.mp member
      have bound := below message inside (congrArg Prod.fst identified)
      rw [identified] at bound
      exact ⟨serial, bound, rfl, rfl⟩
    · rintro ⟨index, lower, rfl, rfl⟩
      exact ⟨present index lower, rfl⟩
  rw [same, Finset.card_image_of_injective _ (fun first second equal => congrArg Prod.snd equal),
    Finset.card_range]

end Interaction.Message
