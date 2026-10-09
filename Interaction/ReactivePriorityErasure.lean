/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveErasure
import Interaction.ReactivePublication

/-! # Priority selection under envelope erasure

Deleting an identifier and renaming later identifiers preserves membership of
every retained identifier. A priority selector whose eligibility predicate
agrees on retained envelopes therefore returns the same identifier whenever
its original selection was retained. Neither unique identifiers nor reachable
network inputs are required.
-/

namespace Interaction

variable {Principal : Type} [DecidableEq Principal]

namespace MessageId

/-- Erasure preserves the authenticated author of every identifier. -/
theorem erase_author (removed id : MessageId Principal) :
    (erase removed id).1 = id.1 := by
  unfold erase
  split <;> rfl

end MessageId

namespace Message

variable {Payload : Type}

/-- A retained identifier occurs in the erased list exactly when its original
identifier occurred in the original list. -/
theorem eraseList_id_mem (removed id : MessageId Principal)
    (kept : id ≠ removed) (messages : List (Message Principal Payload)) :
    MessageId.erase removed id ∈ (eraseList removed messages).map Message.id ↔
      id ∈ messages.map Message.id := by
  constructor
  · intro present
    obtain ⟨message, present, named⟩ := List.mem_map.mp present
    change message ∈ (messages.filter fun original => original.id ≠ removed).map
      (fun original => ⟨MessageId.erase removed original.id, original.payload⟩) at present
    obtain ⟨original, retainedMember, renamed⟩ := List.mem_map.mp present
    have retained : original.id ≠ removed := by
      simpa only [decide_eq_true_eq] using (List.mem_filter.mp retainedMember).2
    have eraseEq : MessageId.erase removed original.id = MessageId.erase removed id :=
      (congrArg Message.id renamed).trans named
    have same := congrArg (MessageId.restore removed) eraseEq
    change MessageId.restore removed (MessageId.erase removed original.id) =
      MessageId.restore removed (MessageId.erase removed id) at same
    rw [MessageId.restore_erase removed original.id retained,
      MessageId.restore_erase removed id kept] at same
    exact List.mem_map.mpr ⟨original, (List.mem_filter.mp retainedMember).1, same⟩
  · intro present
    obtain ⟨original, present, named⟩ := List.mem_map.mp present
    have retained : original.id ≠ removed := named ▸ kept
    apply List.mem_map.mpr
    refine ⟨⟨MessageId.erase removed original.id, original.payload⟩, ?_,
      congrArg (MessageId.erase removed) named⟩
    change (⟨MessageId.erase removed original.id, original.payload⟩ : Message Principal Payload) ∈
      (messages.filter fun original => original.id ≠ removed).map
        (fun original : Message Principal Payload =>
          (⟨MessageId.erase removed original.id, original.payload⟩ : Message Principal Payload))
    apply List.mem_map.mpr
    refine ⟨original, List.mem_filter.mpr ⟨present, ?_⟩, rfl⟩
    exact decide_eq_true retained

/-- Erasing identifiers commutes with reversing priority order. -/
theorem eraseList_reverse (removed : MessageId Principal)
    (messages : List (Message Principal Payload)) :
    eraseList removed messages.reverse = (eraseList removed messages).reverse := by
  simp only [eraseList, List.filter_reverse, List.map_reverse]

/-- A priority selector returns the same retained identifier after erasure,
provided its eligibility predicate agrees on every retained envelope. -/
theorem find_eraseList_restore
    (removed : MessageId Principal) (before after : Message Principal Payload → Bool)
    (same : ∀ message, message.id ≠ removed →
      after ⟨MessageId.erase removed message.id, message.payload⟩ = before message)
    (messages : List (Message Principal Payload))
    (notChosen : (messages.find? before).map Message.id ≠ some removed) :
    ((eraseList removed messages).find? after).map
        (fun message => MessageId.restore removed message.id) =
      (messages.find? before).map Message.id := by
  induction messages with
  | nil => rfl
  | cons head tail ih =>
      by_cases removedHead : head.id = removed
      · by_cases chosen : before head = true
        · simp only [List.find?_cons, chosen, Option.map_some, removedHead] at notChosen
          exact (notChosen rfl).elim
        · have rejected : before head = false := Bool.eq_false_iff.mpr chosen
          have notTail : (tail.find? before).map Message.id ≠ some removed := by
            simpa only [List.find?_cons, rejected] using notChosen
          simpa only [eraseList, List.filter_cons, removedHead, ne_eq,
            not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
            List.find?_cons, rejected] using ih notTail
      · have retained : head.id ≠ removed := removedHead
        have predicate := same head retained
        have filter : decide (head.id ≠ removed) = true := decide_eq_true retained
        cases chosen : before head with
        | false =>
            have notTail : (tail.find? before).map Message.id ≠ some removed := by
              simpa only [List.find?_cons, chosen] using notChosen
            simpa only [eraseList, List.filter_cons, filter, ↓reduceIte,
              List.map_cons, List.find?_cons, predicate, chosen] using ih notTail
        | true =>
            simp only [eraseList, List.filter_cons, filter, ↓reduceIte,
              List.map_cons, List.find?_cons, predicate, chosen, Option.map_some]
            exact congrArg some (MessageId.restore_erase removed head.id retained)

end Message

namespace ReactiveApplication

variable (app : ReactiveApplication Principal)

/-- Erasing another identifier preserves whether a retained envelope has
already been published. -/
theorem EnvironmentView.unpublished_erase (view : app.EnvironmentView)
    (removed id : MessageId Principal) (kept : id ≠ removed) :
    (view.erase app removed).Unpublished app (MessageId.erase removed id) ↔
      view.Unpublished app id := by
  change (MessageId.erase removed id ∉ (Message.eraseList removed view.network.ledger).map
    Message.id) ↔ (id ∉ view.network.ledger.map Message.id)
  exact not_congr (Message.eraseList_id_mem removed id kept view.network.ledger)

end ReactiveApplication

end Interaction
