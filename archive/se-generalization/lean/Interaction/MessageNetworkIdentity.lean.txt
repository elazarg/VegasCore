/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageNetworkCounters
import Interaction.MessagePublication

/-! # An envelope identifier fixes the entire message

Fresh submission allocates a new identifier. Observation and inclusion copy
existing envelopes, so they cannot introduce different payloads under one
identifier. Inclusion moves its envelope from the pending pool to the ledger,
so no identifier is pending twice, published twice, or both pending and
published.
-/

namespace Interaction.MessageNetwork

variable {Principal Payload : Type}

def UniqueIds (network : MessageNetwork Principal Payload) : Prop :=
  network.Satisfies fun message => network.Satisfies fun other =>
    other.id = message.id → other = message

variable {network : MessageNetwork Principal Payload}

theorem UniqueIds.empty : (MessageNetwork.empty : MessageNetwork Principal Payload).UniqueIds :=
  Satisfies.empty

variable [DecidableEq Principal]

theorem UniqueIds.learn (valid : network.UniqueIds) (who : Principal)
    (selected : Finset (MessageId Principal)) : (network.learn who selected).UniqueIds :=
  (valid.mono fun _ matching => matching.learn who selected).learn who selected

theorem UniqueIds.includePending (valid : network.UniqueIds) (id : MessageId Principal) :
    (network.includePending id).2.UniqueIds :=
  (valid.mono fun _ matching => matching.includePending id).includePending id

theorem UniqueIds.submit (valid : network.UniqueIds) (serials : network.SerialsBeforeNext)
    (who : Principal) (payload : Payload) : (network.submit who payload).2.UniqueIds := by
  let issued : Message Principal Payload := ⟨(who, network.nextSerial who), payload⟩
  have fresh : network.Satisfies fun message => message.id ≠ issued.id := by
    apply serials.mono
    intro message earlier same
    change message.id.2 < network.nextSerial message.id.1 at earlier
    rw [same] at earlier
    exact Nat.lt_irrefl _ earlier
  have old : network.Satisfies fun message => (network.submit who payload).2.Satisfies
      fun other => other.id = message.id → other = message :=
    (valid.and fresh).mono fun _ pair => pair.1.submit who payload
      (fun same => False.elim (pair.2 same.symm))
  apply old.submit who payload
  apply (fresh.mono fun _ different same => False.elim (different same)).submit who payload
  exact fun _ => rfl

/-- When a known identifier is already public, the very same envelope is in
the ledger. Equality of identifiers cannot conceal a different certificate. -/
theorem UniqueIds.known_published (valid : network.UniqueIds) (who : Principal)
    (message : Message Principal Payload) (known : message ∈ network.known who)
    (published : message.id ∈ network.ledger.map Message.id) : message ∈ network.ledger := by
  obtain ⟨record, present, same⟩ := List.mem_map.mp published
  have equal := (valid.known who message known).ledger record present same
  exact equal ▸ present

/-- Pending and published identifiers are pairwise distinct. -/
def IdsDistinct (network : MessageNetwork Principal Payload) : Prop :=
  ((network.pending ++ network.ledger).map Message.id).Nodup

omit [DecidableEq Principal] in
theorem IdsDistinct.empty :
    (MessageNetwork.empty : MessageNetwork Principal Payload).IdsDistinct := by
  simp [IdsDistinct, MessageNetwork.empty]

omit [DecidableEq Principal] in
theorem IdsDistinct.publishedOnce (valid : network.IdsDistinct) : network.PublishedOnce := by
  unfold IdsDistinct at valid
  rw [List.map_append] at valid
  exact (List.nodup_append.mp valid).2.1

theorem IdsDistinct.submit (valid : network.IdsDistinct) (serials : network.SerialsBeforeNext)
    (who : Principal) (payload : Payload) : (network.submit who payload).2.IdsDistinct := by
  have fresh : (who, network.nextSerial who) ∉
      (network.pending ++ network.ledger).map Message.id := by
    intro member
    obtain ⟨message, retained, same⟩ := List.mem_map.mp member
    have earlier : message.id.2 < network.nextSerial message.id.1 := by
      rcases List.mem_append.mp retained with pending | ledger
      · exact serials.pending message pending
      · exact serials.ledger message ledger
    rw [same] at earlier
    exact Nat.lt_irrefl _ earlier
  let issued : Message Principal Payload := ⟨(who, network.nextSerial who), payload⟩
  have moved : List.Perm ((network.pending ++ [issued] ++ network.ledger).map Message.id)
      ((who, network.nextSerial who) :: (network.pending ++ network.ledger).map Message.id) := by
    simp only [List.map_append, List.append_assoc, List.singleton_append]
    exact List.perm_middle
  change ((network.pending ++ [issued] ++ network.ledger).map Message.id).Nodup
  exact moved.nodup_iff.mpr (List.nodup_cons.mpr ⟨fresh, valid⟩)

theorem IdsDistinct.learn (valid : network.IdsDistinct) (who : Principal)
    (selected : Finset (MessageId Principal)) : (network.learn who selected).IdsDistinct :=
  valid

private theorem perm_removeFirst (id : MessageId Principal)
    (messages : List (Message Principal Payload)) (selected : Message Principal Payload)
    (found : messages.find? (fun message => message.id = id) = some selected) :
    List.Perm messages (selected :: MessagePool.removeFirst id messages) := by
  induction messages with
  | nil => simp at found
  | cons first rest ih =>
      by_cases head : first.id = id
      · have same : first = selected := by simpa [List.find?, head] using found
        subst same
        simp [MessagePool.removeFirst, head]
      · have later : rest.find? (fun message => message.id = id) = some selected := by
          simpa [List.find?, head] using found
        simp only [MessagePool.removeFirst, head, ↓reduceIte]
        exact ((ih later).cons first).trans (List.Perm.swap selected first _)

theorem IdsDistinct.includePending (valid : network.IdsDistinct) (id : MessageId Principal) :
    (network.includePending id).2.IdsDistinct := by
  cases found : network.lookup id with
  | none => simpa only [MessageNetwork.includePending, found] using valid
  | some selected =>
      have front : List.Perm
          (MessagePool.removeFirst id network.pending ++ (network.ledger ++ [selected]))
          (selected :: (MessagePool.removeFirst id network.pending ++ network.ledger)) := by
        rw [← List.append_assoc]
        exact List.perm_append_singleton _ _
      have moved : List.Perm
          (MessagePool.removeFirst id network.pending ++ (network.ledger ++ [selected]))
          (network.pending ++ network.ledger) :=
        front.trans ((perm_removeFirst id network.pending selected found).append_right _).symm
      unfold IdsDistinct
      simp only [MessageNetwork.includePending, found]
      exact (moved.map Message.id).nodup_iff.mpr valid

end Interaction.MessageNetwork
