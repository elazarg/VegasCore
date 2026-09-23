/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageNetwork
import Interaction.MessageInvariant

/-! # Predicates on all envelopes retained by the network -/

namespace Interaction.MessageNetwork

variable {Principal Payload : Type}

structure Satisfies (safe : Message Principal Payload → Prop)
    (network : MessageNetwork Principal Payload) : Prop where
  pending : ∀ message ∈ network.pending, safe message
  ledger : ∀ message ∈ network.ledger, safe message
  leaked : ∀ who message, message ∈ network.leaked who → safe message
  inputs : ∀ input ∈ network.inputs, safe input.envelope

variable {safe weaker : Message Principal Payload → Prop}
  {network : MessageNetwork Principal Payload}

theorem Satisfies.empty : Satisfies safe (.empty : MessageNetwork Principal Payload) :=
  ⟨by simp [MessageNetwork.empty], by simp [MessageNetwork.empty],
    by simp [MessageNetwork.empty], by simp [MessageNetwork.empty]⟩

theorem Satisfies.mono (valid : network.Satisfies safe)
    (implies : ∀ message, safe message → weaker message) : network.Satisfies weaker :=
  ⟨fun message member => implies message (valid.pending message member),
    fun message member => implies message (valid.ledger message member),
    fun who message member => implies message (valid.leaked who message member),
    fun input member => implies input.envelope (valid.inputs input member)⟩

variable [DecidableEq Principal]

theorem Satisfies.lookup (valid : network.Satisfies safe)
    (id : MessageId Principal) (message : Message Principal Payload)
    (found : network.lookup id = some message) : safe message :=
  valid.pending message (List.mem_of_find?_eq_some found)

theorem Satisfies.known (valid : network.Satisfies safe) (who : Principal)
    (message : Message Principal Payload) (member : message ∈ network.known who) :
    safe message := by
  simp only [MessageNetwork.known, List.mem_append] at member
  rcases member with (fromInputs | received) | included
  · obtain ⟨record, retained, selected⟩ := List.mem_filterMap.mp fromInputs
    split at selected
    · exact Option.some.inj selected ▸ valid.inputs record retained
    · cases selected
  · exact valid.leaked who message received
  · exact valid.ledger message included

theorem Satisfies.submit (valid : network.Satisfies safe) (who : Principal) (payload : Payload)
    (issued : safe ⟨(who, network.nextSerial who), payload⟩) :
    (network.submit who payload).2.Satisfies safe := by
  refine ⟨?_, valid.ledger, valid.leaked, ?_⟩
  · intro message member
    rcases List.mem_append.mp member with prior | fresh
    · exact valid.pending message prior
    · cases List.mem_singleton.mp fresh
      exact issued
  · intro input member
    rcases List.mem_append.mp member with prior | fresh
    · exact valid.inputs input prior
    · cases List.mem_singleton.mp fresh
      exact issued

theorem Satisfies.replay (valid : network.Satisfies safe) (who : Principal)
    (id : MessageId Principal) : (network.replay who id).2.Satisfies safe := by
  unfold MessageNetwork.replay
  split
  · exact valid
  · rename_i message found
    have safeMessage := valid.known who message (List.mem_of_find?_eq_some found)
    refine ⟨?_, valid.ledger, valid.leaked, ?_⟩
    · intro candidate member
      rcases List.mem_append.mp member with prior | replayed
      · exact valid.pending candidate prior
      · cases List.mem_singleton.mp replayed
        exact safeMessage
    · intro input member
      rcases List.mem_append.mp member with prior | replayed
      · exact valid.inputs input prior
      · cases List.mem_singleton.mp replayed
        exact safeMessage

theorem Satisfies.learn (valid : network.Satisfies safe) (who : Principal)
    (selected : Finset (MessageId Principal)) : (network.learn who selected).Satisfies safe := by
  refine ⟨valid.pending, valid.ledger, ?_, valid.inputs⟩
  intro observer candidate member
  by_cases same : observer = who
  · subst observer
    rcases network.learn_mem who selected candidate member with prior | fresh
    · exact valid.leaked who candidate prior
    · exact valid.pending candidate fresh.1
  · rw [network.learn_other who observer selected same] at member
    exact valid.leaked observer candidate member

theorem Satisfies.includePending (valid : network.Satisfies safe) (id : MessageId Principal) :
    (network.includePending id).2.Satisfies safe := by
  unfold MessageNetwork.includePending
  split
  · exact valid
  · rename_i message found
    refine ⟨?_, ?_, valid.leaked, valid.inputs⟩
    · intro candidate member
      exact valid.pending candidate (MessagePool.mem_of_mem_removeFirst id candidate _ member)
    · intro candidate member
      rcases List.mem_append.mp member with prior | included
      · exact valid.ledger candidate prior
      · cases List.mem_singleton.mp included
        exact valid.lookup id message found

end Interaction.MessageNetwork
