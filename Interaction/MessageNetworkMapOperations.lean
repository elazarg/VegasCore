/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.MessageNetworkMap

/-! # Payload maps commute with physical message lookup and inclusion -/

namespace Interaction

variable {Principal A B : Type} [DecidableEq Principal]

theorem MessagePool.removeFirst_mapPayload (f : A → B) (identity : MessageId Principal)
    (messages : List (Message Principal A)) :
    removeFirst identity (messages.map (Message.mapPayload f)) =
      (removeFirst identity messages).map (Message.mapPayload f) := by
  induction messages with
  | nil => rfl
  | cons message rest ih =>
      simp only [List.map_cons, removeFirst, Message.mapPayload]
      split <;> simp only [List.map_cons, ih, Message.mapPayload]

namespace MessageNetwork

theorem mapPayload_lookup (f : A → B) (network : MessageNetwork Principal A)
    (identity : MessageId Principal) :
    (network.mapPayload f).lookup identity =
      (network.lookup identity).map (Message.mapPayload f) := by
  change (network.pending.map (Message.mapPayload f)).find? _ =
    (network.pending.find? (fun packet => packet.id = identity)).map (Message.mapPayload f)
  induction network.pending with
  | nil => rfl
  | cons message rest ih =>
      simp only [List.map_cons, List.find?_cons, Message.mapPayload]
      split <;> simp_all only [Option.map_some, Message.mapPayload]

theorem mapPayload_includePending (f : A → B) (network : MessageNetwork Principal A)
    (identity : MessageId Principal) :
    (network.mapPayload f).includePending identity =
      ((network.includePending identity).1.map (Message.mapPayload f),
        (network.includePending identity).2.mapPayload f) := by
  unfold includePending
  rw [mapPayload_lookup]
  cases network.lookup identity with
  | none => rfl
  | some message =>
      simp only [Option.map_some, mapPayload, List.map_append, List.map_singleton,
        MessagePool.removeFirst_mapPayload]

end MessageNetwork
end Interaction
