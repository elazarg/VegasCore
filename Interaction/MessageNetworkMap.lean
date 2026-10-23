/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.MessageNetwork

/-! # Payload maps preserve the physical message network -/

namespace Interaction

variable {Principal A B C : Type}

/-- Change only the payload; the permanent physical identifier is retained. -/
def Message.mapPayload (f : A → B) (message : Message Principal A) : Message Principal B :=
  ⟨message.id, f message.payload⟩

namespace MessageNetwork

/-- The same physical network with every stored payload mapped uniformly. -/
def mapPayload (f : A → B) (network : MessageNetwork Principal A) : MessageNetwork Principal B :=
  ⟨network.pending.map (Message.mapPayload f), network.ledger.map (Message.mapPayload f),
    fun who => (network.leaked who).map (Message.mapPayload f),
    network.inputs.map (Message.mapPayload f), network.nextSerial⟩

def PublicView.mapPayload (f : A → B) (view : PublicView Principal A) : PublicView Principal B :=
  ⟨view.pending.map (Message.mapPayload f), view.ledger.map (Message.mapPayload f),
    view.inputs.map (Message.mapPayload f), view.nextSerial⟩

def PlayerView.mapPayload (f : A → B) (view : PlayerView Principal A) : PlayerView Principal B :=
  ⟨view.leaked.map (Message.mapPayload f), view.ledger.map (Message.mapPayload f)⟩

variable [DecidableEq Principal]

theorem mapPayload_known (f : A → B) (network : MessageNetwork Principal A) (who : Principal) :
    (network.mapPayload f).known who = (network.known who).map (Message.mapPayload f) := by
  simp only [known, mapPayload, List.map_append, List.filter_map, Function.comp_def,
    Message.sender, Message.mapPayload]

end MessageNetwork
end Interaction
