/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

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

theorem mapPayload_empty (f : A → B) :
    mapPayload f (empty : MessageNetwork Principal A) = empty := rfl

theorem mapPayload_comp (f : A → B) (g : B → C) (network : MessageNetwork Principal A) :
    (network.mapPayload f).mapPayload g = network.mapPayload (g ∘ f) := by
  cases network
  simp only [mapPayload, List.map_map, Function.comp_def, Message.mapPayload]
  rfl

theorem mapPayload_publicView (f : A → B) (network : MessageNetwork Principal A) :
    (network.mapPayload f).publicView = network.publicView.mapPayload f := rfl

theorem mapPayload_observe (f : A → B) (network : MessageNetwork Principal A) (who : Principal) :
    (network.mapPayload f).observe who = (network.observe who).mapPayload f := rfl

variable [DecidableEq Principal]

private theorem find_mapPayload (f : A → B) (messages : List (Message Principal A))
    (id : MessageId Principal) :
    (messages.map (Message.mapPayload f)).find? (fun message => message.id = id) =
      (messages.find? (fun message => message.id = id)).map (Message.mapPayload f) := by
  induction messages with
  | nil => rfl
  | cons message rest ih =>
      simp only [List.map_cons, List.find?_cons, Message.mapPayload]
      split <;> simp_all only [Option.map_some]
      rfl

theorem mapPayload_lookup (f : A → B) (network : MessageNetwork Principal A)
    (id : MessageId Principal) :
    (network.mapPayload f).lookup id = (network.lookup id).map (Message.mapPayload f) :=
  find_mapPayload f network.pending id

theorem mapPayload_known (f : A → B) (network : MessageNetwork Principal A) (who : Principal) :
    (network.mapPayload f).known who = (network.known who).map (Message.mapPayload f) := by
  simp only [known, mapPayload, List.map_append, List.filter_map, Function.comp_def,
    Message.sender, Message.mapPayload]

theorem mapPayload_submit (f : A → B) (network : MessageNetwork Principal A)
    (who : Principal) (payload : A) :
    ((network.submit who payload).1.mapPayload f, (network.submit who payload).2.mapPayload f) =
      (network.mapPayload f).submit who (f payload) := by
  simp only [submit, mapPayload, Message.mapPayload, List.map_append, List.map_cons, List.map_nil]

private theorem removeFirst_mapPayload (f : A → B) (messages : List (Message Principal A))
    (id : MessageId Principal) :
    (MessagePool.removeFirst id messages).map (Message.mapPayload f) =
      MessagePool.removeFirst id (messages.map (Message.mapPayload f)) := by
  induction messages with
  | nil => rfl
  | cons message rest ih =>
      simp only [MessagePool.removeFirst, List.map_cons, Message.mapPayload]
      split <;> simp_all only [List.map_cons]
      rfl

theorem mapPayload_includePending (f : A → B) (network : MessageNetwork Principal A)
    (id : MessageId Principal) :
    (((network.includePending id).1.map (Message.mapPayload f)),
      (network.includePending id).2.mapPayload f) =
        (network.mapPayload f).includePending id := by
  unfold includePending
  rw [mapPayload_lookup]
  cases found : network.lookup id with
  | none => rfl
  | some message =>
      simp only [Option.map_some, mapPayload, List.map_append, List.map_cons, List.map_nil,
        removeFirst_mapPayload]

theorem mapPayload_learn (f : A → B) (network : MessageNetwork Principal A) (who : Principal)
    (selected : Finset (MessageId Principal)) :
    (network.learn who selected).mapPayload f = (network.mapPayload f).learn who selected := by
  have known : ∀ id, ((network.mapPayload f).known who).any (fun message => message.id = id) =
      (network.known who).any (fun message => message.id = id) := by
    intro id
    rw [mapPayload_known]
    simp only [List.any_map, Function.comp_def, Message.mapPayload]
  unfold learn
  simp only [known, mapPayload_lookup]
  simp only [mapPayload]
  congr 1
  funext observer
  split <;> simp_all only [List.map_append, List.map_filterMap]
  simp only [List.map_map, Function.comp_def, Message.mapPayload]

end MessageNetwork
end Interaction
