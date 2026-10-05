/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveRevealBlock
import Vegas.Pending.ReactiveOpeningConformance

/-! # Public transcript of canonical reveal service

Successful publication results and the public handle table determine the
certified opening packets. Numbering those packets determines the ledger,
successful receipts, and sender counters. This is an observation encoder, not
an executor: the service proof must establish equality with these fields.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]

namespace RevealTranscript

/-- Assign each public packet its sender's next serial number. -/
def numberPackets {Payload : Type} (serial : Player → Nat) :
    List (Player × Payload) → List (Message Player Payload)
  | [] => []
  | (who, payload) :: rest =>
      ⟨(who, serial who), payload⟩ ::
        numberPackets (Function.update serial who (serial who + 1)) rest

theorem numberPackets_decode {Payload : Type} (serial : Player → Nat)
    (packets : List (Player × Payload)) :
    (numberPackets serial packets).map (fun message => (message.sender, message.payload)) =
      packets := by
  induction packets generalizing serial with
  | nil => rfl
  | cons packet rest ih =>
      cases packet
      simp only [numberPackets, List.map_cons, ih]
      rfl

/-- The serial of one extra packet counts precisely earlier packets by the
same sender. -/
theorem numberPackets_append {Payload : Type} (serial : Player → Nat)
    (packets : List (Player × Payload)) (who : Player) (payload : Payload) :
    numberPackets serial (packets ++ [(who, payload)]) =
      numberPackets serial packets ++
        [⟨(who, serial who + packets.countP (fun packet => packet.1 = who)), payload⟩] := by
  induction packets generalizing serial with
  | nil => simp [numberPackets]
  | cons packet rest ih =>
      obtain ⟨sender, value⟩ := packet
      simp only [List.cons_append, numberPackets, ih, List.countP_cons]
      by_cases same : sender = who
      · subst sender
        simp [Nat.add_assoc, Nat.add_comm]
      · simp [same, Function.update_of_ne (Ne.symm same)]

end RevealTranscript

variable {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A successful public resolve result identifies the canonical call and its
authentic certificate. Binding values are never read by this function. -/
def publicationPacket? (accepted : AcceptedHandles graph)
    (store : EventGraph.Store graph.layout) (event : graph.EventId) :
    Option (Player × WitnessedPacket graph) :=
  match nodeView graph event with
  | .sample .. | .bind .. => none
  | .resolve owner payload binding _ outputEq _ =>
      match (store (.inr event)).map (cast (congrArg EventField.Value outputEq)) with
      | none | some .failure => none
      | some (.success value) =>
          (accepted binding.field).map fun candidate =>
            (owner, ⟨.opening event candidate ⟨payload, value⟩,
              some ⟨candidate, ⟨payload, value⟩⟩, some ⟨event⟩⟩)

omit [DecidableEq Player] in
theorem publicationPacket?_congr (accepted : AcceptedHandles graph)
    (left right : EventGraph.Store graph.layout) (event : graph.EventId)
    (same : left (.inr event) = right (.inr event)) :
    publicationPacket? accepted left event = publicationPacket? accepted right event := by
  unfold publicationPacket?
  cases nodeView graph event <;> simp only [same]

omit [DecidableEq Player] in
theorem publicationPacket?_publicStore (accepted : AcceptedHandles graph)
    (store : EventGraph.Store graph.layout) (event : graph.EventId) :
    publicationPacket? accepted (graph.publicStore store) event =
      publicationPacket? accepted store event := by
  unfold publicationPacket?
  cases nodeView graph event with
  | sample => rfl
  | bind => rfl
  | resolve owner payload binding checks outputEq codeEq =>
      have visible : graph.fieldPublic (.inr event) := by
        change (graph.outputLayout event).IsPublic
        rw [outputEq]
        trivial
      rw [graph.publicStore_of_public store (.inr event) visible]

/-- Chronological successfully published calls, before assigning message ids. -/
def publicationPackets (accepted : AcceptedHandles graph) (view : graph.PublicObservation) :
    List (Player × WitnessedPacket graph) :=
  view.completionOrder.filterMap (publicationPacket? accepted view.store)

omit [DecidableEq Player] in
theorem publicationPackets_observe (accepted : AcceptedHandles graph) (config : graph.Config) :
    publicationPackets accepted (graph.publicObserve config) =
      (config.history.map Completion.event).filterMap
        (publicationPacket? accepted config.store) := by
  unfold publicationPackets EventGraph.publicObserve
  apply List.filterMap_congr
  intro event _
  exact publicationPacket?_publicStore accepted config.store event

omit [DecidableEq Player] in
theorem publicationPacket?_resolve (accepted : AcceptedHandles graph)
    (store : EventGraph.Store graph.layout) (event : graph.EventId)
    (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (result : PublicationResult (L.Val payload))
    (stored : (store (.inr event)).map (cast (congrArg EventField.Value outputEq)) = some result) :
    publicationPacket? accepted store event = match result with
      | .failure => none
      | .success value => (accepted binding.field).map fun candidate =>
          (owner, ⟨.opening event candidate ⟨payload, value⟩,
            some ⟨candidate, ⟨payload, value⟩⟩, some ⟨event⟩⟩) := by
  simp only [publicationPacket?, node, stored]
  cases result <;> rfl

omit [DecidableEq Player] in
/-- A completion changes the encoded transcript only at its newly completed
event; all earlier packets remain exactly intact. -/
theorem publicationPackets_complete (accepted : AcceptedHandles graph) (config : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event)
    (action : graph.Action event) (value : (graph.outputLayout event).Value) :
    publicationPackets accepted (graph.publicObserve (config.complete event ready action value)) =
      publicationPackets accepted (graph.publicObserve config) ++
        (publicationPacket? accepted
          (config.complete event ready action value).store event).toList := by
  rw [publicationPackets_observe, publicationPackets_observe, Config.complete_history,
    List.map_append, List.map_singleton, List.filterMap_append]
  congr 1
  · apply List.filterMap_congr
    intro prior member
    apply publicationPacket?_congr
    change (config.complete event ready action value).outputs prior = config.outputs prior
    apply Config.complete_output_of_ne
    intro same
    subst prior
    exact ready.1 ((config.history_exact event).mp member)

omit [DecidableEq Player] in
theorem publicationPacket?_complete_resolve (accepted : AcceptedHandles graph)
    (config : graph.Config) (event : graph.EventId) (ready : config.cut.Ready event)
    (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (action : graph.Action event) (result : PublicationResult (L.Val payload)) :
    publicationPacket? accepted
      (config.complete event ready action
        (cast (congrArg EventField.Value outputEq.symm) result)).store
      event = match result with
      | .failure => none
      | .success value => (accepted binding.field).map fun candidate =>
          (owner, ⟨.opening event candidate ⟨payload, value⟩,
            some ⟨candidate, ⟨payload, value⟩⟩, some ⟨event⟩⟩) := by
  have stored : ((config.complete event ready action
      (cast (congrArg EventField.Value outputEq.symm) result)).store (.inr event)).map
        (cast (congrArg EventField.Value outputEq)) = some result := by
    rw [Config.store_output, Config.complete_output_same]
    simp only [Option.map_some, cast_cast, cast_eq]
  have formula := publicationPacket?_resolve accepted _ event owner payload binding checks
    outputEq codeEq node result stored
  cases result <;> exact formula

def publicationLedger (accepted : AcceptedHandles graph) (view : graph.PublicObservation) :
    List (Message Player (WitnessedPacket graph)) :=
  RevealTranscript.numberPackets (fun _ => 0) (publicationPackets accepted view)

def publicationReceipts (accepted : AcceptedHandles graph) (view : graph.PublicObservation) :
    List (MessageId Player × Bool) :=
  (publicationLedger accepted view).map (fun message => (message.id, true))

def publicationSerial (accepted : AcceptedHandles graph) (view : graph.PublicObservation)
    (who : Player) : Nat :=
  (publicationPackets accepted view).countP (fun packet => packet.1 = who)

@[simp] theorem publicationLedger_initial (accepted : AcceptedHandles graph)
    (inputs : graph.Inputs) :
    publicationLedger accepted (graph.publicObserve (Config.initial inputs)) = [] := rfl

@[simp] theorem publicationReceipts_initial (accepted : AcceptedHandles graph)
    (inputs : graph.Inputs) :
    publicationReceipts accepted (graph.publicObserve (Config.initial inputs)) = [] := rfl

@[simp] theorem publicationSerial_initial (accepted : AcceptedHandles graph)
    (inputs : graph.Inputs) :
    publicationSerial accepted (graph.publicObserve (Config.initial inputs)) = fun _ => 0 := rfl

/-- Decoding removes only the deterministic per-sender numbering. -/
theorem publicationLedger_decode (accepted : AcceptedHandles graph)
    (view : graph.PublicObservation) :
    (publicationLedger accepted view).map (fun message => (message.sender, message.payload)) =
      publicationPackets accepted view := RevealTranscript.numberPackets_decode _ _

theorem publicationLedger_complete (accepted : AcceptedHandles graph) (config : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event)
    (action : graph.Action event) (value : (graph.outputLayout event).Value)
    (who : Player) (packet : WitnessedPacket graph)
    (selected : publicationPacket? accepted (config.complete event ready action value).store event =
      some (who, packet)) :
    publicationLedger accepted (graph.publicObserve (config.complete event ready action value)) =
      publicationLedger accepted (graph.publicObserve config) ++
        [⟨(who, publicationSerial accepted (graph.publicObserve config) who), packet⟩] := by
  unfold publicationLedger
  rw [publicationPackets_complete, selected, Option.toList_some,
    RevealTranscript.numberPackets_append]
  simp only [publicationSerial, Nat.zero_add]

theorem publicationReceipts_complete (accepted : AcceptedHandles graph) (config : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event)
    (action : graph.Action event) (value : (graph.outputLayout event).Value)
    (who : Player) (packet : WitnessedPacket graph)
    (selected : publicationPacket? accepted (config.complete event ready action value).store event =
      some (who, packet)) :
    publicationReceipts accepted (graph.publicObserve (config.complete event ready action value)) =
      publicationReceipts accepted (graph.publicObserve config) ++
        [((who, publicationSerial accepted (graph.publicObserve config) who), true)] := by
  unfold publicationReceipts
  rw [publicationLedger_complete accepted config event ready action value who packet selected]
  rw [List.map_append, List.map_singleton]

theorem publicationSerial_complete (accepted : AcceptedHandles graph) (config : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event)
    (action : graph.Action event) (value : (graph.outputLayout event).Value)
    (who : Player) (packet : WitnessedPacket graph)
    (selected : publicationPacket? accepted (config.complete event ready action value).store event =
      some (who, packet)) (observer : Player) :
    publicationSerial accepted (graph.publicObserve (config.complete event ready action value))
        observer =
      publicationSerial accepted (graph.publicObserve config) observer +
        if who = observer then 1 else 0 := by
  unfold publicationSerial
  rw [publicationPackets_complete, selected, Option.toList_some, List.countP_append]
  simp

theorem publicationLedger_complete_none (accepted : AcceptedHandles graph) (config : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event)
    (action : graph.Action event) (value : (graph.outputLayout event).Value)
    (absent : publicationPacket? accepted (config.complete event ready action value).store event =
      none) :
    publicationLedger accepted (graph.publicObserve (config.complete event ready action value)) =
      publicationLedger accepted (graph.publicObserve config) := by
  simp only [publicationLedger, publicationPackets_complete, absent, Option.toList_none,
    List.append_nil]

theorem publicationSerial_complete_none (accepted : AcceptedHandles graph) (config : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event)
    (action : graph.Action event) (value : (graph.outputLayout event).Value)
    (absent : publicationPacket? accepted (config.complete event ready action value).store event =
      none) :
    publicationSerial accepted (graph.publicObserve (config.complete event ready action value)) =
      publicationSerial accepted (graph.publicObserve config) := by
  funext who
  unfold publicationSerial
  rw [publicationPackets_complete, absent, Option.toList_none, List.append_nil]

theorem publicationReceipts_complete_none (accepted : AcceptedHandles graph)
    (config : graph.Config) (event : graph.EventId) (ready : config.cut.Ready event)
    (action : graph.Action event) (value : (graph.outputLayout event).Value)
    (absent : publicationPacket? accepted (config.complete event ready action value).store event =
      none) :
    publicationReceipts accepted (graph.publicObserve (config.complete event ready action value)) =
      publicationReceipts accepted (graph.publicObserve config) := by
  unfold publicationReceipts
  rw [publicationLedger_complete_none accepted config event ready action value absent]

/-- Every encoded packet has exactly the public certificate format audited by
the monitor. This does not assert that a raw runtime ledger has this encoding. -/
theorem publicationPacket?_certified (accepted : AcceptedHandles graph)
    (store : EventGraph.Store graph.layout) (event : graph.EventId)
    (packet : Player × WitnessedPacket graph)
    (encoded : publicationPacket? accepted store event = some packet) :
    certifiedOpening packet.2 = true := by
  unfold publicationPacket? at encoded
  cases node : nodeView graph event with
  | sample => simp only [node] at encoded; cases encoded
  | bind => simp only [node] at encoded; cases encoded
  | resolve owner payload binding checks outputEq codeEq =>
    simp only [node] at encoded
    split at encoded
    · cases encoded
    · cases encoded
    · cases found : accepted binding.field with
      | none => simp only [found, Option.map_none] at encoded; cases encoded
      | some candidate =>
          simp only [found, Option.map_some, Option.some.injEq] at encoded
          subst packet
          simp only [certifiedOpening, decide_true]

theorem publicationLedger_certified (accepted : AcceptedHandles graph)
    (view : graph.PublicObservation) (message : Message Player (WitnessedPacket graph))
    (member : message ∈ publicationLedger accepted view) :
    certifiedOpening message.payload = true := by
  have decoded : (message.sender, message.payload) ∈ publicationPackets accepted view := by
    rw [← RevealTranscript.numberPackets_decode (fun _ : Player => 0)
      (publicationPackets accepted view)]
    exact List.mem_map_of_mem member
  obtain ⟨event, _completed, encoded⟩ := List.mem_filterMap.mp decoded
  exact publicationPacket?_certified accepted view.store event _ encoded

theorem publicationReceipts_successful (accepted : AcceptedHandles graph)
    (view : graph.PublicObservation) (id : MessageId Player) :
    (id, false) ∉ publicationReceipts accepted view := by
  intro rejected
  obtain ⟨message, _published, impossible⟩ := List.mem_map.mp rejected
  exact Bool.noConfusion (congrArg Prod.snd impossible)

end Vegas.EventGraphRuntime
