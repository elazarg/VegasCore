/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveRevealBlock

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

/-- Chronological successfully published calls, before assigning message ids. -/
def publicationPackets (accepted : AcceptedHandles graph) (view : graph.PublicObservation) :
    List (Player × WitnessedPacket graph) :=
  view.completionOrder.filterMap (publicationPacket? accepted view.store)

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

end Vegas.EventGraphRuntime
