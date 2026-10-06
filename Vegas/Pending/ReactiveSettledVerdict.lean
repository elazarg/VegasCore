/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveServiceConformance

/-! # Packet verdicts against the settled contract record

An auditor cannot prove when a packet was sent. A packet's verdict is
therefore a function of its signed content and of the contract's settled
record: the final public view and the receipt of every inclusion
(`Vegas.EventGraphRuntime.SettledRecord.Permits`). No part of it reads the
public view or the ledger at transmission.

A packet for an event the record has not settled is permitted. Once the event
has settled, a commitment or opening is permitted only when the record accepted
it, with its content checked against the record:

* a commitment carries no opening evidence and names the author's next prepared
  handle, counted from the author's bindings settled before the event;
* an opening carries its exact certificate, and the event's guards accept the
  opened value on the settled public store.

Every malformed packet is forbidden. Equivocation needs no separate rule: of
two packets of one author for one event the contract accepts at most one, and
the other is forbidden once the event settles. The same holds for an opening
sent after its owner withheld: it was not accepted, so it is forbidden whenever
it was sent.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The contract's settled record: its public view at settlement and the
receipt of every inclusion, in order. -/
structure SettledRecord (graph : Vegas.EventGraph Player L) where
  view : PublicView graph
  receipts : List (MessageId Player × Bool)

/-- `event` is a binding event owned by `who`. -/
def bindingOwnedBy (graph : Vegas.EventGraph Player L) (who : Player)
    (event : graph.EventId) : Bool :=
  match graph.outputLayout event with
  | .binding owner _ => decide (owner = who)
  | .publicData _ | .privateInput _ _ | .publication _ => false

theorem PublicView.bindingCount_eq_countP (view : PublicView graph) (who : Player) :
    view.bindingCount who =
      view.observation.completionOrder.countP (bindingOwnedBy graph who) := rfl

/-- `event` has not completed in the view. -/
def PublicView.Unsettled (view : PublicView graph) (event : graph.EventId) : Prop :=
  event ∉ view.observation.completionOrder

/-- The bindings of `who` that completed before `event` in the view's
completion order. -/
def PublicView.bindingCountBefore (view : PublicView graph) (who : Player)
    (event : graph.EventId) : Nat :=
  (view.observation.completionOrder.takeWhile (· ≠ event)).countP
    (bindingOwnedBy graph who)

namespace SettledRecord

/-- The record holds an accepting receipt for `id`. -/
def Accepts (record : SettledRecord graph) (id : MessageId Player) : Prop :=
  (id, true) ∈ record.receipts

/-- The content of a packet the record accepted, checked against the record. -/
def SettledContent (record : SettledRecord graph)
    (message : Message Player (WitnessedPacket graph)) : Prop :=
  match message.payload.call with
  | .commitment event candidate =>
      message.payload.evidence = none ∧
        candidate =
          (message.sender, .prepared (record.view.bindingCountBefore message.sender event))
  | .opening _ _ _ =>
      certifiedOpening message.payload = true ∧
        record.view.openingGuardsAccepted message.payload = true
  | .malformed _ => False

/-- **The settled verdict.** A packet for an unsettled event is permitted; a
packet for a settled event is permitted when the record accepted it and its
content checks against the record. It reads neither send time nor the ledger
at transmission. -/
def Permits (record : SettledRecord graph)
    (message : Message Player (WitnessedPacket graph)) : Prop :=
  match message.payload.call.event? graph with
  | none => False
  | some event =>
      record.view.Unsettled event ∨ (record.Accepts message.id ∧ record.SettledContent message)

open Classical in
/-- The settled verdict as a Boolean. -/
def permits (record : SettledRecord graph)
    (message : Message Player (WitnessedPacket graph)) : Bool :=
  decide (record.Permits message)

theorem permits_eq_true_iff (record : SettledRecord graph)
    (message : Message Player (WitnessedPacket graph)) :
    record.permits message = true ↔ record.Permits message := by
  classical
  simp only [permits, decide_eq_true_eq]

theorem permits_eq_false_iff (record : SettledRecord graph)
    (message : Message Player (WitnessedPacket graph)) :
    record.permits message = false ↔ ¬ record.Permits message := by
  classical
  simp only [permits, decide_eq_false_iff_not]

/-- At a record that settled the packet's event, the verdict is acceptance with
settled content. -/
theorem permits_eq_false_of_settled (record : SettledRecord graph)
    (message : Message Player (WitnessedPacket graph)) (event : graph.EventId)
    (named : message.payload.call.event? graph = some event)
    (settled : event ∈ record.view.observation.completionOrder)
    (rejected : ¬ (record.Accepts message.id ∧ record.SettledContent message)) :
    record.permits message = false := by
  rw [permits_eq_false_iff]
  unfold Permits
  rw [named]
  rintro (unsettled | accepted)
  · exact unsettled settled
  · exact rejected accepted

/-- A packet for no event is forbidden. -/
theorem permits_eq_false_of_none (record : SettledRecord graph)
    (message : Message Player (WitnessedPacket graph))
    (unnamed : message.payload.call.event? graph = none) :
    record.permits message = false := by
  rw [permits_eq_false_iff]
  unfold Permits
  rw [unnamed]
  exact id

/-- A packet for an unsettled event is permitted. -/
theorem permits_of_unsettled (record : SettledRecord graph)
    (message : Message Player (WitnessedPacket graph)) (event : graph.EventId)
    (named : message.payload.call.event? graph = some event)
    (unsettled : record.view.Unsettled event) :
    record.permits message = true := by
  rw [permits_eq_true_iff]
  unfold Permits
  rw [named]
  exact Or.inl unsettled

/-- An accepted packet with settled content is permitted. -/
theorem permits_of_accepted (record : SettledRecord graph)
    (message : Message Player (WitnessedPacket graph)) (event : graph.EventId)
    (named : message.payload.call.event? graph = some event)
    (accepted : record.Accepts message.id) (content : record.SettledContent message) :
    record.permits message = true := by
  rw [permits_eq_true_iff]
  unfold Permits
  rw [named]
  exact Or.inr ⟨accepted, content⟩

end SettledRecord

end Vegas.EventGraphRuntime
