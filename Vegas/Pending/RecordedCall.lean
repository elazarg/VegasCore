module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveFreshCallAcceptance
public import Vegas.Pending.ReactiveCanonicalDecision
public import Vegas.Pending.ReactiveAsyncContract

@[expose] public section

/-! # Acceptable protected calls

A fresh call records the actual native packet, the public readiness and inclusion window
at its submission, and the handler's acceptance predicate. Authentic openings may publish
failure when deferred guards reject them.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- The envelope a response transmitting `material` emits. -/
def sentEnvelope (execution : ((reactiveApplication timeouts) leaks).Execution) (who : Player)
    (material : ((reactiveApplication timeouts) leaks).Submission) :
    Message Player (WitnessedPacket graph) :=
  ⟨(who, execution.network.nextSerial who),
    ((reactiveApplication timeouts) leaks).packet
      (((reactiveApplication timeouts) leaks).submit execution.application who material) who
      (execution.network.known who) material⟩


/-- The recall entry a response appends: the view it was made from, the
response, and the envelope it emits. -/
def respondEntry (execution : ((reactiveApplication timeouts) leaks).Execution) (who : Player)
    (response : ((reactiveApplication timeouts) leaks).Action) :
      ((reactiveApplication timeouts) leaks).PlayerEntry :=
  ⟨execution.observe ((reactiveApplication timeouts) leaks) who, response,
    response.transmission.map (sentEnvelope timeouts leaks execution who)⟩

variable {timeouts leaks} in
/-- The entry of a transmitting response records its envelope. -/
theorem respondEntry_of_transmission (execution : ((reactiveApplication timeouts) leaks).Execution)
    (who : Player) (response : ((reactiveApplication timeouts) leaks).Action)
    (material : ((reactiveApplication timeouts) leaks).Submission)
    (submits : response.transmission = some material) :
    respondEntry timeouts leaks execution who response =
      ⟨execution.observe ((reactiveApplication timeouts) leaks) who, response,
        some (sentEnvelope timeouts leaks execution who material)⟩ := by
  unfold respondEntry
  rw [submits]
  rfl
/-- A fresh call the handler accepts when included in time: the acceptance part
of the audit's public conformance rule, evaluated on the view its author saw
when emitting it. -/
def AcceptableFreshCall (entry : ((reactiveApplication timeouts) leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket graph)) : Prop :=
  (freshServiceAcceptable timeouts)
  entry.beforeView.application.publicView message

/-- One recorded fresh call of `owner` for `event`: a fresh submission, sent
while the event was ready and early enough that an inclusion within
`bound event` slots lands before the deadline, and acceptable on the view its
author saw. -/
structure FreshCall (owner : Player) (event : graph.EventId)
    (bound : graph.EventId → Nat)
    (entry : ((reactiveApplication timeouts) leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket graph)) : Prop where
  fresh : ∃ material, entry.action.transmission = some material
  emitted : entry.emitted = some message
  authored : message.sender = owner
  addressed : message.payload.call.event? graph = some event
  ready : entry.beforeView.application.publicView.EventReady event
  fits : entry.beforeView.application.publicView.InclusionFitsDeadline
      timeouts bound event
  conforming : AcceptableFreshCall timeouts leaks entry message

/-- An event completes only together with an accepting receipt for `id`, and
every receipt for `id` is accompanied by an accepting one. -/
def Settled (event : graph.EventId) (id : MessageId Player)
    (execution : ((reactiveApplication timeouts) leaks).Execution) : Prop :=
  (event ∈ execution.application.config.cut.completed → (id, true) ∈ execution.receipts) ∧
    (∀ accepted, (id, accepted) ∈ execution.receipts → (id, true) ∈ execution.receipts) ∧
    ((id, true) ∈ execution.receipts → event ∈ execution.application.config.cut.completed)

/-- Every recorded fresh call of `owner` for `event`, with no other identifier
emitted by `owner` for the event, is settled. -/
def SettlesFreshCalls (owner : Player) (event : graph.EventId)
    (bound : graph.EventId → Nat)
    (execution : ((reactiveApplication timeouts) leaks).Execution) :
    Prop :=
  ∀ earlier entry later message, execution.logs owner = earlier ++ entry :: later →
    FreshCall timeouts leaks owner event bound entry message →
    (∀ other ∈ earlier ++ later, ¬ EmitsOtherFor timeouts leaks other
        event message.id) →
    Settled timeouts leaks event message.id execution

end Vegas.EventGraphRuntime
