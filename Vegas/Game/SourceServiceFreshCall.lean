module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.RevealService
public import Vegas.Pending.ReactiveFreshCallAcceptance
public import Vegas.Pending.ReactiveCanonicalDecision
public import Vegas.Pending.ReactiveAsyncContract

@[expose] public section

/-! # Acceptable protected source calls

A fresh call records the actual native packet, the public readiness and inclusion window
at its submission, and the handler's acceptance predicate. Authentic openings may publish
failure when deferred guards reject them.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

section RecordedResponses
variable (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  (timeouts : EventTimeouts (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- The envelope a response transmitting `material` emits. -/
def sentEnvelope (execution : ((reactiveApplication timeouts) leaks).Execution) (who : Player)
    (material : ((reactiveApplication timeouts) leaks).Submission) :
    Message Player (WitnessedPacket (serviceGraph setup mode)) :=
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
    response.transmission.map (sentEnvelope setup timeouts leaks execution who)⟩

variable {setup timeouts leaks}

/-- The entry of a transmitting response records its envelope. -/
theorem respondEntry_of_transmission (execution : ((reactiveApplication timeouts) leaks).Execution)
    (who : Player) (response : ((reactiveApplication timeouts) leaks).Action)
    (material : ((reactiveApplication timeouts) leaks).Submission)
    (submits : response.transmission = some material) :
    respondEntry setup timeouts leaks execution who response =
      ⟨execution.observe ((reactiveApplication timeouts) leaks) who, response,
        some (sentEnvelope setup timeouts leaks execution who material)⟩ := by
  unfold respondEntry
  rw [submits]
  rfl
end RecordedResponses

variable (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {duration : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- A fresh call the handler accepts when included in time: the acceptance part
of the audit's public conformance rule, evaluated on the view its author saw
when emitting it. -/
def AcceptableFreshCall (entry : (serviceApplication setup mode duration leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode))) : Prop :=
  (freshServiceAcceptable (serviceTimeouts setup mode duration))
  entry.beforeView.application.publicView message

/-- One recorded fresh call of `owner` for `event`: a fresh submission, sent
while the event was ready and early enough that an inclusion within
`bound event` slots lands before the deadline, and acceptable on the view its
author saw. -/
structure FreshCall (owner : Player) (event : (serviceGraph setup mode).EventId)
    (bound : (serviceGraph setup mode).EventId → Nat)
    (entry : (serviceApplication setup mode duration leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode))) : Prop where
  fresh : ∃ material, entry.action.transmission = some material
  emitted : entry.emitted = some message
  authored : message.sender = owner
  addressed : message.payload.call.event? (serviceGraph setup mode) = some event
  ready : entry.beforeView.application.publicView.EventReady event
  fits : entry.beforeView.application.publicView.InclusionFitsDeadline
      (serviceTimeouts setup mode duration) bound event
  conforming : AcceptableFreshCall setup leaks entry message

/-- An event completes only together with an accepting receipt for `id`, and
every receipt for `id` is accompanied by an accepting one. -/
def Settled (event : (serviceGraph setup mode).EventId) (id : MessageId Player)
    (execution : (serviceApplication setup mode duration leaks).Execution) : Prop :=
  (event ∈ execution.application.config.cut.completed → (id, true) ∈ execution.receipts) ∧
    (∀ accepted, (id, accepted) ∈ execution.receipts → (id, true) ∈ execution.receipts) ∧
    ((id, true) ∈ execution.receipts → event ∈ execution.application.config.cut.completed)

/-- Every recorded fresh call of `owner` for `event`, with no other identifier
emitted by `owner` for the event, is settled. -/
def SettlesFreshCalls (owner : Player) (event : (serviceGraph setup mode).EventId)
    (bound : (serviceGraph setup mode).EventId → Nat)
    (execution : (serviceApplication setup mode duration leaks).Execution) :
    Prop :=
  ∀ earlier entry later message, execution.logs owner = earlier ++ entry :: later →
    FreshCall setup leaks owner event bound entry message →
    (∀ other ∈ earlier ++ later, ¬ EmitsOtherFor (serviceTimeouts setup mode duration) leaks other
        event message.id) →
    Settled setup leaks event message.id execution

end Vegas
