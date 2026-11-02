/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealService
import Vegas.Pending.ReactiveFreshCallAcceptance
import Vegas.Pending.ReactiveCanonicalDecision
import Vegas.Pending.ReactiveAsyncContract

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
variable (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The envelope a response transmitting `material` emits. -/
def sentEnvelope (execution : (application setup runtime leaks).Execution) (who : Player)
    (material : (application setup runtime leaks).Submission) :
    Message Player (WitnessedPacket (graph setup)) :=
  ⟨(who, execution.network.nextSerial who),
    (application setup runtime leaks).packet
      ((application setup runtime leaks).submit execution.application who material) who
      (execution.network.known who) material⟩


/-- The recall entry a response appends: the view it was made from, the
response, and the envelope it emits. -/
def respondEntry (execution : (application setup runtime leaks).Execution) (who : Player)
    (response : (application setup runtime leaks).Action) : (application setup runtime
      leaks).PlayerEntry :=
  ⟨execution.observe (application setup runtime leaks) who, response,
    response.transmission.map (sentEnvelope setup runtime leaks execution who)⟩

variable {setup runtime leaks}

/-- The entry of a transmitting response records its envelope. -/
theorem respondEntry_of_transmission (execution : (application setup runtime leaks).Execution)
    (who : Player) (response : (application setup runtime leaks).Action)
    (material : (application setup runtime leaks).Submission)
    (submits : response.transmission = some material) :
    respondEntry setup runtime leaks execution who response =
      ⟨execution.observe (application setup runtime leaks) who, response,
        some (sentEnvelope setup runtime leaks execution who material)⟩ := by
  unfold respondEntry
  rw [submits]
  rfl
end RecordedResponses

variable (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- A fresh call the handler accepts when included in time: the acceptance part
of the audit's public conformance rule, evaluated on the view its author saw
when emitting it. -/
def AcceptableFreshCall (entry : (serviceApplication setup mode deadline leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode))) : Prop :=
  (serviceRuntime setup mode deadline).freshServiceAcceptable
  entry.beforeView.application.publicView message

/-- One recorded fresh call of `owner` for `event`: a fresh submission, sent
while the event was ready and early enough that an inclusion within
`bound event` slots lands before the deadline, and acceptable on the view its
author saw. -/
structure FreshCall (owner : Player) (event : (serviceGraph setup mode).EventId)
    (bound : (serviceGraph setup mode).EventId → Nat)
    (entry : (serviceApplication setup mode deadline leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode))) : Prop where
  fresh : ∃ material, entry.action.transmission = some material
  emitted : entry.emitted = some message
  authored : message.sender = owner
  addressed : message.payload.call.event? (serviceGraph setup mode) = some event
  ready : entry.beforeView.application.publicView.EventReady event
  fits : entry.beforeView.application.publicView.InclusionFitsDeadline
      (serviceRuntime setup mode deadline) bound event
  conforming : AcceptableFreshCall setup leaks entry message

/-- An event completes only together with an accepting receipt for `id`, and
every receipt for `id` is accompanied by an accepting one. -/
def Settled (event : (serviceGraph setup mode).EventId) (id : MessageId Player)
    (execution : (serviceApplication setup mode deadline leaks).Execution) : Prop :=
  (event ∈ execution.application.config.cut.completed → (id, true) ∈ execution.receipts) ∧
    (∀ accepted, (id, accepted) ∈ execution.receipts → (id, true) ∈ execution.receipts) ∧
    ((id, true) ∈ execution.receipts → event ∈ execution.application.config.cut.completed)

/-- Every recorded fresh call of `owner` for `event`, with no other identifier
emitted by `owner` for the event, is settled. -/
def SettlesFreshCalls (owner : Player) (event : (serviceGraph setup mode).EventId)
    (bound : (serviceGraph setup mode).EventId → Nat)
    (execution : (serviceApplication setup mode deadline leaks).Execution) :
    Prop :=
  ∀ earlier entry later message, execution.logs owner = earlier ++ entry :: later →
    FreshCall setup leaks owner event bound entry message →
    (∀ other ∈ earlier ++ later, ¬ EmitsOtherFor (serviceRuntime setup mode deadline) leaks other
        event message.id) →
    Settled setup leaks event message.id execution

end Vegas
