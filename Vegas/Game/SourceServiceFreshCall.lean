/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealService
import Vegas.Pending.ReactiveFreshCallAcceptance
import Vegas.Pending.ReactiveCanonicalDecision

/-! # Acceptable protected source calls

A fresh call records the actual native packet, the public readiness and inclusion window
at its submission, and the handler's acceptance predicate. Authentic openings may publish
failure when deferred guards reject them.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
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

end Vegas
