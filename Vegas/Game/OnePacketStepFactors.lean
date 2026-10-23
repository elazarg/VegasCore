/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLateMasses

/-! # Factors of a response step, read from late-delivery keys

A key's pending event is its turn, unless one of its envelopes names it
(`Vegas.LateKey.pending`); a key is a late delivery when its pending event was
its turn at a recalled view (`Vegas.LateKey.IsLate`). From the keys of the
responder before and after a response, the factors of the as-if-honest law
(`Vegas.honestFactor`), of a late option (`Vegas.lateOptionFactor`) and of the
slot tier (`Vegas.slotTierFactor`) are read case by case: without a pending
event every factor is one; at a pending binding they are the pending-binding
factors; at a pending reveal, a law sending the disclosure has factor one when
the response transmits and zero when it is silent.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

namespace LateKey

open Classical in
/-- The key's pending event: its turn, unless one of its envelopes names it. -/
def pending (key : LateKey setup leaks) : Option (graph setup).EventId :=
  key.turn.filter fun event => !decide (key.Recorded event)

/-- The key is a late delivery: its pending event was its turn at a recalled
view. -/
def IsLate (key : LateKey setup leaks) : Prop :=
  ∃ event, key.pending = some event ∧
    ∃ entry ∈ key.recalled, entry.1.1.ownTurn? key.owner = some event

end LateKey

/-- The factor of a law sending the disclosure at a reveal: one when the
response transmits, zero when it is silent. -/
def transmitFactor (after : LateKey setup leaks) : ℝ :=
  1 - silenceFactor after

/-- **The as-if-honest factor.** One without a pending event; at a pending
binding, the commitment at the canonical slot; at a pending reveal, the
disclosure. -/
def honestFactor (before after : LateKey setup leaks) : ℝ :=
  match before.pending with
  | none => 1
  | some event =>
      match nodeView (graph setup) event with
      | .bind .. => pendingBindingHonestFactor before after
      | _ => transmitFactor after

variable [Fintype Player] (bounds : MessageBounds (graph setup))

/-- **The slot-tier factor.** One without a pending event; at a pending binding,
the uniform tremble slot; at a pending reveal, the disclosure. -/
def slotTierFactor (before after : LateKey setup leaks) : ℝ :=
  match before.pending with
  | none => 1
  | some event =>
      match nodeView (graph setup) event with
      | .bind .. => pendingBindingSlotFactor bounds before after event
      | _ => transmitFactor after

open Classical in
/-- **The factor of a late option.** Waiting is silence. Sending at a slot is
silence without a pending event; at a pending binding it commits at that slot,
and is silence when the slot is beyond the capacity or rejected; at a pending
reveal it sends the disclosure. -/
def lateOptionFactor {slots : Nat} (before after : LateKey setup leaks) :
    LateOption slots → ℝ
  | none => silenceFactor after
  | some slot =>
      match before.pending with
      | none => silenceFactor after
      | some event =>
          match nodeView (graph setup) event with
          | .bind .. =>
              match (after.lastEmitted.map fun message => message.payload.call :
                  Option (Payload (graph setup))) with
              | some (.commitment _ (_, .prepared committed)) =>
                  if committed = slot.val then 1 else 0
              | _ => if slot.val < bounds.candidateCount ∧
                  before.slotPermitted event slot.val = true then 0 else 1
          | _ => transmitFactor after

end Vegas
