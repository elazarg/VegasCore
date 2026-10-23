/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveSettledVerdict

/-! # Packet verdicts from signed traffic alone

A packet is permitted when it is well formed for the event it names and is its
sender's first packet for that event:

* its sender owns the event and its readiness token names the event;
* a commitment names a binding event of the sender, carries no evidence, and
  uses a prepared handle of the sender that none of the sender's lower-serial
  commitments named;
* an opening names a resolve event of the sender, carries exactly its own
  certificate, has the value type of the binding, and opens the handle the
  sender's own signed data bound to that field: the fixed handle of an initial
  binding input, or the handle of a lower-serial commitment of the sender for
  the binding event;
* no lower-serial packet of the sender names the same event.

The verdict reads signed content, tokens and serials of the sender's own
packets with lower serials, and nothing else. It reads no receipt, inclusion,
ledger, public view or send time, so non-inclusion alone never makes a packet
forbidden, and a packet's verdict is fixed once it is signed: later packets of
the same sender carry higher serials and cannot change it.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- `other` is a packet in `traffic` with the sender of `message` and a lower
serial. -/
def EarlierOwnPacket (traffic : List (Message Player (WitnessedPacket graph)))
    (message other : Message Player (WitnessedPacket graph)) : Prop :=
  other ∈ traffic ∧ other.sender = message.sender ∧ other.id.2 < message.id.2

/-- The sender's own signed data binds `candidate` to `field`: an initial
binding input carries its fixed input handle, and a binding event carries the
handle of one of the given earlier commitments for it. -/
def SignedBinding (earlier : Message Player (WitnessedPacket graph) → Prop)
    (sender : Player) (candidate : Handle graph) : graph.Field → Prop
  | .inl input => candidate = (sender, .initial input)
  | .inr event => ∃ other, earlier other ∧ other.payload.call = .commitment event candidate

/-- The packet's call is correct for the event it names, given the sender's
earlier packets. A malformed call is never correct. -/
def CountCallCorrect (earlier : Message Player (WitnessedPacket graph) → Prop)
    (message : Message Player (WitnessedPacket graph)) : Prop :=
  match message.payload.call with
  | .commitment event candidate =>
      bindingOwnedBy graph message.sender event = true ∧ message.payload.evidence = none ∧
        candidate.1 = message.sender ∧ (∃ serial, candidate.2 = .prepared serial) ∧
        ∀ other, earlier other → ∀ named, other.payload.call ≠ .commitment named candidate
  | .opening event candidate raw =>
      certifiedOpening message.payload = true ∧
        match nodeView graph event with
        | .resolve owner payload binding _ _ _ =>
            message.sender = owner ∧ raw.ty = payload ∧
              SignedBinding earlier message.sender candidate binding.field
        | .bind .. | .sample .. => False
  | .malformed _ => False

/-- No earlier packet names the event this packet names. -/
def FirstForEvent (earlier : Message Player (WitnessedPacket graph) → Prop)
    (message : Message Player (WitnessedPacket graph)) : Prop :=
  ∀ other, earlier other → other.payload.call.event? graph ≠ message.payload.call.event? graph

/-- The count verdict relative to a set of earlier packets of the sender. -/
def CountPermitsAmong (earlier : Message Player (WitnessedPacket graph) → Prop)
    (message : Message Player (WitnessedPacket graph)) : Prop :=
  message.payload.tokenValid = true ∧ CountCallCorrect earlier message ∧
    FirstForEvent earlier message

/-- **The count verdict.** A packet is permitted when it is well formed and
first for its event among the sender's packets in `traffic`. -/
def CountPermits (traffic : List (Message Player (WitnessedPacket graph)))
    (message : Message Player (WitnessedPacket graph)) : Prop :=
  CountPermitsAmong (EarlierOwnPacket traffic message) message

open Classical in
/-- The count verdict as a Boolean. -/
def countPermits (traffic : List (Message Player (WitnessedPacket graph)))
    (message : Message Player (WitnessedPacket graph)) : Bool :=
  decide (CountPermits traffic message)

theorem countPermits_eq_true_iff (traffic : List (Message Player (WitnessedPacket graph)))
    (message : Message Player (WitnessedPacket graph)) :
    countPermits traffic message = true ↔ CountPermits traffic message := by
  classical
  simp only [countPermits, decide_eq_true_eq]

/-- The verdict reads `traffic` only through the sender's packets with lower
serials. -/
theorem countPermits_congr (left right : List (Message Player (WitnessedPacket graph)))
    (message : Message Player (WitnessedPacket graph))
    (same : ∀ other, EarlierOwnPacket left message other ↔ EarlierOwnPacket right message other) :
    countPermits left message = countPermits right message := by
  have earlier : EarlierOwnPacket left message = EarlierOwnPacket right message :=
    funext fun other => propext (same other)
  rw [Bool.eq_iff_iff, countPermits_eq_true_iff, countPermits_eq_true_iff]
  unfold CountPermits
  rw [earlier]

/-- Packets of other senders, and packets of the sender with serials no lower
than this one's, never change its verdict. -/
theorem countPermits_append_later (traffic later : List (Message Player (WitnessedPacket graph)))
    (message : Message Player (WitnessedPacket graph))
    (laterSerial : ∀ other ∈ later, other.sender = message.sender → message.id.2 ≤ other.id.2) :
    countPermits (traffic ++ later) message = countPermits traffic message := by
  apply countPermits_congr
  intro other
  constructor
  · rintro ⟨member, owner, lower⟩
    rcases List.mem_append.mp member with old | new
    · exact ⟨old, owner, lower⟩
    · exact absurd lower (Nat.not_lt.mpr (laterSerial other new owner))
  · rintro ⟨member, owner, lower⟩
    exact ⟨List.mem_append_left _ member, owner, lower⟩

/-- A packet is not among its own earlier packets, so appending it to traffic
does not change its own verdict. -/
theorem countPermits_append_self (traffic : List (Message Player (WitnessedPacket graph)))
    (message : Message Player (WitnessedPacket graph)) :
    countPermits (traffic ++ [message]) message = countPermits traffic message :=
  countPermits_append_later traffic [message] message fun other member _ => by
    rw [List.mem_singleton.mp member]

end Vegas.EventGraphRuntime
