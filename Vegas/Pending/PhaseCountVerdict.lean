/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseApplication
import Vegas.Pending.ReactiveCountVerdict

/-! # Signed packet counts for permanent physical attempts

The native content and globally fresh handle rules are unchanged. Event-first
checks use the authenticated attempt address, so a retired first packet retains
its verdict and a retry receives a distinct packet allowance. All predicates
read signed content and serials, never submission time or inclusion receipts.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Forget only the physical namespace, retaining message identity and exact evidence. -/
def nativeMessage (message : Message Player (CommitAttemptPacket graph)) :
    Message Player (WitnessedPacket graph) := ⟨message.id, message.payload.packet⟩

/-- An earlier signed packet of the same principal. -/
def Earlier (traffic : List (Message Player (CommitAttemptPacket graph)))
    (message other : Message Player (CommitAttemptPacket graph)) : Prop :=
  other ∈ traffic ∧ other.sender = message.sender ∧ other.id.2 < message.id.2

/-- The complete physical event name, including its attempt namespace. -/
def event? (packet : CommitAttemptPacket graph) : Option (CommitAttemptEvent graph) :=
  (packet.packet.call.event? graph).map fun event => ⟨packet.attempt, event⟩

/-- There is no earlier own packet addressing this physical event. -/
def First (traffic : List (Message Player (CommitAttemptPacket graph)))
    (message : Message Player (CommitAttemptPacket graph)) : Prop :=
  ∀ other, Earlier traffic message other → event? other.payload ≠ event? message.payload

/-- A correctly signed FIRST commitment, tested only against earlier physical
packets. This definition does not refer to the final permission verdict. -/
def EligibleBinding (earlier : Message Player (CommitAttemptPacket graph) → Prop)
    (message : Message Player (CommitAttemptPacket graph)) (event : graph.EventId)
    (candidate : Handle graph) : Prop :=
  message.payload.packet.call = .commitment event candidate ∧
    message.payload.packet.tokenValid = true ∧
    CountCallCorrect (fun raw => ∃ prior, earlier prior ∧ prior.id.2 < message.id.2 ∧
      nativeMessage prior = raw) (nativeMessage message) ∧
    ∀ prior, earlier prior → prior.id.2 < message.id.2 →
      event? prior.payload ≠ event? message.payload

/-- A reveal names the latest eligible physical binding for its source field;
commitments voided by an earlier retry cannot authorize the surviving reveal. -/
def LatestSignedBinding (earlier : Message Player (CommitAttemptPacket graph) → Prop)
    (sender : Player) (candidate : Handle graph) : graph.Field → Prop
  | .inl input => candidate = (sender, .initial input)
  | .inr event => ∃ message, earlier message ∧ EligibleBinding earlier message event candidate ∧
      ∀ later, earlier later → ∀ handle, EligibleBinding earlier later event handle →
        later.id.2 ≤ message.id.2

/-- Only openings need the extra binding-generation disambiguation. A signed
binding packet keeps exactly the same verdict when its attempt is later voided. -/
def OpeningBinding (earlier : Message Player (CommitAttemptPacket graph) → Prop)
    (message : Message Player (CommitAttemptPacket graph)) : Prop :=
  match message.payload.packet.call with
  | .commitment .. | .malformed .. => True
  | .opening event candidate _ =>
      match nodeView graph event with
      | .resolve _ _ binding _ _ _ =>
          LatestSignedBinding earlier message.sender candidate binding.field
      | .bind .. | .sample .. => False

/-- Native well-formed content and global slot freshness, with a first-packet
allowance for each physical attempt event. Certificates may refer to surviving
bindings of earlier phases, so their signed evidence is not phase-filtered. -/
def Permits (traffic : List (Message Player (CommitAttemptPacket graph)))
    (message : Message Player (CommitAttemptPacket graph)) : Prop :=
  message.payload.packet.tokenValid = true ∧
    CountCallCorrect (EarlierOwnPacket (traffic.map nativeMessage) (nativeMessage message))
      (nativeMessage message) ∧ First traffic message ∧
      OpeningBinding (Earlier traffic message) message

open Classical in
/-- Receipt-independent count verdict for physical signed traffic. -/
def permits (traffic : List (Message Player (CommitAttemptPacket graph)))
    (message : Message Player (CommitAttemptPacket graph)) : Bool :=
  decide (Permits traffic message)

theorem permits_eq_true_iff (traffic : List (Message Player (CommitAttemptPacket graph)))
    (message : Message Player (CommitAttemptPacket graph)) :
    permits traffic message = true ↔ Permits traffic message := by
  classical
  simp only [permits, decide_eq_true_eq]

theorem permits_eq_false_iff (traffic : List (Message Player (CommitAttemptPacket graph)))
    (message : Message Player (CommitAttemptPacket graph)) :
    permits traffic message = false ↔ ¬ Permits traffic message := by
  classical
  simp only [permits, decide_eq_false_iff_not]

omit [DecidableEq Player] in
/-- Raw content comparison uses exactly the projected lower-serial own packets. -/
theorem earlier_native (traffic : List (Message Player (CommitAttemptPacket graph)))
    (message : Message Player (CommitAttemptPacket graph))
    (other : Message Player (WitnessedPacket graph)) :
    EarlierOwnPacket (traffic.map nativeMessage) (nativeMessage message) other ↔
      ∃ original, Earlier traffic message original ∧ nativeMessage original = other := by
  constructor
  · rintro ⟨member, owner, serial⟩
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact ⟨original, ⟨present, owner, serial⟩, rfl⟩
  · rintro ⟨original, ⟨present, owner, serial⟩, rfl⟩
    exact ⟨List.mem_map.mpr ⟨original, present, rfl⟩, owner, serial⟩

/-- Equal earlier signed data gives the same immutable verdict. -/
theorem permits_congr (left right : List (Message Player (CommitAttemptPacket graph)))
    (message : Message Player (CommitAttemptPacket graph))
    (same : ∀ other, Earlier left message other ↔ Earlier right message other) :
    permits left message = permits right message := by
  have earlier : Earlier left message = Earlier right message :=
    funext fun other => propext (same other)
  have native : EarlierOwnPacket (left.map nativeMessage) (nativeMessage message) =
      EarlierOwnPacket (right.map nativeMessage) (nativeMessage message) := by
    funext other
    apply propext
    simp only [earlier_native, earlier]
  rw [Bool.eq_iff_iff, permits_eq_true_iff, permits_eq_true_iff]
  unfold Permits First
  rw [native, earlier]

/-- Later signed traffic cannot alter the permission of an already signed
packet, including a packet belonging to a now voided attempt. -/
theorem permits_append_later (traffic later : List (Message Player (CommitAttemptPacket graph)))
    (message : Message Player (CommitAttemptPacket graph))
    (serials : ∀ other ∈ later, other.sender = message.sender → message.id.2 ≤ other.id.2) :
    permits (traffic ++ later) message = permits traffic message := by
  apply permits_congr
  intro other
  constructor
  · rintro ⟨member, owner, lower⟩
    rcases List.mem_append.mp member with old | new
    · exact ⟨old, owner, lower⟩
    · exact absurd lower (Nat.not_lt.mpr (serials other new owner))
  · rintro ⟨member, owner, lower⟩
    exact ⟨List.mem_append_left _ member, owner, lower⟩

theorem permits_append_self (traffic : List (Message Player (CommitAttemptPacket graph)))
    (message : Message Player (CommitAttemptPacket graph)) :
    permits (traffic ++ [message]) message = permits traffic message :=
  permits_append_later traffic [message] message fun other member _ => by
    rw [List.mem_singleton.mp member]

/-- On a count-clean prefix, every earlier signed commitment is eligible,
so the dynamic binding reference is exactly the last such own commitment. -/
theorem eligibleBinding_of_permitted
    (traffic : List (Message Player (CommitAttemptPacket graph)))
    (current message : Message Player (CommitAttemptPacket graph))
    (event : graph.EventId) (candidate : Handle graph)
    (before : Earlier traffic current message) (permitted : Permits traffic message)
    (sent : message.payload.packet.call = .commitment event candidate) :
    EligibleBinding (Earlier traffic current) message event candidate := by
  refine ⟨sent, permitted.1, ?_, ?_⟩
  · have native : (fun raw => ∃ prior, Earlier traffic current prior ∧
          prior.id.2 < message.id.2 ∧ nativeMessage prior = raw) =
        EarlierOwnPacket (traffic.map nativeMessage) (nativeMessage message) := by
      funext raw
      apply propext
      rw [earlier_native]
      constructor
      · rintro ⟨prior, older, lower, same⟩
        exact ⟨prior, ⟨older.1, older.2.1.trans before.2.1.symm, lower⟩, same⟩
      · rintro ⟨prior, older, same⟩
        exact ⟨prior, ⟨older.1, older.2.1.trans before.2.1,
          lt_trans older.2.2 before.2.2⟩, older.2.2, same⟩
    rw [native]
    exact permitted.2.1
  · intro prior older lower
    exact permitted.2.2.1 prior
      ⟨older.1, older.2.1.trans before.2.1.symm, lower⟩

theorem latestSignedBinding_iff_last_of_clean
    (traffic : List (Message Player (CommitAttemptPacket graph)))
    (current : Message Player (CommitAttemptPacket graph)) (event : graph.EventId)
    (candidate : Handle graph) (clean : ∀ message ∈ traffic, Permits traffic message) :
    LatestSignedBinding (Earlier traffic current) current.sender candidate (.inr event) ↔
      ∃ message, Earlier traffic current message ∧
        message.payload.packet.call = .commitment event candidate ∧
        ∀ later, Earlier traffic current later → ∀ handle,
          later.payload.packet.call = .commitment event handle → later.id.2 ≤ message.id.2 := by
  constructor
  · rintro ⟨message, before, eligible, latest⟩
    refine ⟨message, before, eligible.1, ?_⟩
    intro later older handle sent
    exact latest later older handle
      (eligibleBinding_of_permitted traffic current later event handle older
        (clean later older.1) sent)
  · rintro ⟨message, before, sent, latest⟩
    refine ⟨message, before, eligibleBinding_of_permitted traffic current message event
      candidate before (clean message before.1) sent, ?_⟩
    intro later older handle eligible
    exact latest later older handle eligible.1

end Vegas.EventGraphRuntime.PhaseCount
