/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseCountVerdict

/-! # Count verdict agreement when event namespaces are static

Without retries, an event has one physical namespace. On clean signed traffic,
the phase verdict's latest-binding requirement then agrees with the native
signed-binding requirement. The assumptions concern packet tags and traffic,
not a scheduler or equilibrium law.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
private theorem event_eq_iff_of_static (stamp : graph.EventId → CommitAttemptId)
    (left right : Message Player (CommitAttemptPacket graph))
    (leftTag : ∀ event, left.payload.packet.call.event? graph = some event →
      left.payload.attempt = stamp event)
    (rightTag : ∀ event, right.payload.packet.call.event? graph = some event →
      right.payload.attempt = stamp event) :
    event? left.payload = event? right.payload ↔
      left.payload.packet.call.event? graph = right.payload.packet.call.event? graph := by
  cases first : left.payload.packet.call.event? graph with
  | none =>
      cases last : right.payload.packet.call.event? graph <;>
        simp only [event?, first, last, Option.map_none, Option.map_some, reduceCtorEq]
  | some event =>
      cases last : right.payload.packet.call.event? graph with
      | none => simp only [event?, first, last, Option.map_none, Option.map_some, reduceCtorEq]
      | some other =>
          simp only [event?, first, last, Option.map_some, Option.some.injEq]
          rw [leftTag event first, rightTag other last]
          constructor
          · exact congrArg CommitAttemptEvent.event
          · intro same
            subst other
            rfl

omit [DecidableEq Player] in
/-- Static namespaces turn the physical first-packet test into the event test. -/
theorem first_iff_native_of_static (stamp : graph.EventId → CommitAttemptId)
    (traffic : List (Message Player (CommitAttemptPacket graph)))
    (message : Message Player (CommitAttemptPacket graph))
    (static : ∀ other ∈ traffic, ∀ event,
      other.payload.packet.call.event? graph = some event → other.payload.attempt = stamp event)
    (tag : ∀ event, message.payload.packet.call.event? graph = some event →
      message.payload.attempt = stamp event) :
    First traffic message ↔
      FirstForEvent (EarlierOwnPacket (traffic.map nativeMessage) (nativeMessage message))
        (nativeMessage message) := by
  constructor
  · intro first other before same
    obtain ⟨original, earlier, rfl⟩ := (earlier_native traffic message other).mp before
    exact first original earlier
      ((event_eq_iff_of_static stamp original message (static original earlier.1) tag).mpr same)
  · intro first other before same
    exact first (nativeMessage other)
      ((earlier_native traffic message (nativeMessage other)).mpr ⟨other, before, rfl⟩)
      ((event_eq_iff_of_static stamp other message (static other before.1) tag).mp same)

/-- Forgetting static attempt tags preserves every permitted packet. -/
theorem countPermits_of_permits_of_static (stamp : graph.EventId → CommitAttemptId)
    (traffic : List (Message Player (CommitAttemptPacket graph)))
    (message : Message Player (CommitAttemptPacket graph))
    (static : ∀ other ∈ traffic, ∀ event,
      other.payload.packet.call.event? graph = some event → other.payload.attempt = stamp event)
    (tag : ∀ event, message.payload.packet.call.event? graph = some event →
      message.payload.attempt = stamp event)
    (permitted : Permits traffic message) :
    CountPermits (traffic.map nativeMessage) (nativeMessage message) :=
  ⟨permitted.1, permitted.2.1,
    (first_iff_native_of_static stamp traffic message static tag).mp permitted.2.2.1⟩

private theorem openingBinding_of_countPermits_of_static
    (stamp : graph.EventId → CommitAttemptId)
    (traffic : List (Message Player (CommitAttemptPacket graph)))
    (message : Message Player (CommitAttemptPacket graph))
    (static : ∀ other ∈ traffic, ∀ event,
      other.payload.packet.call.event? graph = some event → other.payload.attempt = stamp event)
    (clean : ∀ other ∈ traffic, Permits traffic other)
    (permitted : CountPermits (traffic.map nativeMessage) (nativeMessage message)) :
    OpeningBinding (Earlier traffic message) message := by
  have correct := permitted.2.1
  cases call : message.payload.packet.call with
  | commitment event candidate => simp only [OpeningBinding, call]
  | malformed raw => simp only [OpeningBinding, call]
  | opening event candidate raw =>
      unfold CountCallCorrect at correct
      dsimp only [nativeMessage] at correct
      rw [call] at correct
      obtain ⟨_certified, resolves⟩ := correct
      unfold OpeningBinding
      rw [call]
      cases view : nodeView graph event with
      | bind owner payload outputEq codeEq | sample payload law outputEq codeEq =>
          simp only [view] at resolves
      | resolve owner payload binding checks outputEq codeEq =>
          simp only [view] at resolves ⊢
          have signed := resolves.2.2
          cases field : binding.field with
          | inl input =>
              simpa only [field, SignedBinding, LatestSignedBinding, Message.sender] using signed
          | inr producer =>
              rw [field] at signed
              obtain ⟨original, before, sent⟩ := signed
              obtain ⟨prior, earlier, rfl⟩ := (earlier_native traffic message original).mp before
              change prior.payload.packet.call = .commitment producer candidate at sent
              refine ⟨prior, earlier,
                eligibleBinding_of_permitted traffic message prior producer candidate earlier
                  (clean prior earlier.1) sent, ?_⟩
              intro later beforeLater handle eligible
              by_contra notBefore
              have lower : prior.id.2 < later.id.2 := by omega
              have nativeLater := countPermits_of_permits_of_static stamp traffic later static
                (static later beforeLater.1) (clean later beforeLater.1)
              apply nativeLater.2.2 (nativeMessage prior)
                ⟨List.mem_map.mpr ⟨prior, earlier.1, rfl⟩,
                  earlier.2.1.trans beforeLater.2.1.symm, lower⟩
              change prior.payload.packet.call.event? graph = later.payload.packet.call.event? graph
              rw [sent, eligible.1]
              rfl

/-- On clean static traffic the phase and native count verdicts coincide,
including openings' binding references. -/
theorem permits_eq_countPermits_of_static (stamp : graph.EventId → CommitAttemptId)
    (traffic : List (Message Player (CommitAttemptPacket graph)))
    (message : Message Player (CommitAttemptPacket graph))
    (static : ∀ other ∈ traffic, ∀ event,
      other.payload.packet.call.event? graph = some event → other.payload.attempt = stamp event)
    (tag : ∀ event, message.payload.packet.call.event? graph = some event →
      message.payload.attempt = stamp event)
    (clean : ∀ other ∈ traffic, Permits traffic other) :
    permits traffic message = countPermits (traffic.map nativeMessage) (nativeMessage message) := by
  rw [Bool.eq_iff_iff, permits_eq_true_iff, countPermits_eq_true_iff]
  constructor
  · exact countPermits_of_permits_of_static stamp traffic message static tag
  · intro permitted
    exact ⟨permitted.1, permitted.2.1,
      (first_iff_native_of_static stamp traffic message static tag).mpr permitted.2.2,
      openingBinding_of_countPermits_of_static stamp traffic message static clean permitted⟩

end Vegas.EventGraphRuntime.PhaseCount
