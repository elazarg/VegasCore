/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseBindingStampHistory
import Vegas.Pending.PhaseCurrentPackets

/-! # The surviving handle is the latest signed binding

A permitted response cannot supersede a currently accepted binding: saved
fields are outside the active phase, and a live association already has its
unique first packet in the current namespace. Normalization copies saved or
live tables without deleting the physical traffic used by the count verdict.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Every accepted event association is the latest own signed commitment to
that static field in the full permanent physical input list. -/
def LatestBindingTable (traffic : List (Message Player (CommitAttemptPacket graph)))
    (state : State graph) : Prop :=
  ∀ event candidate, state.accepted (.inr event) = some candidate →
    ∃ message ∈ traffic, message.sender = candidate.1 ∧
      message.payload.packet.call = .commitment event candidate ∧
      ∀ later ∈ traffic, later.sender = message.sender → ∀ handle,
        later.payload.packet.call = .commitment event handle → later.id.2 ≤ message.id.2

namespace LatestBindingTable

variable {traffic : List (Message Player (CommitAttemptPacket graph))}

omit [DecidableEq Player] in
theorem copy {before after : State graph} (valid : LatestBindingTable traffic before)
    (accepted : after.accepted = before.accepted) : LatestBindingTable traffic after := by
  simpa only [LatestBindingTable, accepted] using valid

omit [DecidableEq Player] in
theorem append {state : State graph} (valid : LatestBindingTable traffic state)
    (message : Message Player (CommitAttemptPacket graph))
    (forbidden : ∀ event candidate, state.accepted (.inr event) = some candidate →
      message.sender = candidate.1 → ∀ handle,
        message.payload.packet.call ≠ .commitment event handle) :
    LatestBindingTable (traffic ++ [message]) state := by
  intro event candidate accepted
  obtain ⟨original, member, sender, call, latest⟩ := valid event candidate accepted
  refine ⟨original, List.mem_append_left _ member, sender, call, ?_⟩
  intro later present same handle sent
  rcases List.mem_append.mp present with earlier | newer
  · exact latest later earlier same handle sent
  · rw [List.mem_singleton.mp newer] at same sent ⊢
    exact (forbidden event candidate accepted (same.trans sender) handle sent).elim

end LatestBindingTable

namespace PhaseRuntimeState

/-- Retirement changes semantic associations but never the physical traffic
against which surviving signed origins are compared. -/
theorem settle_latestBindings (traffic : List (Message Player (CommitAttemptPacket graph)))
    (phases : List (RuntimePhase graph)) (generation : Nat) (entry current : RecoveryState graph)
    (retired : List (RetiredCommitAttempt graph))
    (saved : LatestBindingTable traffic entry.native)
    (active : LatestBindingTable traffic current.native) :
    LatestBindingTable traffic (settle phases generation entry current retired).entry.native ∧
      LatestBindingTable traffic
        (settle phases generation entry current retired).current.native := by
  induction phases generalizing generation entry current retired with
  | nil => exact ⟨saved, active⟩
  | cons phase rest ih =>
      have drained := active.copy (phase.drain_tables current).1
      have rebuilt := saved.copy (phase.drain_tables (restore entry (phase.drain current))).1
      simp only [settle]
      split
      · split
        · split
          · exact ⟨saved, rebuilt⟩
          · exact ih _ _ _ _ rebuilt rebuilt
        · exact ih _ _ _ _ drained drained
      · exact ⟨saved, drained⟩

end PhaseRuntimeState

namespace PhaseCount

/-- A phase-masked packet can have a valid token only for the active interval. -/
theorem maskPacket_valid_allows (view : PhasePublicView graph) (packet : WitnessedPacket graph)
    (valid : (maskPacket view packet).tokenValid = true) : allows view packet.call = true := by
  cases allowed : allows view packet.call with
  | true => rfl
  | false =>
      simp only [maskPacket, allowed, Bool.false_eq_true, ↓reduceIte,
        WitnessedPacket.tokenValid_none] at valid

theorem maskPacket_call (view : PhasePublicView graph) (packet : WitnessedPacket graph) :
    (maskPacket view packet).call = packet.call := by
  unfold maskPacket
  split <;> split <;> rfl

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A genuine permitted new response cannot replace any currently accepted
association whose saved/live attempt origin is known. -/
theorem response_ne_accepted_binding (execution : (app).Execution)
    (clean : CountClean runtime leaks execution) (who : Player) (material : (app).Submission)
    (nextClean : CountClean runtime leaks (execution.respond (app) who ⟨some material⟩))
    (native : State graph)
    (stamped : BindingStamp (fun owner => (app).outputs (execution.recall owner))
      execution.application.attempt native)
    (event : graph.EventId) (candidate : Handle graph)
    (installed : native.accepted (.inr event) = some candidate) (sender : who = candidate.1)
    (handle : Handle graph) :
    (localEnvelope runtime leaks who (execution.recall who)
      (execution.observe (app) who) material).payload.packet.call ≠ .commitment event handle := by
  let message := localEnvelope runtime leaks who (execution.recall who)
    (execution.observe (app) who) material
  obtain ⟨inputs, verdict, unchanged⟩ :=
    permits_respond runtime leaks execution clean.1 who material
  have present : message ∈ (execution.respond (app) who ⟨some material⟩).network.inputs := by
    rw [inputs]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have allowed := (permits_eq_true_iff _ _).mp (nextClean.2 message present)
  intro sent
  change message.payload.packet.call = .commitment event handle at sent
  have interval : allows execution.application.publicView material.call.packet = true := by
    apply maskPacket_valid_allows _ _ allowed.1
  have packetCall : message.payload.packet.call = material.call.packet :=
    maskPacket_call _ _
  have materialCall : material.call.packet = .commitment event handle := packetCall.symm.trans sent
  have inside : execution.application.allows (.commitment event handle) = true := by
    rw [materialCall] at interval
    exact (allows_publicView execution.application _).symm.trans interval
  obtain ⟨phase, head, named, address, within⟩ :=
    PhaseRuntimeState.allows_event execution.application _ inside
  have namedEq : named = event := by
    exact Option.some.inj address.symm
  subst named
  have headEq : execution.application.phases.head? = some phase := head
  have low : execution.application.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, headEq, Option.map_some, Option.getD_some]
  rcases stamped event candidate installed with previous |
    ⟨original, output, originalSender, originalCall, current⟩
  · have lower := ((phase.mem_events event).mp within).1
    omega
  · have originalInput : original ∈ execution.network.inputs := by
      change original ∈ (app).outputs (execution.recall candidate.1) at output
      rw [← clean.1.1 candidate.1] at output
      exact (List.mem_filter.mp output).1
    have originalEarlier : Earlier (execution.respond (app) who ⟨some material⟩).network.inputs
        message original := by
      refine ⟨?_, ?_, ?_⟩
      · rw [inputs]
        exact List.mem_append_left _ originalInput
      · exact originalSender.trans sender.symm
      · have before := clean.1.2.2.serial_lt originalInput
        have serial : message.id.2 = execution.network.nextSerial who :=
          (clean.1.2.1 who).symm
        rw [serial]
        rw [originalSender, ← sender] at before
        exact before
    have sameAttempt : message.payload.attempt = execution.application.attempt := rfl
    have sameEvent : event? original.payload = event? message.payload := by
      simp only [event?, originalCall, sent, Payload.event?, Option.map_some, current, sameAttempt]
    exact allowed.2.2.1 original originalEarlier sameEvent

end PhaseCount

end Vegas.EventGraphRuntime
