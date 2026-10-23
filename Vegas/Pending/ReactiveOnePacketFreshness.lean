/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveOnePacketMenu
import Vegas.Pending.ReactiveSignedCommitments

/-! # Fresh prepared slots in the one-packet game

Every nonfresh prepared candidate originates in an earlier own commitment.
The count verdict forbids reusing such a candidate, so every admitted binding
response names a currently fresh slot, under arbitrary scheduling and delays.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

private theorem recalled_submission_emitted
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    {control : (runtime.reactiveApplication leaks).Control}
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) (who : Player)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (recorded : entry ∈ control.execution.recall who)
    (material : (runtime.reactiveApplication leaks).Submission)
    (sent : entry.action.transmission = some material) :
    ∃ message, entry.emitted = some message ∧ message.sender = who ∧
      message.payload.call = material.call.packet := by
  let app := runtime.reactiveApplication leaks
  let property := fun execution : app.Execution => ∀ who, ∀ entry ∈ execution.recall who,
    ∀ material, entry.action.transmission = some material →
      ∃ message, entry.emitted = some message ∧ message.sender = who ∧
        message.payload.call = material.call.packet
  have invariant : app.ServiceInvariant scheduler property := {
    respond := by
      intro execution actor action valid observer found member supplied sends
      rw [respond_recall] at member
      split at member
      · rename_i same
        subst observer
        rcases List.mem_append.mp member with old | new
        · exact valid actor found old supplied sends
        · obtain rfl := List.mem_singleton.mp new
          rcases action with ⟨_ | submitted⟩
          · cases sends
          · cases Option.some.inj sends
            exact ⟨_, rfl, rfl, rfl⟩
      · exact valid observer found member supplied sends
    environment := by
      intro execution next command valid _ moved observer found member supplied sends
      rw [app.environmentStep_recall execution next command moved] at member
      exact valid observer found member supplied sends }
  exact invariant.history initial horizon (by intro state _ observer found member; cases member)
    trace who entry recorded material sent

private theorem responseCandidateSlot_spec
    (response : (runtime.reactiveApplication leaks).Action) {serial : Nat}
    (selected : runtime.responseCandidateSlot leaks response = some serial) :
    ∃ material event owner, response.transmission = some material ∧
      material.call.packet = .commitment event (owner, .prepared serial) := by
  cases response with
  | mk transmission =>
      cases transmission with
      | none => cases selected
      | some material =>
          cases packet : material.call.packet with
          | commitment event candidate =>
              rcases candidate with ⟨owner, slot⟩
              cases slot with
              | initial input => simp [responseCandidateSlot, packet,
                  Payload.preparedCommitment?] at selected
              | prepared used =>
                  simp only [responseCandidateSlot, packet, Payload.preparedCommitment?,
                    Option.some.injEq] at selected
                  subst used
                  exact ⟨material, event, owner, rfl, packet⟩
          | opening | malformed =>
              simp [responseCandidateSlot, packet, Payload.preparedCommitment?] at selected

variable [Fintype Player] (bounds : MessageBounds graph)

/-- At every actual one-packet input, an admitted commitment to an owned
prepared handle names a currently fresh candidate, even before inclusion. -/
theorem MessageBounds.onePacket_binding_fresh
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    {control : (runtime.reactiveApplication leaks).Control}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (inputs.map State.initial) horizon
      scheduler).Trace (some control))
    (who : Player) (event : graph.EventId) (serial : Nat) (opening : Option (Raw L))
    (member : (⟨some ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩⟩ :
      (runtime.reactiveApplication leaks).Action) ∈ bounds.onePacketActions runtime leaks who
        (control.execution.recall who)
        (control.execution.observe (runtime.reactiveApplication leaks) who)) :
    control.execution.application.candidates.lookup (who, .prepared serial) = .fresh := by
  let app := runtime.reactiveApplication leaks
  have rawTrace := (bounds.onePacketMenu runtime leaks).toRawTrace (inputs.map State.initial)
    horizon scheduler trace
  have candidates : runtime.CandidateRecall leaks control.execution :=
    runtime.candidateRecall_history leaks inputs horizon scheduler rawTrace
  have clean : runtime.CountClean leaks control.execution :=
    (bounds.onePacketMenu_countClean runtime leaks scheduler).history (inputs.map State.initial)
      horizon (fun state _ => runtime.countClean_initial leaks state) trace
  have count := clean.1
  obtain ⟨_, permitted⟩ := (bounds.mem_onePacketActions runtime leaks who
    (control.execution.recall who) (control.execution.observe app who) _).mp member
  have current : countPermits (app.outputs (control.execution.recall who))
      (runtime.localEnvelope leaks who (control.execution.recall who)
        (control.execution.observe app who)
        ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩) = true := by
    rcases permitted with impossible | ⟨material, sent, permits⟩
    · cases impossible
    · cases Option.some.inj sent
      exact permits
  have correct := ((countPermits_eq_true_iff _ _).mp current).2.1
  apply candidates who serial
  intro used
  obtain ⟨action, actionMember, selected⟩ := List.mem_filterMap.mp used
  obtain ⟨entry, recorded, rfl⟩ := List.mem_map.mp actionMember
  obtain ⟨material, earlierEvent, owner, sent, packet⟩ :=
    responseCandidateSlot_spec runtime leaks entry.action selected
  obtain ⟨message, emitted, sender, call⟩ := recalled_submission_emitted runtime leaks
    (inputs.map State.initial) horizon scheduler rawTrace who entry recorded material sent
  have output : message ∈ app.outputs (control.execution.recall who) :=
    List.mem_filterMap.mpr ⟨entry, recorded, emitted⟩
  have input : message ∈ control.execution.network.inputs := by
    have present := output
    rw [← count.1 who] at present
    exact (List.mem_filter.mp present).1
  have previous := ((countPermits_eq_true_iff _ _).mp (clean.2 message input)).2.1
  unfold CountCallCorrect at previous
  rw [call, packet] at previous
  have owns : owner = who := previous.2.2.1.trans sender
  subst owner
  have earlier : EarlierOwnPacket (app.outputs (control.execution.recall who))
      (runtime.localEnvelope leaks who (control.execution.recall who)
        (control.execution.observe app who)
        ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩) message := by
    refine ⟨output, sender, ?_⟩
    change message.id.2 < app.submissionCount (control.execution.recall who)
    rw [← count.2.1 who, ← sender]
    exact count.2.2.serial_lt input
  exact correct.2.2.2.2 message earlier earlierEvent (call.trans packet)

end Vegas.EventGraphRuntime
