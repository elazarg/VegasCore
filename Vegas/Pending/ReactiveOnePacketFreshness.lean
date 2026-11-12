module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveOnePacketMenu
public import Vegas.Pending.ReactiveSignedCommitments

@[expose] public section

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
  (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

private theorem recalled_submission_emitted
    (initial : PMF ((reactiveApplication timeouts) leaks).State) (horizon : Nat)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    {control : ((reactiveApplication timeouts) leaks).Control}
    (trace : (((reactiveApplication timeouts) leaks).protocol initial horizon scheduler).Trace
      (some control)) (who : Player)
    (entry : ((reactiveApplication timeouts) leaks).PlayerEntry)
    (recorded : entry ∈ control.execution.logs who)
    (material : ((reactiveApplication timeouts) leaks).Submission)
    (sent : entry.action.transmission = some material) :
    ∃ message, entry.emitted = some message ∧ message.sender = who ∧
      message.payload.call = material.call.packet := by
  let app := (reactiveApplication timeouts) leaks
  let property := fun execution : app.Execution => ∀ who, ∀ entry ∈ execution.logs who,
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
    (response : ((reactiveApplication timeouts) leaks).Action) {serial : Nat}
    (selected : (responseCandidateSlot timeouts) leaks response = some serial) :
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

/-- At an actual one-packet history, the count verdict permits a commitment
only at a currently fresh prepared candidate, independently of response bounds. -/
theorem MessageBounds.onePacket_permitted_binding_fresh
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    {control : ((reactiveApplication timeouts) leaks).Control}
    (trace : ((bounds.onePacketMenu timeouts leaks).protocol (inputs.map State.initial) horizon
      scheduler).Trace (some control))
    (who : Player) (event : graph.EventId) (serial : Nat) (opening : Option (Raw L))
    (permitted : countPermits
      (((reactiveApplication timeouts) leaks).outputs (control.execution.logs who))
      ((localEnvelope timeouts) leaks who (control.execution.logs who)
        (control.execution.observe ((reactiveApplication timeouts) leaks) who)
        ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩) = true) :
    control.execution.application.candidates.lookup (who, .prepared serial) = .fresh := by
  let app := (reactiveApplication timeouts) leaks
  have rawTrace := (bounds.onePacketMenu timeouts leaks).toRawTrace (inputs.map State.initial)
    horizon scheduler trace
  have candidates : (CandidateRecall timeouts) leaks control.execution :=
    (candidateRecall_history timeouts) leaks inputs horizon scheduler rawTrace
  have clean : (CountClean timeouts) leaks control.execution :=
    (bounds.onePacketMenu_countClean timeouts leaks scheduler).history (inputs.map State.initial)
      horizon (fun state _ => (countClean_initial timeouts) leaks state) trace
  have count := clean.1
  have correct := ((countPermits_eq_true_iff _ _).mp permitted).2.1
  apply candidates who serial
  intro used
  obtain ⟨action, actionMember, selected⟩ := List.mem_filterMap.mp used
  obtain ⟨entry, recorded, rfl⟩ := List.mem_map.mp actionMember
  obtain ⟨material, earlierEvent, owner, sent, packet⟩ :=
    responseCandidateSlot_spec timeouts leaks entry.action selected
  obtain ⟨message, emitted, sender, call⟩ := recalled_submission_emitted timeouts leaks
    (inputs.map State.initial) horizon scheduler rawTrace who entry recorded material sent
  have output : message ∈ app.outputs (control.execution.logs who) :=
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
  have earlier : EarlierOwnPacket (app.outputs (control.execution.logs who))
      ((localEnvelope timeouts) leaks who (control.execution.logs who)
        (control.execution.observe app who)
        ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩) message := by
    refine ⟨output, sender, ?_⟩
    change message.id.2 < app.submissionCount (control.execution.logs who)
    rw [← count.2.1 who, ← sender]
    exact count.2.2.serial_lt input
  exact correct.2.2.2.2 message earlier earlierEvent (call.trans packet)

/-- At every actual one-packet input, an admitted commitment to an owned
prepared handle names a currently fresh candidate, even before inclusion. -/
theorem MessageBounds.onePacket_binding_fresh
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    {control : ((reactiveApplication timeouts) leaks).Control}
    (trace : ((bounds.onePacketMenu timeouts leaks).protocol (inputs.map State.initial) horizon
      scheduler).Trace (some control))
    (who : Player) (event : graph.EventId) (serial : Nat) (opening : Option (Raw L))
    (member : (⟨some ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩⟩ :
      ((reactiveApplication timeouts) leaks).Action) ∈ bounds.onePacketActions timeouts leaks who
        (control.execution.logs who)
        (control.execution.observe ((reactiveApplication timeouts) leaks) who)) :
    control.execution.application.candidates.lookup (who, .prepared serial) = .fresh := by
  obtain ⟨_, permitted⟩ := (bounds.mem_onePacketActions timeouts leaks who
    (control.execution.logs who)
    (control.execution.observe ((reactiveApplication timeouts) leaks) who) _).mp member
  apply bounds.onePacket_permitted_binding_fresh timeouts leaks inputs horizon scheduler trace
    who event serial opening
  rcases permitted with impossible | ⟨material, sent, permits⟩
  · cases impossible
  · cases Option.some.inj sent
    exact permits

end Vegas.EventGraphRuntime
