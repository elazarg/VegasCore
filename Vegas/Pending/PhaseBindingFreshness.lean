/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhasePreparedOnePacket

/-! # Every permitted phased binding uses a globally fresh prepared slot -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

theorem recalled_submission_emitted
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    {control : (phaseApplication runtime leaks).Control}
    (trace : ((phaseApplication runtime leaks).protocol initial horizon scheduler).Trace
      (some control)) (who : Player)
    (entry : (phaseApplication runtime leaks).PlayerEntry)
    (recorded : entry ∈ control.execution.recall who)
    (material : (phaseApplication runtime leaks).Submission)
    (sent : entry.action.transmission = some material) :
    ∃ message, entry.emitted = some message ∧ message.sender = who ∧
      message.payload.packet.call = material.call.packet := by
  let app := phaseApplication runtime leaks
  let property := fun execution : app.Execution => ∀ who, ∀ entry ∈ execution.recall who,
    ∀ material, entry.action.transmission = some material →
      ∃ message, entry.emitted = some message ∧ message.sender = who ∧
        message.payload.packet.call = material.call.packet
  have invariant : app.ServiceInvariant scheduler property := {
    respond := by
      intro execution actor action valid observer found member supplied sends
      simp only [ReactiveApplication.Execution.respond] at member
      split at member
      · rename_i same
        subst observer
        rcases List.mem_append.mp member with old | new
        · exact valid actor found old supplied sends
        · obtain rfl := List.mem_singleton.mp new
          rcases action with ⟨_ | submitted⟩
          · cases sends
          · cases Option.some.inj sends
            exact ⟨_, rfl, rfl, phase_emit_call _ actor _ supplied⟩
      · exact valid observer found member supplied sends
    environment := by
      intro execution next command valid _ moved observer found member supplied sends
      rw [app.environmentStep_recall execution next command moved] at member
      exact valid observer found member supplied sends }
  exact invariant.history initial horizon (by intro state _ observer found member; cases member)
    trace who entry recorded material sent

private theorem responseCandidateSlot_spec
    (response : (phaseApplication runtime leaks).Action) {serial : Nat}
    (selected : PhaseCandidates.responseCandidateSlot runtime leaks response = some serial) :
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
              | initial input =>
                  simp [PhaseCandidates.responseCandidateSlot, packet,
                    Payload.preparedCommitment?] at selected
              | prepared used =>
                  simp only [PhaseCandidates.responseCandidateSlot, packet,
                    Payload.preparedCommitment?, Option.some.injEq] at selected
                  subst used
                  exact ⟨material, event, owner, rfl, packet⟩
          | opening | malformed =>
              simp [PhaseCandidates.responseCandidateSlot, packet,
                Payload.preparedCommitment?] at selected

variable [Fintype Player] (bounds : MessageBounds graph)

/-- Arbitrary legal earlier raw responses and retired attempts cannot consume
the handle of a currently permitted binding. Preparation need not be typed. -/
theorem onePacket_binding_fresh
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    {control : (phaseApplication runtime leaks).Control}
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (who : Player) (event : graph.EventId) (serial : Nat) (preparation : Option (Raw L))
    (evidence : EvidenceRequest graph)
    (member : (⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩⟩ :
      (phaseApplication runtime leaks).Action) ∈ onePacketActions runtime leaks bounds who
        (control.execution.recall who)
        (control.execution.observe (phaseApplication runtime leaks) who)) :
    control.execution.application.current.native.candidates.lookup
      (who, .prepared serial) = .fresh := by
  let app := phaseApplication runtime leaks
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have raw := (onePacketMenu runtime leaks bounds).toRawTrace initial horizon scheduler trace
  have candidates := PhaseCandidates.candidateRecall_history runtime leaks plan inputs horizon
    scheduler raw
  have clean : CountClean runtime leaks control.execution :=
    (onePacketMenu_countClean runtime leaks bounds scheduler).history initial horizon
      (fun state _ => countClean_initial runtime leaks state) trace
  have count := clean.1
  obtain ⟨_, permitted⟩ := (mem_onePacketActions runtime leaks bounds who
    (control.execution.recall who) (control.execution.observe app who) _).mp member
  let material : WitnessedSubmission graph :=
    ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩
  let current := localEnvelope runtime leaks who (control.execution.recall who)
    (control.execution.observe app who) material
  have allowed : permits (app.outputs (control.execution.recall who)) current = true := by
    rcases permitted with impossible | ⟨supplied, sent, allowed⟩
    · cases impossible
    · cases Option.some.inj sent
      exact allowed
  have correct := ((permits_eq_true_iff _ _).mp allowed).2.1
  have currentCall : (nativeMessage current).payload.call =
      .commitment event (who, .prepared serial) := by
    change (maskPacket _ _).call = _
    unfold maskPacket
    split <;> split <;> rfl
  unfold CountCallCorrect at correct
  rw [currentCall] at correct
  apply candidates who serial
  intro used
  obtain ⟨action, actionMember, selected⟩ := List.mem_filterMap.mp used
  obtain ⟨entry, recorded, rfl⟩ := List.mem_map.mp actionMember
  obtain ⟨supplied, earlierEvent, owner, sent, packet⟩ :=
    responseCandidateSlot_spec runtime leaks entry.action selected
  obtain ⟨message, emitted, sender, call⟩ := recalled_submission_emitted runtime leaks
    initial horizon scheduler raw who entry recorded supplied sent
  have output : message ∈ app.outputs (control.execution.recall who) :=
    List.mem_filterMap.mpr ⟨entry, recorded, emitted⟩
  have input : message ∈ control.execution.network.inputs := by
    have present := output
    rw [← count.1 who] at present
    exact (List.mem_filter.mp present).1
  have previous := ((permits_eq_true_iff _ _).mp (clean.2 message input)).2.1
  have previousCall : (nativeMessage message).payload.call =
      .commitment earlierEvent (owner, .prepared serial) := call.trans packet
  unfold CountCallCorrect at previous
  rw [previousCall] at previous
  have owns : owner = who := previous.2.2.1.trans sender
  subst owner
  have earlier : EarlierOwnPacket
      ((app.outputs (control.execution.recall who)).map nativeMessage)
        (nativeMessage current) (nativeMessage message) := by
    refine ⟨List.mem_map.mpr ⟨message, output, rfl⟩, sender, ?_⟩
    change message.id.2 < app.submissionCount (control.execution.recall who)
    rw [← count.2.1 who, ← sender]
    exact count.2.2.serial_lt input
  exact correct.2.2.2.2 (nativeMessage message) earlier earlierEvent (call.trans packet)

end Vegas.EventGraphRuntime.PhaseCount
