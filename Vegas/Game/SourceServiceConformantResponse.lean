/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCanonicalSlots
import Vegas.Pending.ReactiveRiskMenu
import Vegas.Pending.EvidenceNormalization
import Interaction.ReactiveLocalContinuation
import Interaction.ReactiveSubmissionSerial

/-! # Conformant first submissions at actual service histories

Own recall and the current view reconstruct the next signed envelope, so the
send-time check that admits a conformant response to the clear risk menu is the
check of the packet actually emitted. Such a response names its owner's
current turn, is the first call for that event, and a commitment among them
uses the owner's counted prepared slot. Its private material is unrestricted.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- Legal own recall and observation reconstruct the entire actual envelope.
This uses neither a prescribed source policy nor a hidden intention table. -/
theorem localEnvelope_actual
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {control : (serviceApplication setup mode deadline leaks).Control}
    (trace : ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup
      mode) horizon scheduler).Trace
      (some control)) (who : Player) (material : (serviceApplication setup mode deadline
        leaks).Submission) :
    (serviceRuntime setup mode deadline).localEnvelope leaks who (control.execution.recall who)
      (control.execution.observe (serviceApplication setup mode deadline leaks) who) material =
      (⟨(who, control.execution.network.nextSerial who), (serviceApplication setup mode deadline
        leaks).packet
        ((serviceApplication setup mode deadline leaks).submit control.execution.application who
          material) who
          (control.execution.network.known who) material⟩ :
            Message Player (WitnessedPacket (serviceGraph setup mode))) := by
  let app := serviceApplication setup mode deadline leaks
  have input : control.execution.InputRecall app :=
    app.history_inputRecall (serviceInitialLaw setup mode) horizon scheduler trace
  have serial : control.execution.SerialRecall app :=
    app.serialRecall_history scheduler (serviceInitialLaw setup mode) horizon trace
  have known : ReactiveApplication.ResponseMenu.knownPackets (control.execution.recall who)
      (control.execution.observe app who) = control.execution.network.known who :=
    (app.known_from_recall control.execution who input).symm
  unfold EventGraphRuntime.localEnvelope
  change Message.mk (who, app.submissionCount (control.execution.recall who)) _ = _
  rw [← serial who, known]
  apply congrArg (Message.mk (who, control.execution.network.nextSerial who))
  change WitnessedPacket.mk _ _ _ = material.emit
    (app.submit control.execution.application who material) who
      (control.execution.network.known who)
  rw [WitnessedSubmission.emit_eq_resolve,
    (serviceRuntime setup mode deadline).reactiveApplication_submit_publicView leaks]
  have candidates : (fun slot => (app.submit control.execution.application who
      material).candidates.lookup (who, slot)) =
      material.call.candidateAfter who
        (control.execution.observe app who).application.candidates := by
    funext slot
    exact material.call.candidateAfter_eq who control.execution.application slot
  rw [candidates]
  rfl

/-- At an actual history, a conformant response emits a packet that passes the
public send-time check at the current public view. -/
theorem conformantResponse_actual
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {control : (serviceApplication setup mode deadline leaks).Control}
    (trace : ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup
      mode) horizon scheduler).Trace
      (some control)) (who : Player)
    (response : (serviceApplication setup mode deadline leaks).Action)
    (conformant : (serviceRuntime setup mode deadline).ConformantResponse leaks who
      (control.execution.recall who)
      (control.execution.observe (serviceApplication setup mode deadline leaks) who) response) :
    ∃ material, response.transmission = some material ∧
      (serviceRuntime setup mode deadline).firstSubmission leaks (control.execution.recall who)
        response = true ∧
      (serviceRuntime setup mode deadline).freshServiceEnvelope
        control.execution.application.publicView
        ⟨(who, control.execution.network.nextSerial who),
          (serviceApplication setup mode deadline leaks).packet
          ((serviceApplication setup mode deadline leaks).submit control.execution.application who
            material) who (control.execution.network.known who) material⟩ := by
  obtain ⟨material, sent, first, fresh⟩ := conformant
  rw [localEnvelope_actual trace who material] at fresh
  exact ⟨material, sent, first, fresh⟩

/-- A conformant response names its owner's current turn, which it has not
called before, and a conformant commitment uses the counted prepared slot of a
binding of its owner. -/
theorem conformantResponse_turn
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {control : (serviceApplication setup mode deadline leaks).Control}
    (trace : ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup
      mode) horizon scheduler).Trace
      (some control)) (who : Player)
    (response : (serviceApplication setup mode deadline leaks).Action)
    (conformant : (serviceRuntime setup mode deadline).ConformantResponse leaks who
      (control.execution.recall who)
      (control.execution.observe (serviceApplication setup mode deadline leaks) who) response) :
    ∃ event, (serviceRuntime setup mode deadline).submittedEvent? leaks response = some event ∧
      control.execution.application.publicView.ownTurn? who = some event ∧
      (serviceGraph setup mode).actor? event = some who ∧
      control.execution.application.config.cut.Ready event ∧
      (serviceRuntime setup mode deadline).eventRecorded leaks (control.execution.recall who)
        event = false ∧
      ∀ serial, (serviceRuntime setup mode deadline).responseCandidateSlot leaks response =
          some serial →
        serial = control.execution.application.publicView.bindingCount who ∧
          ∃ payload, (serviceGraph setup mode).outputLayout event = .binding who payload := by
  obtain ⟨material, sent, first, fresh⟩ := conformantResponse_actual trace who response conformant
  obtain ⟨event, named, ready, owned⟩ :=
    (serviceRuntime setup mode deadline).freshServiceEnvelope_owned _ _ fresh
  change material.call.packet.event? (serviceGraph setup mode) = some event at named
  have submitted : (serviceRuntime setup mode deadline).submittedEvent? leaks response =
      some event := by
    simp only [EventGraphRuntime.submittedEvent?, sent, named]
  have readyCut := (control.execution.application.publicView_eventReady event).mp ready
  have unrecorded : (serviceRuntime setup mode deadline).eventRecorded leaks
      (control.execution.recall who) event = false := by
    simpa only [EventGraphRuntime.firstSubmission, submitted, Bool.not_eq_true_eq_eq_false]
      using first
  refine ⟨event, submitted, serviceOwnTurn?_of_ready setup _ readyCut owned, owned, readyCut,
    unrecorded, fun serial slot => ?_⟩
  simp only [EventGraphRuntime.responseCandidateSlot, sent] at slot
  cases node : nodeView (serviceGraph setup mode) event with
  | bind owner payload outputEq codeEq =>
      obtain ⟨authored, shape⟩ :=
        (serviceRuntime setup mode deadline).freshServiceEnvelope_binding_shape _ owner event
          payload outputEq codeEq node _ named fresh
      change who = owner at authored
      subst owner
      have call := congrArg WitnessedPacket.call shape
      change material.call.packet = _ at call
      rw [call] at slot
      simp only [Payload.preparedCommitment?, Option.some.injEq] at slot
      exact ⟨slot.symm, payload, outputEq⟩
  | resolve owner payload binding checks outputEq codeEq =>
      obtain ⟨candidate, raw, _, _, _, _, shape, _⟩ :=
        (serviceRuntime setup mode deadline).freshServiceEnvelope_resolution_shape _ owner event
          payload binding checks outputEq codeEq node _ named fresh
      have call := congrArg WitnessedPacket.call shape
      change material.call.packet = _ at call
      rw [call] at slot
      simp only [Payload.preparedCommitment?, reduceCtorEq] at slot
  | sample payload law outputEq codeEq =>
      have none := nodeView_sample_actor outputEq codeEq
      rw [owned] at none
      cases none

end Vegas
