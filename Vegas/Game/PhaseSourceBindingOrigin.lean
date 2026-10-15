/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseSourcePolicy
import Vegas.Pending.PhaseBindingResponseOrigin
import Vegas.Pending.PhaseRecordedBindingMeaning
import Vegas.Pending.PhaseNativeInvariant
import Vegas.Pending.PhaseClearTraceProgress

/-! # The original auxiliary source draw of an actual accepted binding -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks

private theorem binding_policy_transmitted_choice (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment) (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) (response : (app).Action)
    (supported : response ∈ (phaseRecoveryBindingPolicy setup mode runtime leaks bounds wellFormed
      assessment who event payload binding past view).support)
    (material : WitnessedSubmission (serviceGraph setup mode))
    (transmitted : response.transmission = some material) :
    ∃ serial, ∃ choice : setup.commitRecoveryModel.Choice who
        (setup.commitRecoveryClearInformation wellFormed who
          (phaseSourceView? setup mode runtime leaks who event view)),
      reactiveFreshSlot view.application.1 = some serial ∧
      choice ∈ (assessment.strategy who (setup.commitRecoveryClearInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event view))).support ∧
      (phaseRecoveryBindingData setup mode event who payload binding choice.1).2 = false ∧
      response = phaseBindingResponse runtime leaks who event payload
        (phaseRecoveryBindingData setup mode event who payload binding choice.1).1 serial := by
  unfold phaseRecoveryBindingPolicy at supported
  split at supported
  · cases (PMF.mem_support_pure_iff _ _).mp supported
    cases transmitted
  · rename_i serial selected
    split at supported
    · dsimp only [phaseRecoveryBindingLaw] at supported
      obtain ⟨choice, chosen, equal⟩ := PMF.support_map .. ▸ supported
      have missing : (phaseRecoveryBindingData setup mode event who payload binding
          choice.1).2 = false := by
        cases value : (phaseRecoveryBindingData setup mode event who payload binding
            choice.1).2 with
        | false => rfl
        | true =>
            rw [← equal] at transmitted
            dsimp only at transmitted
            simp only [phaseRecoveryBindingResponse, value, ↓reduceIte] at transmitted
            cases transmitted
      refine ⟨serial, choice, selected, chosen, missing, ?_⟩
      rw [← equal]
      simp only [phaseRecoveryBindingResponse, missing, Bool.false_eq_true, ↓reduceIte]
    · cases (PMF.mem_support_pure_iff _ _).mp supported
      cases transmitted

/-- An actual surviving current-phase accepted binding retains the very source
draw used at its genuine earlier ready callback. Its immutable typed result,
fresh physical slot and full actual history prefix are derived together. -/
theorem phase_accepted_binding_source_choice
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) {control : (app).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (candidate : Handle (serviceGraph setup mode))
    (accepted : control.execution.application.current.native.accepted (.inr event) =
      some candidate)
    (phase : RuntimePhase (serviceGraph setup mode))
    (installed : control.execution.application.phases.head? = some phase)
    (inside : event ∈ phase.events)
    (consistent : (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment
      who).Consistent (control.execution.recall who)) :
    ∃ (before : (app).Control)
      (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some before))
      (entry : (app).PlayerEntry) (serial : Nat)
      (choice : setup.commitRecoveryModel.Choice who
        (setup.commitRecoveryClearInformation wellFormed who
          (phaseSourceView? setup mode runtime leaks who event
            (before.execution.observe (app) who)))),
      TracePrefix prior trace ∧ before.actor = some who ∧
      before.execution.application.current.excluded = ∅ ∧
      before.execution.application.SeedRequest who
        ⟨before.execution.application.attempt, event⟩ ∧
      entry ∈ control.execution.recall who ∧
      entry.beforeView = before.execution.observe (app) who ∧
      reactiveFreshSlot entry.beforeView.application.1 = some serial ∧
      choice ∈ (assessment.strategy who (setup.commitRecoveryClearInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event
          (before.execution.observe (app) who)))).support ∧
      (phaseRecoveryBindingData setup mode event who payload binding choice.1).2 = false ∧
      entry.action = phaseBindingResponse runtime leaks who event payload
        (phaseRecoveryBindingData setup mode event who payload binding choice.1).1 serial ∧
      candidate = (who, .prepared serial) ∧
      control.execution.application.current.native.bindingResult candidate payload =
        (phaseRecoveryBindingData setup mode event who payload binding choice.1).1 := by
  have rawCurrent := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon
    scheduler trace
  have bindings := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler rawCurrent
  obtain ⟨actualPayload, typed⟩ := bindings.active.accepted_typed (.inr event) candidate accepted
  have owner : candidate.1 = who := (EventField.binding.inj (typed.symm.trans binding)).1
  have focal : (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment
      who).Consistent (control.execution.recall candidate.1) := by rw [owner]; exact consistent
  obtain ⟨message, entry, material, before, prior, _sender, _attempt, _call, retained, _emitted,
    transmitted, materialCall, retainedTrace, acting, viewed, supported, _suffix, _samePast⟩ :=
    phase_accepted_binding_response_origin runtime leaks bounds plan inputs horizon scheduler
      trace event candidate accepted phase installed inside
        (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment who) focal
  rw [owner] at retained acting viewed supported
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler prior
  obtain ⟨_draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    scheduler raw
  have request := phaseSourcePolicy_request_of_binding_support setup mode runtime leaks bounds
    wellFormed assessment before.execution valid who entry.action supported material transmitted
      event candidate materialCall
  have branch := phaseSourcePolicy_binding setup mode runtime leaks bounds wellFormed assessment
    before.execution valid who event payload binding request
  rw [branch] at supported
  obtain ⟨serial, choice, selected, chosen, missing, declared⟩ := binding_policy_transmitted_choice
    setup mode runtime leaks bounds wellFormed assessment who event payload binding
      (before.execution.recall who) (before.execution.observe (app) who) entry.action supported
        material transmitted
  have fresh : reactiveFreshSlot entry.beforeView.application.1 = some serial := by
    rw [viewed]
    exact selected
  have sameMaterial : (phaseBindingResponse runtime leaks who event payload
      (phaseRecoveryBindingData setup mode event who payload binding choice.1).1
        serial).transmission = some material := declared ▸ transmitted
  have exactCall := (congrArg (fun submitted : WitnessedSubmission (serviceGraph setup mode) =>
    submitted.call.packet) (Option.some.inj sameMaterial)).trans materialCall
  have handleEq : candidate = (who, .prepared serial) :=
    (Payload.commitment.inj exactCall).2.symm
  have beforeClear := (phase_clear_nativeProgress_of_prefix runtime leaks
    (PhaseCount.onePacketMenu runtime leaks bounds) _ horizon scheduler before control prior
      trace retainedTrace clear).1
  refine ⟨before, prior, entry, serial, choice, retainedTrace, acting, beforeClear, request,
    retained, viewed, fresh, chosen, missing, declared, handleEq, ?_⟩
  rw [handleEq]
  exact PhaseNativeProjection.recorded_binding_result_of_clear runtime leaks plan bounds
    (serviceGraph_revealRelaxedOrdered setup mode) maximal inputs horizon scheduler trace clear
      who event payload _ serial entry retained declared (reactiveFreshSlot_spec _ serial fresh)

end Vegas
