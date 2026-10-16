/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCommitWordRecall

/-! # Actual accepted-word provenance from concrete callback response laws -/

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
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
  (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
  (who : Player) (word : DecisionView who Δ)

local notation "app" => phaseApplication runtime leaks

/-- The genuine earlier callback and its typed reply determine each surviving
accepted binding. The response hypothesis is a local packet-shape property;
all actual prefix, request, provenance and accepted-result facts are derived. -/
theorem phaseCommitWordRecall_accepted_of_response
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler)
    (policy : (app).Policy)
    (covered : ∀ past view response, response ∈ (policy past view).support →
      response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view)
    (responds : ∀ (remaining : Nat) (execution : (app).Execution),
      ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
          (some ⟨remaining, some who, execution⟩) →
      execution.application.current.excluded = ∅ →
      ∀ (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
        (binding : (serviceGraph setup mode).outputLayout event = .binding who payload),
      execution.application.SeedRequest who ⟨execution.application.attempt, event⟩ →
      (low ≤ event.val ∧ event.val < low + block.length) →
      execution.application.attempt = ⟨low, generation⟩ →
      ∀ response ∈ (policy (execution.recall who) (execution.observe (app) who)).support,
        response ≠ ⟨none⟩ →
        ∃ serial, response = phaseBindingResponse runtime leaks who event payload
          (phaseRecoveryBindingData setup mode event who payload binding
            (CommitRecoveryMove.lift (block.wordAction who (event.val - low) word))).1 serial)
    {control : (app).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (inside : low ≤ event.val ∧ event.val < low + block.length)
    (address : control.execution.application.attempt = ⟨low, generation⟩)
    (candidate : Handle (serviceGraph setup mode))
    (accepted : control.execution.application.current.native.accepted (.inr event) =
      some candidate)
    (consistent : policy.Consistent (control.execution.recall who)) :
    let result := (phaseRecoveryBindingData setup mode event who payload binding
      (CommitRecoveryMove.lift (block.wordAction who (event.val - low) word))).1
    ∃ (entry : (app).PlayerEntry) (serial : Nat),
      entry ∈ control.execution.recall who ∧
      entry.beforeView.application.2.attempt = ⟨low, generation⟩ ∧
      entry.action = phaseBindingResponse runtime leaks who event payload result serial ∧
      candidate = (who, .prepared serial) ∧
      control.execution.application.current.native.bindingResult candidate payload = result ∧
      phaseBindingAction? setup.program mode runtime leaks entry.action =
        decodeEventAction setup.program event
          (cast (congrArg EventField.Action binding.symm) result) := by
  classical
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have raw := menu.toRawTrace initial horizon scheduler trace
  have bindings := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler raw
  have stamped := phaseLiveBindingStamp_history runtime leaks plan inputs horizon scheduler raw
  obtain ⟨actualPayload, typed⟩ := bindings.active.accepted_typed (.inr event) candidate accepted
  have owner : candidate.1 = who := (EventField.binding.inj (typed.symm.trans binding)).1
  have memberConsistent : policy.Consistent (control.execution.recall candidate.1) := by
    rw [owner]
    exact consistent
  have lower : control.execution.application.attempt.phase ≤ event.val := by
    rw [address]
    exact inside.1
  obtain ⟨message, entry, material, before, prior, _sender, _tag, _call, retained, _emitted,
    transmitted, materialCall, isPrefix, sameAttempt, acting, viewed, supported, _after,
      _samePast⟩ :=
    phase_binding_response_origin_of_stamp runtime leaks bounds plan inputs horizon scheduler
      trace control.execution.application.current.native stamped event candidate accepted lower
        policy memberConsistent
  rw [owner] at retained acting viewed supported
  have beforeClear := (phase_clear_nativeProgress_of_prefix runtime leaks menu initial horizon
    scheduler before control prior trace isPrefix clear).1
  have offered := covered (before.execution.recall who)
    (before.execution.observe (app) who) entry.action supported
  have actionEq : entry.action = ⟨some material⟩ := by
    cases actionAt : entry.action with
    | mk transmission =>
        have materialEq : transmission = some material := by
          simpa only [actionAt] using transmitted
        cases materialEq
        rfl
  have priorActive : (menu.protocol initial horizon scheduler).Trace
      (some ⟨before.remaining, some who, before.execution⟩) := by
    simpa only [← acting] using prior
  rw [actionEq] at offered
  obtain ⟨coordinate, request⟩ := PhaseCount.onePacket_request_of_nonsilent runtime leaks bounds
    plan inputs horizon scheduler before.remaining who before.execution priorActive beforeClear
      material offered
  have named := PhaseCount.onePacket_event_of_request runtime leaks bounds plan
    (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler before.remaining who
      before.execution priorActive coordinate request material offered
  rw [materialCall] at named
  have eventEq : coordinate.event = event := (Option.some.inj named).symm
  have actualRequest : before.execution.application.SeedRequest who
      ⟨before.execution.application.attempt, event⟩ := by
    have coordinateEq : coordinate = ⟨before.execution.application.attempt, event⟩ :=
      by
        cases coordinate with
        | mk tag selected =>
            have tagEq := request.1
            cases tagEq
            cases eventEq
            rfl
    rwa [coordinateEq] at request
  have beforeAddress := sameAttempt.trans address
  obtain ⟨serial, declared⟩ := responds before.remaining before.execution priorActive
    beforeClear event payload binding actualRequest inside beforeAddress entry.action supported
      (by intro silent; rw [silent] at transmitted; cases transmitted)
  have sameMaterial : (phaseBindingResponse runtime leaks who event payload _
      serial).transmission = some material := declared ▸ transmitted
  have exactCall := (congrArg (fun submitted : WitnessedSubmission (serviceGraph setup mode) =>
    submitted.call.packet) (Option.some.inj sameMaterial)).trans materialCall
  have handleEq : candidate = (who, .prepared serial) :=
    (Payload.commitment.inj exactCall).2.symm
  have fresh := phaseBindingRecall_fresh setup.program mode runtime leaks bounds plan inputs
    horizon scheduler trace who event payload _ serial entry retained declared
  refine ⟨entry, serial, retained, ?_, declared, handleEq, ?_, ?_⟩
  · rw [viewed]
    exact beforeAddress
  · rw [handleEq]
    exact PhaseNativeProjection.recorded_binding_result_of_clear runtime leaks plan bounds
      (serviceGraph_revealRelaxedOrdered setup mode) maximal inputs horizon scheduler trace
        clear who event payload _ serial entry retained declared fresh
  · rw [declared]
    exact phaseBindingAction?_response setup.program mode runtime leaks who event payload binding
      _ serial

end Vegas
