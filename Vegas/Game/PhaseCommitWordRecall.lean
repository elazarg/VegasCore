/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseBindingRecallMeaning
import Vegas.Game.PhaseCommitWordPolicy
import Vegas.Pending.PhaseBindingResponseOrigin
import Vegas.Pending.PhaseBindingIdleMenu
import Vegas.Pending.PhaseBindingResponseWitness
import Vegas.Pending.PhaseClearTraceProgress
import Vegas.Pending.PhaseNativeInvariant
import Interaction.ReactiveMixtureRecall

/-! # Surviving bindings constrain the actual owned-word member

An accepted current-block handle is traced to its authentic earlier callback.
The legal callback and public address select the concrete member channel, so
the action in raw recall reads that member's typed word at the actual event.
-/

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
  (wellFormed : setup.WellFormed)
  (assessment : setup.commitRecoveryModel.BehavioralAssessment)
  (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (who : Player) (word : DecisionView who Δ)

local notation "app" => phaseApplication runtime leaks
local notation "family" => phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed
  assessment block low generation slotWeight slotNonnegative slotBounded who

/-- Every surviving addressed binding of a possible member has an authentic
raw record of that member's exact typed result. The callback and its legality
are reconstructed from the initialized history, rather than supplied. -/
private theorem accepted_member
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) {control : (app).Control}
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
    (consistent : (family word).Consistent (control.execution.recall who)) :
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
  have memberConsistent : (family word).Consistent (control.execution.recall candidate.1) := by
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
        (family word) memberConsistent
  rw [owner] at retained acting viewed supported
  have beforeClear := (phase_clear_nativeProgress_of_prefix runtime leaks menu initial horizon
    scheduler before control prior trace isPrefix clear).1
  have offered := phaseCommitWordPolicy_covered setup mode runtime leaks bounds wellFormed
    assessment block low generation slotWeight slotNonnegative slotBounded who word
      (before.execution.recall who) (before.execution.observe (app) who) entry.action supported
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
  have beforeRaw := menu.toRawTrace initial horizon scheduler prior
  obtain ⟨_draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    beforeRaw
  rw [phaseCommitWordPolicy_binding setup mode runtime leaks bounds wellFormed assessment block
    low generation slotWeight slotNonnegative slotBounded who word before.execution valid event
      payload binding actualRequest inside beforeAddress] at supported
  unfold PhaseCount.phaseBindingWordPolicy at supported
  split at supported
  · obtain ⟨serial, declared⟩ := PhaseCount.phaseBindingWordResponse_nonsilent runtime leaks
      bounds who event payload _ _ slotWeight slotNonnegative slotBounded _ _ _ entry.action
        supported (by intro silent; rw [silent] at transmitted; cases transmitted)
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
  · have silent := (PMF.mem_support_pure_iff ..).mp supported
    rw [silent] at transmitted
    cases transmitted

/-- Every latent owned word still possible at the actual supported recall
agrees with each surviving current-block binding. Its exact private raw action
is retained as a witness, so an accepted failure is constrained as well. -/
theorem phaseCommitWordPosterior_accepted
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) {control : (app).Control}
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
    (prior : PMF (DecisionView who Δ))
    (consistent : ((app).policyMixture prior family).policy.Consistent
      (control.execution.recall who))
    (possible : word ∈ (((app).policyMixture prior family).posterior
      (control.execution.recall who)).support) :
    let result := (phaseRecoveryBindingData setup mode event who payload binding
      (CommitRecoveryMove.lift (block.wordAction who (event.val - low) word))).1
    control.execution.application.current.native.bindingResult candidate payload = result ∧
      (∃ entry ∈ control.execution.recall who,
        entry.beforeView.application.2.attempt = ⟨low, generation⟩ ∧
        phaseBindingAction? setup.program mode runtime leaks entry.action =
          decodeEventAction setup.program event
            (cast (congrArg EventField.Action binding.symm) result)) ∧
      ∀ action, decodeEventAction setup.program event
          (cast (congrArg EventField.Action binding.symm) result) = some action →
        action ∈ phaseCommitRecallWord setup.program mode runtime leaks low (low + block.length)
          generation (control.execution.recall who) := by
  have member := (app).policyMixture_member_consistent prior family
    (control.execution.recall who) consistent word possible
  obtain ⟨entry, serial, retained, attempt, declared, _candidate, meaning, decoded⟩ :=
    accepted_member setup mode runtime leaks bounds wellFormed assessment block low generation
      slotWeight slotNonnegative slotBounded who word plan maximal inputs horizon scheduler trace
        clear event payload binding inside address candidate accepted member
  refine ⟨meaning, ⟨entry, retained, attempt, decoded⟩, ?_⟩
  intro action observed
  let result := (phaseRecoveryBindingData setup mode event who payload binding
    (CommitRecoveryMove.lift (block.wordAction who (event.val - low) word))).1
  let material : WitnessedSubmission (serviceGraph setup mode) :=
    ⟨⟨.commitment event (who, .prepared serial), match result with
      | .failure => none
      | .success value => some ⟨payload, value⟩⟩, .none⟩
  have transmitted : entry.action.transmission = some material := by rw [declared]; rfl
  exact phaseCommitRecallWord_mem setup.program mode runtime leaks low (low + block.length)
    generation (control.execution.recall who) entry retained attempt material transmitted event
      (who, .prepared serial) rfl inside action (decoded.trans observed)

end Vegas
