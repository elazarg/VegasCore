/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseOpeningDeadline
import Vegas.Pending.ExclusionAcceptedOutput

/-! # Physical operations preserve clear canonical phase play -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (deadline : (serviceGraph setup mode).EventId → Nat)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
  (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
  (assessment : setup.commitRecoveryModel.BehavioralAssessment)
  (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source assessment.strategy)
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (horizon : Nat)
  (scheduler : (phaseApplication (serviceRuntime setup mode deadline) leaks).Scheduler)

local notation "R" => serviceRuntime setup mode deadline
local notation "P" => phaseApplication R leaks
local notation "I" => setup.initialLaw.map encodeInputs
local notation "start" =>
  PMF.map (PhaseRuntimeState.initial plan) (setup.initialLaw.map encodeInputs)

include copies maximal

/-- An actual accepted canonical-history opening has successful current guards;
accepted commitments retain exclusion independently of their hidden result. -/
theorem phaseSourcePolicy_handle_clear_of_history
    (current : (P).Control)
    (trace : ((PhaseCount.onePacketMenu R leaks bounds).protocol start horizon scheduler).Trace
      (some current))
    (clear : current.execution.application.current.excluded = ∅)
    (consistent : ∀ owner, (phaseSourcePolicy setup mode R leaks bounds wellFormed assessment
      owner).Consistent (current.execution.recall owner))
    (message : Message Player (CommitAttemptPacket (serviceGraph setup mode)))
    (next : PhaseRuntimeState (serviceGraph setup mode))
    (accepted : current.execution.application.handle R message = some next) :
    next.current.excluded = ∅ := by
  classical
  let state : PhaseRuntimeState (serviceGraph setup mode) := current.execution.application
  change state.handle R message = some next at accepted
  unfold PhaseRuntimeState.handle at accepted
  split at accepted
  · rename_i authorized
    obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
    apply (PhaseRuntimeState.settle_physical _ _ _ _ _).1.trans
    change (state.current.inclusionResult message.payload.packet.call native).excluded = ∅
    cases call : message.payload.packet.call with
    | commitment event candidate =>
        simpa only [call, RecoveryState.inclusionResult] using clear
    | malformed raw =>
        simp only [call, handle] at handled
        cases handled
    | opening event candidate raw =>
        rw [call] at handled
        obtain ⟨ready, _within, owner, payload, binding, checks, outputEq, codeEq, _value,
          _result, node, _sender, _candidateOwner, _accepted, _raw, _lookup, _stored,
          _resolved, _next⟩ := handle_opening_conditions R state.current.native native
            message.id event candidate raw handled
        have allowed := (Bool.and_eq_true_iff.mp
          (Bool.and_eq_true_iff.mp authorized).1).2
        obtain ⟨phase, installed, actual, named, inside⟩ := state.allows_event _ allowed
        simp only [call, Payload.event?, Option.some.injEq] at named
        subst actual
        have owned := nodeView_resolve_actor outputEq codeEq
        have request : state.SeedRequest owner ⟨state.attempt, event⟩ :=
          ⟨rfl, ⟨phase, installed, inside⟩, ready, owned, by
            change owner ∉ current.execution.application.current.excluded
            rw [clear]
            exact Finset.notMem_empty owner⟩
        obtain ⟨payload', binding', checks', outputEq', codeEq', otherNode, value, resolved⟩ :=
          phase_ready_publication_success setup mode R leaks bounds wellFormed source assessment
            copies plan maximal horizon scheduler trace clear consistent owner event request
              (by rw [outputEq]; trivial)
        rw [node] at otherNode
        cases otherNode
        have succeeded := handle_opening_output_success R state.current.native native message.id
          event candidate raw handled owner payload binding checks outputEq codeEq node value
            resolved
        have valid := (phaseBindingRecord_history R leaks plan I horizon scheduler
          ((PhaseCount.onePacketMenu R leaks bounds).toRawTrace start horizon scheduler
            trace)).active
        have notFailed := succeeded.not_publicFailure
          (handle_bindingInvariant R state.current.native native
            ⟨message.id, .opening event candidate raw⟩ valid handled)
        have failed : RecoveryState.publicationFailed native event = false :=
          Bool.eq_false_iff.mpr (fun bad => notFailed (Or.inr bad))
        simpa only [call, RecoveryState.inclusionResult, failed, Bool.false_eq_true, ↓reduceIte]
          using clear
  · cases accepted

end Vegas
