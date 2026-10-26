/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourcePhaseClientLaw

/-! # Nontruncated first binding laws for arbitrary source clients -/

noncomputable section

namespace Vegas.SourcePhaseClient

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (serviceGraph setup .sequential))
  (leaks : MessageNetwork.ObservationRule Player
    (CommitAttemptPacket (serviceGraph setup .sequential)))
  (bounds : MessageBounds (serviceGraph setup .sequential))

local notation "app" => phaseApplication runtime leaks
local notation "counted" => PhaseCount.onePacketMenu runtime leaks bounds

private theorem moveResponse_binding (who : Player)
    (event : (serviceGraph setup .sequential).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .sequential).outputLayout event = .binding who payload)
    (move : Option (CommitRecoveryMove Player L)) :
    moveResponse setup runtime leaks bounds who event move =
      fun past view => if move.elim false (·.missing) then PMF.pure ⟨none⟩ else
        PhaseCount.phaseBindingPolicy runtime leaks bounds who event payload
          (fun _ _ => PMF.pure
            (phaseRecoveryBindingData setup .sequential event who payload binding move).1)
          past view := by
  classical
  cases node : nodeView (serviceGraph setup .sequential) event with
  | bind owner actual outputEq codeEq =>
      obtain ⟨rfl, rfl⟩ := EventField.binding.inj (outputEq.symm.trans binding)
      funext past view
      simp only [moveResponse, node, ↓reduceDIte]
  | resolve owner actual ref checks outputEq codeEq => cases outputEq.symm.trans binding
  | sample actual law outputEq codeEq => cases outputEq.symm.trans binding

/-- The same actual locally selected fresh serial realizes every binding move.
Source omission remains silence; accepted unusable bindings use the real
failure packet and retain its exact result in the permanent catalogue. -/
theorem binding_encoders_of_history (horizon : Nat) (scheduler : (app).Scheduler)
    {control : (app).Control}
    (trace : ((counted).protocol (initial setup runtime leaks) horizon scheduler).Trace
      (some control))
    (who : Player) (active : control.actor = some who)
    (event : (serviceGraph setup .sequential).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .sequential).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (capacity : horizon ≤ bounds.candidateCount)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    ∃ serial, serial < horizon ∧
      reactiveFreshSlot (control.execution.observe app who).application.1 = some serial ∧
      control.execution.application.current.native.candidates.lookup (who, .prepared serial) =
        .fresh ∧
      (∀ move, moveResponse setup runtime leaks bounds who event move
          (control.execution.recall who) (control.execution.observe app who) =
        PMF.pure (if move.elim false (·.missing) then ⟨none⟩ else
          phaseBindingResponse runtime leaks who event payload
            (phaseRecoveryBindingData setup .sequential event who payload binding move).1
              serial)) ∧
      (∀ result : PublicationResult (L.Val payload),
        let next := control.execution.respond app who
          (phaseBindingResponse runtime leaks who event payload result serial)
        next.application.current.native.bindingResult (who, .prepared serial) payload =
          result) := by
  classical
  let inputs := setup.initialLaw.map encodeInputs
  have countedTrace : ((counted).protocol
      (inputs.map (PhaseRuntimeState.initial (plan setup))) horizon scheduler).Trace
        (some control) := by
    rw [PMF.map_comp]
    exact trace
  have raw := (counted).toRawTrace _ horizon scheduler countedTrace
  obtain ⟨serial, bounded, selected⟩ := PhaseCandidates.reactiveFreshSlot_lt_horizon runtime leaks
    (plan setup) inputs horizon scheduler control raw who active
  have fresh := reactiveFreshSlot_spec _ serial selected
  have fixed := phaseOwnCommitmentsFixed_history runtime leaks _ horizon scheduler raw
  have recalled := PhaseCount.countRecall_history runtime leaks raw
  have covered (result : PublicationResult (L.Val payload)) :
      phaseBindingResponse runtime leaks who event payload result serial ∈
        PhaseCount.onePacketActions runtime leaks bounds who (control.execution.recall who)
          (control.execution.observe app who) := by
    rw [PhaseCount.mem_onePacketActions]
    exact ⟨phaseBindingResponse_available runtime leaks bounds who _ _ event payload values
      result serial (bounded.trans_le capacity), Or.inr
        (PhaseCount.phaseBindingResponse_permitted runtime leaks control.execution recalled fixed
          who event payload binding request unsent result serial fresh)⟩
  refine ⟨serial, bounded, selected, fresh, ?_, ?_⟩
  · intro move
    rw [moveResponse_binding setup runtime leaks bounds who event payload binding]
    split
    · rfl
    · unfold PhaseCount.phaseBindingPolicy
      simp only [selected, ite_eq_left covered, PMF.pure_map]
  · intro result
    exact phaseBindingResponse_result runtime leaks control.execution who event payload result
      serial fresh

/-- At any supported first binding callback, the entire arbitrary source
choice law is pushed through one physical encoder at one locally selected
serial. Omission and accepted failure remain distinct actual responses. -/
theorem supported_first_binding_law (horizon : Nat) (scheduler : (app).Scheduler)
    (source : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) (fuel : Nat)
    (history : ((PhaseCount.rawMenu runtime leaks bounds).protocol
      (initial setup runtime leaks) horizon scheduler).History)
    (supported : history ∈ (((PhaseCount.rawMenu runtime leaks bounds).information
      (initial setup runtime leaks) horizon scheduler).runBehavioral
        (compileProfile setup runtime leaks bounds horizon scheduler source) fuel).support)
    (control : (app).Control) (atState : history.state = some control)
    (who : Player) (active : control.actor = some who)
    (event : (serviceGraph setup .sequential).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .sequential).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (first : ¬ PhaseCount.ResponseRecorded runtime leaks who
      ⟨control.execution.application.attempt, event⟩ (control.execution.recall who))
    (capacity : horizon ≤ bounds.candidateCount)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    ∃ serial, serial < horizon ∧
      reactiveFreshSlot (control.execution.observe app who).application.1 = some serial ∧
      ∃ (current : CommitRecoveryState setup.program)
        (sourceTrace : setup.commitRecoveryProtocol.Trace (some current)),
        current.excluded = control.execution.application.current.excluded ∧
        ProtocolState.actor setup.program current.point = some who ∧
        policy setup runtime leaks bounds who (source who) (control.execution.recall who)
            (control.execution.observe app who) =
          (source who (setup.commitRecoveryModel.infoOf who sourceTrace)).map fun choice =>
            if choice.val.elim false (·.missing) then ⟨none⟩ else
              phaseBindingResponse runtime leaks who event payload
                (phaseRecoveryBindingData setup .sequential event who payload binding choice.val).1
                serial := by
  obtain ⟨countedTrace⟩ := supported_counted_trace setup runtime leaks bounds horizon scheduler
    source fuel history supported control atState
  have unsent := supported_first_unsent setup runtime leaks bounds horizon scheduler source fuel
    history supported control atState who ⟨control.execution.application.attempt, event⟩ first
  obtain ⟨serial, bounded, selected, _fresh, encoded, _results⟩ :=
    binding_encoders_of_history setup runtime leaks bounds horizon scheduler countedTrace who
      active event payload binding request unsent capacity values
  have directTrace := (counted).toRawTrace _ horizon scheduler countedTrace
  obtain ⟨current, sourceTrace, exclusions, actor, law⟩ := policy_first_of_history setup runtime
    leaks bounds horizon scheduler directTrace who (source who) event request first
  refine ⟨serial, bounded, selected, current, sourceTrace, exclusions, actor, ?_⟩
  rw [law, ← PMF.bind_pure_comp]
  apply congrArg (fun continuation =>
    (source who (setup.commitRecoveryModel.infoOf who sourceTrace)).bind continuation)
  funext choice
  exact encoded choice.val

end Vegas.SourcePhaseClient
