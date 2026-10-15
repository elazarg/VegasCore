/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseSourceSlotPolicy
import Vegas.Game.PhaseRecoverySlotHistory
import Vegas.Game.PhaseSourcePolicyLaw
import Vegas.Game.PhaseBindingCounterpart
import Vegas.Pending.PhaseBindingSlotHistory

/-! # Whole slot-dispatch laws at actual phased histories -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks

/-- Slot eligibility and joint source data preservation follow from genuine
readiness, recall and the response budget; no slot or result-law premise is supplied. -/
theorem phaseSourceSlotPolicy_binding_of_history
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (capacity : horizon ≤ bounds.candidateCount)
    (control : (phaseApplication runtime leaks).Control)
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some control)) (acting : control.actor = some who)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    (PhaseCount.phaseBindingSlots runtime leaks bounds who event payload
      (control.execution.recall who)
        (control.execution.observe (phaseApplication runtime leaks) who)).Nonempty ∧
    (phaseSourceSlotPolicy setup mode runtime leaks bounds wellFormed assessment who
      (control.execution.recall who)
        (control.execution.observe (phaseApplication runtime leaks) who)).map
      (phaseBindingResponseOutcome setup mode runtime leaks control.execution who payload) =
      (assessment.strategy who (setup.commitRecoveryClearInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event
          (control.execution.observe (phaseApplication runtime leaks) who)))).map
        (fun choice => phaseRecoveryBindingData setup mode event who payload outputEq
          choice.1) := by
  have raw := menu.toRawTrace (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    raw
  have branch := phaseSourceSlotPolicy_binding setup mode runtime leaks bounds wellFormed
    assessment control.execution valid who event payload outputEq request
  rw [branch]
  exact phaseRecoverySlotPolicy_of_history setup mode runtime leaks bounds wellFormed assessment
    who event payload outputEq menu plan inputs horizon scheduler capacity control trace acting
    request unsent values

/-- Every bounded fresh physical slot receives its complete original typed-result
mass, scaled only by the number of eligible slots. -/
theorem phaseSourceSlotPolicy_result_mass_of_history
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (control : (phaseApplication runtime leaks).Control)
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some control))
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (serial : Nat) (bounded : serial < bounds.candidateCount)
    (fresh : control.execution.application.current.native.candidates.lookup
      (who, .prepared serial) = .fresh) (result : PublicationResult (L.Val payload)) :
    ((PhaseCount.phaseBindingSlots runtime leaks bounds who event payload
        (control.execution.recall who)
        (control.execution.observe (phaseApplication runtime leaks) who)).card : ENNReal)⁻¹ *
      ((assessment.strategy who (setup.commitRecoveryClearInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event
          (control.execution.observe (phaseApplication runtime leaks) who)))).map
            (fun choice => phaseRecoveryBindingData setup mode event who payload outputEq
              choice.1)) (result, false) ≤
      phaseSourceSlotPolicy setup mode runtime leaks bounds wellFormed assessment who
        (control.execution.recall who) (control.execution.observe (phaseApplication runtime leaks)
          who) (phaseBindingResponse runtime leaks who event payload result serial) := by
  have raw := menu.toRawTrace (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    raw
  rw [phaseSourceSlotPolicy_binding setup mode runtime leaks bounds wellFormed assessment
    control.execution valid who event payload outputEq request]
  have eligible := PhaseCount.mem_phaseBindingSlots_of_history runtime leaks bounds menu plan
    inputs horizon scheduler control trace who event payload outputEq request unsent values
    serial bounded fresh
  exact phaseRecoverySlotPolicy_result_mass setup mode runtime leaks bounds wellFormed assessment
    who event payload outputEq _ _ serial eligible result

/-- At an actual unsent timely opening of a surviving successful binding,
the whole dispatcher emits exactly its authentic canonical opening response. -/
theorem phaseSourceSlotPolicy_opening_of_history
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) {control : (app).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : FieldRef (serviceGraph setup mode).layout (.binding who payload))
    (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) =
      .resolve who payload binding checks)
    (node : nodeView (serviceGraph setup mode) event =
      .resolve who payload binding checks outputEq codeEq)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (value : L.Val payload)
    (stored : binding.get? control.execution.application.current.native.config.store =
      some (.success value))
    (values : (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    ∃ candidate,
      control.execution.application.current.native.accepted binding.field = some candidate ∧
      phaseSourceSlotPolicy setup mode runtime leaks bounds wellFormed assessment who
          (control.execution.recall who) (control.execution.observe app who) =
        PMF.pure (PhaseCount.phaseOpeningResponse runtime leaks event candidate
          ⟨payload, value⟩) := by
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    raw
  have branch := phaseSourceSlotPolicy_opening setup mode runtime leaks bounds wellFormed assessment
    control.execution valid who event payload binding checks outputEq codeEq request
  obtain ⟨candidate, accepted, law⟩ := PhaseCount.phaseOpeningPolicy_of_history runtime leaks bounds
    plan inputs horizon scheduler trace who event payload binding checks outputEq codeEq node
    request
    unsent value stored values (fun _ _ => PMF.pure true)
  refine ⟨candidate, accepted, ?_⟩
  rw [branch, law, PMF.pure_map]
  rfl

end Vegas
