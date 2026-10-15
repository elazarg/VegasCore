/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoverySlotComponent
import Vegas.Pending.PhaseBindingSlotHistory

/-! # Exact recovery slot laws at actual phased binding histories -/

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

/-- Slot eligibility and joint source data preservation follow from genuine
readiness, recall and the response budget; no slot or result-law premise is supplied. -/
theorem phaseRecoverySlotPolicy_of_history
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
    (phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed assessment who event
      payload outputEq (control.execution.recall who)
        (control.execution.observe (phaseApplication runtime leaks) who)).map
      (phaseBindingResponseOutcome setup mode runtime leaks control.execution who payload) =
      (assessment.strategy who (setup.commitRecoveryInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event
          (control.execution.observe (phaseApplication runtime leaks) who)))).map
        (fun choice => phaseRecoveryBindingData setup mode event who payload outputEq
          choice.1) := by
  have nonempty := PhaseCount.phaseBindingSlots_nonempty_of_history runtime leaks bounds menu
    plan inputs horizon scheduler capacity control trace who acting event payload outputEq request
    unsent values
  exact ⟨nonempty, phaseRecoverySlotPolicy_result_law setup mode runtime leaks bounds wellFormed
    assessment control.execution who event payload outputEq nonempty⟩

end Vegas
