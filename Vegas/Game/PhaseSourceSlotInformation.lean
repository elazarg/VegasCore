/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseSourceSlotPolicyLaw
import Vegas.Game.PhaseSourcePolicyInformation
import Vegas.Game.PhaseBindingCounterpart

/-! # Dispatched binding laws at genuinely played auxiliary source information -/

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

/-- The slot law is evaluated at genuinely played auxiliary information
when the actual current source view has a played intended witness. -/
theorem phaseSourceSlotPolicy_binding_at_played_information
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (capacity : horizon ≤ bounds.candidateCount)
    (control : (phaseApplication runtime leaks).Control)
    (trace : (menu.protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control)) (acting : control.actor = some who)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (clear : control.execution.application.current.excluded = ∅)
    (original : setup.intendedProtocol.History)
    (same : phaseSourceView? setup mode runtime leaks who event
      (control.execution.observe (phaseApplication runtime leaks) who) =
        setup.intendedModel.infoOf who original.trace) :
    ∃ view,
      phaseSourceView? setup mode runtime leaks who event
        (control.execution.observe (phaseApplication runtime leaks) who) = some view ∧
      setup.commitRecoveryModel.IsDecisionInfo who
        (setup.commitRecoveryInformation wellFormed who (some view)) ∧
      (PhaseCount.phaseBindingSlots runtime leaks bounds who event payload
        (control.execution.recall who)
        (control.execution.observe (phaseApplication runtime leaks) who)).Nonempty ∧
      (phaseSourceSlotPolicy setup mode runtime leaks bounds wellFormed assessment who
        (control.execution.recall who)
        (control.execution.observe (phaseApplication runtime leaks) who)).map
        (phaseBindingResponseOutcome setup mode runtime leaks control.execution who payload) =
        (assessment.strategy who (setup.commitRecoveryInformation wellFormed who (some view))).map
          (fun choice => phaseRecoveryBindingData setup mode event who payload outputEq
            choice.1) := by
  obtain ⟨view, serial, decoded, played, _bounded, _canonical, _result⟩ :=
    phaseSourcePolicy_binding_at_played_information setup mode runtime leaks bounds wellFormed
      assessment who event payload outputEq menu plan maximal horizon scheduler capacity control
      trace acting request unsent values clear original same
  let inputs : PMF (serviceGraph setup mode).Inputs := setup.initialLaw.map encodeInputs
  have finiteTrace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  obtain ⟨nonempty, law⟩ := phaseSourceSlotPolicy_binding_of_history setup mode runtime leaks
    bounds wellFormed assessment who event payload outputEq menu plan inputs horizon scheduler
      capacity control finiteTrace acting request unsent values
  rw [decoded] at law
  exact ⟨view, decoded, played, nonempty, law⟩

end Vegas
