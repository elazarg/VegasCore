/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseSourcePolicyLaw
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

/-- Every actual clear unsent binding selects a genuine complete auxiliary
decision input. Its exact local typed-result and omission law is retained;
source posterior and continuation comparisons are separate. -/
theorem phaseSourcePolicy_binding_at_played_information
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
    (clear : control.execution.application.current.excluded = ∅) :
    ∃ view serial,
      phaseSourceView? setup mode runtime leaks who event
        (control.execution.observe (phaseApplication runtime leaks) who) = some view ∧
      setup.commitRecoveryModel.IsDecisionInfo who
        (setup.commitRecoveryClearInformation wellFormed who (some view)) ∧
      serial < horizon ∧
      let source := assessment.strategy who
        (setup.commitRecoveryClearInformation wellFormed who (some view))
      let actual := phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment who
        (control.execution.recall who)
          (control.execution.observe (phaseApplication runtime leaks) who)
      actual = source.map (fun choice => phaseRecoveryBindingResponse setup mode runtime leaks
        who event payload outputEq serial choice.1) ∧
      actual.map (fun response =>
        let after := control.execution.respond (phaseApplication runtime leaks) who response
        (after.application.current.native.bindingResult (who, .prepared serial) payload,
          response.transmission.isNone)) =
        source.map (fun choice =>
          phaseRecoveryBindingData setup mode event who payload outputEq choice.1) := by
  let inputs : PMF (serviceGraph setup mode).Inputs := setup.initialLaw.map encodeInputs
  have finiteTrace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  obtain ⟨view, serial, decoded, bounded, law, result⟩ := phaseSourcePolicy_binding_of_history
    setup mode runtime leaks bounds wellFormed assessment who event payload outputEq menu plan
      inputs horizon scheduler capacity control finiteTrace acting request unsent values
  have raw := menu.toRawTrace _ horizon scheduler trace
  have played := phase_ready_binding_information setup mode runtime leaks plan maximal horizon
    scheduler raw who event payload outputEq request.2.2.1 clear wellFormed
  rw [decoded] at played
  exact ⟨view, serial, decoded, played, bounded, law, result⟩

end Vegas
