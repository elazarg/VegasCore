/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseIntendedOpeningSuccess
import Vegas.Game.PhaseCompiledDisclosure

/-! # Complete compiled opening kernels at actual intended copied histories -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (source : ∀ who, setup.intendedModel.BehavioralPolicy who)

local notation "copied" => EventGraph.toModeProfile (toEventGraph setup.program) mode
  (compileEventProfile setup.program (Setup.decodeBehavioralProfile setup
    (CommitmentInterface.values setup.program) (Setup.openingExtension setup source)))

/-- Canonical unsent openings and the compiled disclosing response agree at
actual clear copied histories. Successful guard evaluation and the genuine
saved intended checkpoint are derived from that same physical history. -/
theorem phaseSourcePolicy_compiled_opening_of_intended_history
    (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source
      assessment.strategy)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)) horizon
        scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (consistent : ∀ owner, (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment
      owner).Consistent (control.execution.recall owner))
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (publication : ((serviceGraph setup mode).outputLayout event).IsPublication)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs
      (control.execution.recall who), PhaseCount.event? message.payload ≠
        some ⟨control.execution.application.attempt, event⟩)
    (values : ∀ payload, (serviceGraph setup mode).outputLayout event = .publication payload →
      ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (observation : (serviceGraph setup mode).PlayerObservation who) :
    (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment who
      (control.execution.recall who)
      (control.execution.observe (phaseApplication runtime leaks) who)).map
        (PhaseNativeProjection.action runtime leaks plan) =
      ((serviceGraph setup mode).normalizePolicy who (copied who) event request.2.2.2.1
        observation).map (fun action => runtime.reactiveDecision
          (PhaseNativeProjection.nativeLeaks leaks plan) who event action
          (control.execution.application.current.native.playerView who)) := by
  obtain ⟨payload, binding, checks, outputEq, codeEq, node, value, resolved⟩ :=
    phase_ready_publication_success setup mode runtime leaks bounds wellFormed source assessment
      copies plan maximal horizon scheduler trace clear consistent who event request publication
  have stored := EventCode.binding_success_of_resolve_success binding checks true
    control.execution.application.current.native.config.store value resolved
  exact phaseSourcePolicy_compiled_opening_of_success setup mode runtime leaks source bounds
    wellFormed assessment plan (setup.initialLaw.map encodeInputs) horizon scheduler trace who event
      payload binding checks outputEq codeEq node request unsent value stored
        (values payload outputEq value) resolved observation

end Vegas
