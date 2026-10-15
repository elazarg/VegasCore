/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCompiledBindingResponse
import Vegas.Game.PhaseCompiledObservation

/-! # Actual binding kernels at their reconstructed original configurations -/

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

/-- The complete fresh physical binding law equals the normalized compiled
kernel at its actual original-action configuration. The graph decoder match
is derived from the clear history and supported disclosing memories. -/
theorem phaseSourcePolicy_compiled_binding_of_originalConfig
    (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile
      source assessment.strategy)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (capacity : horizon ≤ bounds.candidateCount)
    (control : (phaseApplication runtime leaks).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (consistent : ∀ who,
      (runtime.prescribedReactivePolicy (PhaseNativeProjection.nativeLeaks leaks plan) who
        (copied who)).Consistent
          ((PhaseNativeProjection.execution runtime leaks plan control.execution).recall who))
    (memories : Player → List (Option (serviceGraph setup mode).Completion))
    (supported : ∀ who, memories who ∈
      ((runtime.prescribedReactiveImplementation (PhaseNativeProjection.nativeLeaks leaks plan)
        who (copied who)).posterior
          ((PhaseNativeProjection.execution runtime leaks plan
            control.execution).recall who)).support)
    (who : Player) (active : control.actor = some who)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (site : setup.intendedModel.InformationSite who)
    (original : setup.intendedModel.InformationHistory who site.1)
    (view : SourceProgram.ProtocolView who setup.program) (current : site.1 = some view)
    (decodedPhase : phaseSourceView? setup mode runtime leaks who event
      (control.execution.observe (phaseApplication runtime leaks) who) = some view)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) binding)
      ((serviceGraph setup mode).nodes event) = .bind who payload)
    (node : nodeView (serviceGraph setup mode) event = .bind who payload binding codeEq) :
    ∃ serial, serial < horizon ∧
      reactiveFreshSlot (control.execution.application.current.native.playerView who) =
        some serial ∧
      (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment who
        (control.execution.recall who)
        (control.execution.observe (phaseApplication runtime leaks) who)).map
          (PhaseNativeProjection.action runtime leaks plan) =
        ((serviceGraph setup mode).normalizePolicy who (copied who) event request.2.2.2.1
          ((serviceGraph setup mode).playerObserve who
            (runtime.originalConfig (PhaseNativeProjection.nativeLeaks leaks plan)
              (PhaseNativeProjection.execution runtime leaks plan control.execution) memories))).map
          (fun action => runtime.reactiveDecision (PhaseNativeProjection.nativeLeaks leaks plan)
            who event action (control.execution.application.current.native.playerView who)) := by
  classical
  have fixed := phase_compiled_originalConfig_of_clear setup mode runtime leaks
    (setup.decodeBehavioralProfile (CommitmentInterface.values setup.program)
      (setup.openingExtension source)) (setup.openingExtension_disclosing source)
        bounds plan inputs horizon scheduler trace clear consistent memories supported
  let observation := (toEventGraph setup.program).fromModeObservation mode who
    ((serviceGraph setup mode).normalizeObservation event who
      ((serviceGraph setup mode).playerObserve who
        (runtime.originalConfig (PhaseNativeProjection.nativeLeaks leaks plan)
          (PhaseNativeProjection.execution runtime leaks plan control.execution) memories)))
  have readback : phaseSourceView? setup mode runtime leaks who event
      (control.execution.observe (phaseApplication runtime leaks) who) =
      decodeEventView? setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program)) (outputRef setup.program)
        who event observation.store (decodeCompletions setup.program observation.ownActions) := by
    dsimp only [observation, EventGraph.fromModeObservation, EventGraph.normalizeObservation]
    rw [fixed]
    unfold phaseSourceView?
    rw [dite_eq_left (show (control.execution.observe (phaseApplication runtime leaks)
      who).application.1.who = who from rfl)]
    rfl
  have decodedGraph := readback.symm.trans decodedPhase
  obtain ⟨serial, bounded, allocated, law⟩ := phaseSourcePolicy_compiled_binding_of_history
    setup mode runtime leaks bounds wellFormed source assessment copies plan inputs horizon
      scheduler capacity control trace who active event payload binding request unsent values
        site original view current decodedPhase observation decodedGraph codeEq node
  exact ⟨serial, bounded, allocated, law⟩

end Vegas
