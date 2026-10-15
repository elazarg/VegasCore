/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCompiledBindingMemory
import Vegas.Game.PhaseIntendedBindingInformation

/-! # Compiled binding kernels at actual reconstructed intended source inputs -/

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

/-- The actual canonical history supplies the original intended information
used to identify the complete physical binding kernel. No intended site,
source observation match or filled-prefix admission is supplied. -/
theorem phaseSourcePolicy_compiled_binding_of_intended_history
    (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile
      source assessment.strategy)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (capacity : horizon ≤ bounds.candidateCount)
    (control : (phaseApplication runtime leaks).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)) horizon
        scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (phaseConsistent : ∀ who, (phaseSourcePolicy setup mode runtime leaks bounds wellFormed
      assessment who).Consistent (control.execution.recall who))
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
  let inputs : PMF (serviceGraph setup mode).Inputs := setup.initialLaw.map encodeInputs
  obtain ⟨site, original, _decoded, phaseView⟩ := phase_ready_binding_intended_information setup
    mode runtime leaks bounds wellFormed source assessment copies plan maximal horizon scheduler
      trace clear phaseConsistent who event payload binding request.2.2.1
  obtain ⟨view, _serial, viewed, _bounded, _law⟩ := phaseSourcePolicy_binding_of_history setup mode
    runtime leaks bounds wellFormed assessment who event payload binding
      (PhaseCount.onePacketMenu runtime leaks bounds) plan inputs horizon scheduler capacity
        control trace active request unsent values
  have current : site.1 = some view := phaseView.symm.trans viewed
  exact phaseSourcePolicy_compiled_binding_of_originalConfig setup mode runtime leaks source bounds
    wellFormed assessment copies plan inputs horizon scheduler capacity control trace clear
      consistent
      memories supported who active event payload binding request unsent values site original view
        current viewed codeEq node

end Vegas
