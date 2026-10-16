/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseSurvivingSourceView
import Vegas.Source.CommitRecoverySavedObservation

/-! # Observable saved source views at surviving physical binding requests -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Existing current-view decoding and the public phase rank recover the saved
view of the same genuine source counterpart. Physical in-phase exclusions are
kept separate from the counterpart's saved exclusions. -/
theorem phaseSurvivingSourceView?_saved_of_ready_binding
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩) :
    ∃ (source : CommitRecoveryState setup.program)
      (sourceTrace : setup.commitRecoveryProtocol.Trace (some source)),
      source.excluded = control.execution.application.entry.excluded ∧
      source.generation = control.execution.application.generation ∧
      setup.commitRecoveryPublic (some source) =
        (control.execution.application.entry.excluded, control.execution.application.generation,
          control.execution.application.attempt.phase) ∧
      ProtocolState.actor setup.program source.point = some who ∧
      setup.commitRecoveryModel.IsDecisionInfo who
        (setup.commitRecoveryModel.infoOf who sourceTrace) ∧
      phaseSurvivingSourceView? setup mode runtime leaks who event
          (control.execution.observe (phaseApplication runtime leaks) who) =
        some (ProtocolState.observe who setup.program source.point) ∧
      (phaseSurvivingSourceView? setup mode runtime leaks who event
          (control.execution.observe (phaseApplication runtime leaks) who)).bind
        (ProtocolView.atRank who setup.program
          (control.execution.observe (phaseApplication runtime leaks)
            who).application.2.attempt.phase)
        =
        some (ProtocolState.observe who setup.program source.saved) := by
  obtain ⟨source, sourceTrace, excluded, generation, publicSignal, acting, played, decoded⟩ :=
    phaseSurvivingSourceView?_of_ready_binding setup mode runtime leaks plan maximal horizon
      scheduler trace who event payload binding request
  let inputs : PMF (serviceGraph setup mode).Inputs := setup.initialLaw.map encodeInputs
  have physicalTrace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  have coverage := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler
    physicalTrace
  have survives : who ∉ source.excluded := by
    rw [excluded]
    exact fun member => request.2.2.2.2 (coverage.inherited member)
  have readback := setup.commitRecovery_saved_rank who sourceTrace survives
  have rank := congrArg (fun signal => signal.2.2) publicSignal
  change instructionCount setup.program - ProtocolState.remaining setup.program source.saved =
    control.execution.application.attempt.phase at rank
  rw [rank] at readback
  refine ⟨source, sourceTrace, excluded, generation, publicSignal, acting, played, decoded, ?_⟩
  change (phaseSurvivingSourceView? setup mode runtime leaks who event
    (control.execution.observe (phaseApplication runtime leaks) who)).bind
      (ProtocolView.atRank who setup.program control.execution.application.attempt.phase) = _
  rw [decoded, Option.bind_some]
  exact readback

end Vegas
