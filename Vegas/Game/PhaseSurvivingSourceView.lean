/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseArchivedObservation
import Vegas.Game.PhaseSurvivingBindingSource

/-! # Observable complete surviving source views across retired attempts -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Read the current original source view using all publicly archived attempts
and the owner's permanent private catalogue. Foreign stored bindings remain masked. -/
def phaseSurvivingSourceView? (setup : Setup (Player := Player) (L := L))
    (mode : ExecutionMode) (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (view : (phaseApplication runtime leaks).PlayerView) : setup.ProtocolView who :=
  if same : view.application.1.who = who then
    let observed : (serviceGraph setup mode).PlayerObservation who := same ▸
      view.application.1.observation
    let past := view.application.2.archivedOwnHistory who view.application.1.candidates
      observed.ownActions
    decodeEventView? setup.program (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputRef setup.program) who event observed.store
      (decodeCompletions setup.program (past.map (setup.eventGraph.fromModeCompletion mode)))
  else none

/-- At any actual initialized physical history the existing decoder reads the
entire effective own source word, including the publicly archived attempts. -/
theorem phaseSurvivingSourceView?_observed_of_history
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId) :
    phaseSurvivingSourceView? setup mode runtime leaks who event
        (control.execution.observe (phaseApplication runtime leaks) who) =
      decodeEventView? setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (outputEmbedding setup.program).ref who event
        ((serviceGraph setup mode).playerStore who
          control.execution.application.current.native.config.store)
        (decodeHistory setup.program
          ((PhaseRuntimeState.archivedHistory control.execution.application.retired
            control.execution.application.current.native.config.history).map
              ((toEventGraph setup.program).fromModeCompletion mode)) who) := by
  have visible := phaseArchivedHistory_observed runtime leaks plan inputs horizon scheduler trace
    who
  have word : decodeCompletions setup.program
      ((control.execution.application.publicView.archivedOwnHistory who
          (control.execution.application.current.native.playerView who).candidates
          ((serviceGraph setup mode).playerObserve who
            control.execution.application.current.native.config).ownActions).map
        (setup.eventGraph.fromModeCompletion mode)) =
      decodeHistory setup.program
        ((PhaseRuntimeState.archivedHistory control.execution.application.retired
          control.execution.application.current.native.config.history).map
            ((toEventGraph setup.program).fromModeCompletion mode)) who := by
    rw [visible]
    simp only [decodeHistory, ownCompletions, List.filter_map]
    rfl
  simp only [phaseSurvivingSourceView?, ReactiveApplication.Execution.observe,
    phaseApplication, PhaseRuntimeState.playerView, State.playerView]
  change decodeEventView? setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program)) (outputRef setup.program)
    who event ((serviceGraph setup mode).playerStore who
      control.execution.application.current.native.config.store) _ = _
  exact congrArg (fun past => decodeEventView? setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program)) (outputRef setup.program)
    who event ((serviceGraph setup mode).playerStore who
      control.execution.application.current.native.config.store) past) word

/-- At an authentic surviving binding request the observable decoder gives a
genuine played auxiliary source view, with its complete own history including
retired attempts. Saved source exclusions and generation are retained separately
from the additional physical in-phase exclusions. -/
theorem phaseSurvivingSourceView?_of_ready_binding [Finite Player]
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
        some (ProtocolState.observe who setup.program source.point) := by
  let := Fintype.ofFinite Player
  obtain ⟨source, sourceTrace, excluded, generation, publicSignal, acting, played,
      history, decoded, _numeric⟩ :=
    phase_ready_binding_surviving_source setup mode runtime leaks plan maximal horizon scheduler
      trace who event payload binding request
  let inputs : PMF (serviceGraph setup mode).Inputs := setup.initialLaw.map encodeInputs
  have actualTrace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  refine ⟨source, sourceTrace, excluded, generation, publicSignal, acting, played, ?_⟩
  rw [phaseSurvivingSourceView?_observed_of_history setup mode runtime leaks plan inputs horizon
    scheduler actualTrace who event, ← history]
  exact decoded

end Vegas
