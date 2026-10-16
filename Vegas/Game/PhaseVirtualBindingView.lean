/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseSurvivingBindingSource
import Vegas.Compile.EventSourceViewErasure
import Vegas.Compile.EventSourcePosition
import Vegas.Source.CommitRecoveryVirtualHistory
import Vegas.Source.CommitRecoveryNoMissRepresentative
import Vegas.Source.CommitRecoveryPublicScan

/-! # Observable virtual typed queries at actual binding requests -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The native typed virtual query reads only the current masked store.
It retains original private inputs, repairs introduced unusable declarations,
and does not reconstruct any retired private action word. -/
def phaseVirtualSourceView? (setup : Setup (Player := Player) (L := L))
    (mode : ExecutionMode) (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (view : (phaseApplication runtime leaks).PlayerView) : setup.ProtocolView who :=
  if same : view.application.1.who = who then
    let observed : (serviceGraph setup mode).PlayerObservation who := same ▸
      view.application.1.observation
    (decodeEventView? setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputEmbedding setup.program).ref who event observed.store []).map
        (ProtocolView.virtualBindings who (setup.context.map Prod.fst).toFinset setup.program)
  else none

/-- At an actual surviving native binding request, the observable virtual typed
view is the current view of a genuine full source query. Its public signal
chronology is exactly that of the same original source counterpart; original
setup bindings and every retry/exhaustion are retained. -/
theorem phaseVirtualSourceView?_genuine_of_ready_binding
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
    ∃ (original virtual : CommitRecoveryState setup.program)
      (originalTrace : setup.commitRecoveryProtocol.Trace (some original))
      (virtualTrace : setup.commitRecoveryProtocol.Trace (some virtual)),
      virtual.excluded = control.execution.application.entry.excluded ∧
      virtual.generation = control.execution.application.generation ∧
      ProtocolState.actor setup.program virtual.point = some who ∧
      instructionCount setup.program - ProtocolState.remaining setup.program virtual.point =
        event.val ∧
      setup.commitRecoveryModel.IsDecisionInfo who
        (setup.commitRecoveryModel.infoOf who virtualTrace) ∧
      phaseVirtualSourceView? setup mode runtime leaks who event
        (control.execution.observe (phaseApplication runtime leaks) who) =
          some (ProtocolView.eraseHistory who setup.program
            (ProtocolState.observe who setup.program virtual.point)) ∧
      (∀ observer, setup.attemptPublicRecall observer virtualTrace =
        setup.attemptPublicRecall observer originalTrace) ∧
      setup.commitRecoveryPublic (some virtual) =
        (control.execution.application.entry.excluded, control.execution.application.generation,
          control.execution.application.attempt.phase) ∧
      (setup.attemptPublicRecall who virtualTrace).map
        (setup.commitRecoveryPublicAddress who) =
          (control.execution.application.sourcePublicAddressWord plan event.val).reverse ++
            [(none, (∅, 0, 0))] := by
  obtain ⟨original, originalTrace, excluded, generation, publicSignal, actor, _played,
    _word, decoded, numeric⟩ :=
    phase_ready_binding_surviving_source setup mode runtime leaks plan maximal
      horizon scheduler trace who event payload binding request
  let inputs : PMF (serviceGraph setup mode).Inputs := setup.initialLaw.map encodeInputs
  have raw : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  have coverage := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler raw
  have active : who ∉ original.excluded := by
    rw [excluded]
    exact fun member => request.2.2.2.2 (coverage.inherited member)
  obtain ⟨virtual, virtualTrace, _length, relation, publicRecall⟩ :=
    setup.commitRecovery_virtual_history who originalTrace original rfl active
  have virtualActive : who ∉ virtual.excluded := by rwa [relation.excluded]
  have virtualActor : ProtocolState.actor setup.program virtual.point = some who := by
    rw [(ProtocolState.FocalRepair.control who setup.program _ _
      relation.focalRepair.point).2.1]
    exact actor
  have originalPosition := decodeEventView?_position setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (outputEmbedding setup.program).ref who event _ _ _ decoded
  have positionCount := ProtocolView.position_add_remaining who setup.program original.point
  rw [originalPosition] at positionCount
  have virtualRemaining := (ProtocolState.FocalRepair.control who setup.program _ _
    relation.focalRepair.point).1
  have virtualPosition : instructionCount setup.program -
      ProtocolState.remaining setup.program virtual.point = event.val := by omega
  have virtualPublic := congrArg Prod.snd
    (setup.commitRecovery_publicSignal_of_focalRepair relation.focalRepair who)
  change setup.commitRecoveryPublic (some virtual) =
    setup.commitRecoveryPublic (some original) at virtualPublic
  refine ⟨original, virtual, originalTrace, virtualTrace, relation.excluded.trans excluded,
    relation.generation.trans generation, virtualActor, virtualPosition,
    commitRecovery_isDecisionInfo_of_surviving_actor setup virtual virtualTrace who virtualActive
      virtualActor, ?_, publicRecall, virtualPublic.trans publicSignal, ?_⟩
  · dsimp only [phaseVirtualSourceView?, ReactiveApplication.Execution.observe, phaseApplication,
      PhaseRuntimeState.playerView, State.playerView]
    rw [dite_eq_left rfl]
    change (decodeEventView? setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (outputEmbedding setup.program).ref who event
        ((serviceGraph setup mode).playerStore who
          control.execution.application.current.native.config.store) []).map _ = _
    rw [decodeEventView?_eraseHistory
        (past := ProtocolState.history setup.program original.point who),
      decoded, Option.map_some, Option.map_some, ProtocolView.virtualBindings_eraseHistory]
    exact congrArg some
      (ProtocolState.VirtualRepair.observe (setup.context.map Prod.fst).toFinset who setup.program
        _ _ relation.point).symm
  · rw [publicRecall who, setup.commitRecovery_publicRecall_addresses, numeric]

end Vegas
