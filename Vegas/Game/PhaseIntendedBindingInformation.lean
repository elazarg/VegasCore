/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseIntendedCheckpointHistory
import Vegas.Game.PhaseCommitPrefixAdmission
import Vegas.Game.RecoveryBindingPrefix
import Vegas.Game.RecoveryIntendedBindingCheckpoint
import Vegas.Game.RecoveryReadyCommitInformation
import Vegas.Pending.PhaseBindingReadiness

/-! # Genuine intended source information at actual ready binding callbacks -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Actual copied-policy histories determine a genuine intended source site and
original information history with exactly the decoded whole private view.
Saved intendedness and earlier owner admission are derived from the same history. -/
theorem phase_ready_binding_intended_information
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
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
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (ready : control.execution.application.current.native.config.cut.Ready event) :
    ∃ site : setup.intendedModel.InformationSite who,
      ∃ _original : setup.intendedModel.InformationHistory who site.1,
        decodeEventView? setup.program
          (ContextRefs.initial setup.context (outputLayout setup.program))
          (outputEmbedding setup.program).ref who event
          ((serviceGraph setup mode).playerStore who
            control.execution.application.current.native.config.store)
          (decodeHistory setup.program
            (control.execution.application.current.native.config.history.map
              (setup.eventGraph.fromModeCompletion mode)) who) = site.1 ∧
        phaseSourceView? setup mode runtime leaks who event
          (control.execution.observe (phaseApplication runtime leaks) who) = site.1 := by
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let inputs : PMF (serviceGraph setup mode).Inputs := setup.initialLaw.map encodeInputs
  have raw := menu.toRawTrace (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
  obtain ⟨checkpoint, savedIntended⟩ := phase_intended_checkpoint_history setup mode runtime leaks
    bounds wellFormed source assessment copies plan maximal horizon scheduler trace clear consistent
  have exclusion := phaseExclusionRecord_history runtime leaks plan inputs horizon scheduler raw
  have bindings := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler raw
  have stored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler raw
  have retained := phaseHistoryCheckpoint_history runtime leaks plan inputs horizon scheduler raw
  have coverage := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler raw
  obtain ⟨_draw, native⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    raw
  obtain ⟨phase, remaining, installed, kind, inside⟩ := phase_ready_binding_phase runtime leaks
    plan (serviceGraph_revealRelaxedOrdered setup mode) maximal inputs horizon scheduler raw
      who event payload binding ready
  obtain ⟨selected, selectedEq, Δ, P, name, fresh, guard, next, earlier, atEnd, reconstruct⟩ :=
    checkpoint.ready_binding_prefix exclusion.frontier phase remaining installed kind event inside
      ready who payload binding
  have savedClear : control.execution.application.entry.excluded = ∅ :=
    Finset.subset_empty.mp (clear ▸ coverage.inherited)
  have low : control.execution.application.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some]
  have positioned := exclusion.frontier.positioned
  rw [installed] at positioned
  have saved : control.execution.application.entry.native.config.cut.IsPrefix
      control.execution.application.attempt.phase := by
    rw [low]
    exact positioned.1
  let embedding := cast (congrArg
    (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      program) reconstruct.symm) checkpoint.embedding
  let index : Fin (eventCount (earlier.prepend (.commit name who fresh guard next))) :=
    ⟨selected.val, by rw [reconstruct]; exact selected.isLt⟩
  have sameEvent : checkpoint.embedding.event selected = embedding.event index :=
    OutputEmbedding.event_cast setup.program reconstruct.symm checkpoint.embedding selected index
      rfl
  have acting : (serviceGraph setup mode).actor? event = some who :=
    EventGraph.actor?_of_outputLayout_binding _ binding
  have notPublication : ¬ ((serviceGraph setup mode).outputLayout event).IsPublication := by
    rw [binding]
    exact id
  have admitted : (fillCommitPrefix setup.program earlier (.commit name who fresh guard next)
      embedding control.execution.application.current.native.config.store
        checkpoint.source).IntendedFor who P := by
    apply phase_commitPrefix_admitted setup mode runtime leaks bounds wellFormed source assessment
      copies plan maximal inputs horizon scheduler trace clear checkpoint earlier
        (.commit name who fresh guard next) reconstruct who (consistent who) savedIntended
    exact commitPrefix_owned_completed_of_ready setup mode earlier (.commit name who fresh guard
      next) embedding control.execution.application.current.native.config who index atEnd
        (by rw [← sameEvent, selectedEq]; exact ready)
        (by rw [← sameEvent, selectedEq]; exact acting)
        (by rw [← sameEvent, selectedEq]; exact notPublication)
  obtain ⟨site, original, decoded⟩ := checkpoint.intended_binding_information_of_ready wellFormed
    fresh guard next earlier reconstruct savedClear stored savedIntended selected atEnd
      (selectedEq.symm ▸ ready) (selectedEq.symm ▸ acting) (selectedEq.symm ▸ notPublication)
      bindings.active native.active.reachable retained saved admitted
  rw [selectedEq] at decoded
  exact ⟨site, original, decoded,
    (phaseSourceView?_observed setup mode runtime leaks control.execution who event).trans decoded⟩

end Vegas
