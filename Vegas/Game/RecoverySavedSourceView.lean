/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoverySavedSourceRank
import Vegas.Game.RecoveryResidualUniqueness
import Vegas.Game.RecoveryArchivedBindingRecall
import Vegas.Game.PhaseSurvivingSourceView
import Vegas.Game.PhaseSurvivingBindingSource

/-! # Saved source checkpoint views read from actual surviving binding data -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The same physical archived-word decoder recovers the exact saved view of
this chosen checkpoint. Readiness need not complete foreign private bindings;
only the virtual current view is used before projecting back to the saved rank. -/
theorem RecoverySourceCheckpoint.saved_view_of_ready_binding
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (aligned : checkpoint.ArchivedRecall) (archives : state.ArchivesBefore)
    {Δ : SourceCtx Player L} {P : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} (fresh : name ∉ Δ.map Prod.fst)
    (guard : SourceGuard L Δ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Δ) (insert name P))
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (reconstruct : earlier.prepend (.commit name owner fresh guard next) = checkpoint.residual.tail)
    (stored : state.StoredCheckpoint) (survives : owner ∉ state.entry.excluded)
    (selected : Fin (eventCount checkpoint.residual.tail)) (atEnd : selected.val = earlier.length)
    (ready : state.current.native.config.cut.Ready (checkpoint.embedding.event selected))
    (acting : (serviceGraph setup mode).actor? (checkpoint.embedding.event selected) = some owner)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout
      (checkpoint.embedding.event selected)).IsPublication)
    (valid : state.current.native.BindingInvariant) {inputs}
    (reachable : state.current.native.config.Reachable inputs)
    (retained : state.HistoryCheckpoint)
    (saved : state.entry.native.config.cut.IsPrefix state.attempt.phase) :
    let past := decodeHistory setup.program
      ((PhaseRuntimeState.archivedHistory state.retired
        state.current.native.config.history).map
          ((toEventGraph setup.program).fromModeCompletion mode)) owner
    (decodeEventView? setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputEmbedding setup.program).ref owner (checkpoint.embedding.event selected)
      ((serviceGraph setup mode).playerStore owner state.current.native.config.store) past).bind
        (ProtocolView.atRank owner setup.program state.attempt.phase) =
      some (ProtocolState.observe owner setup.program (checkpoint.residual.lift
        (ProtocolState.entry checkpoint.residual.tail checkpoint.source))) := by
  intro past
  have word := checkpoint.filled_prefix_archived_history_of_ready aligned archives fresh guard next
    earlier reconstruct survives selected atEnd ready acting valid reachable retained saved
  have current := checkpoint.filled_prefix_view fresh guard next earlier reconstruct stored selected
    atEnd ready acting notPublication past word
  have readback := checkpoint.filled_prefix_saved_rank earlier (.commit name owner fresh guard next)
    reconstruct state.current.native.config.store owner
  rw [current, Option.bind_some]
  exact readback

/-- The chosen archive-aligned checkpoint's saved view is an actual observable
readout at a surviving seed request; all native provenance is derived from the trace. -/
theorem RecoverySourceCheckpoint.saved_view_of_seed_request
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control))
    (checkpoint : RecoverySourceCheckpoint setup mode control.execution.application)
    (aligned : checkpoint.ArchivedRecall)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩) :
    (phaseSurvivingSourceView? setup mode runtime leaks who event
      (control.execution.observe (phaseApplication runtime leaks) who)).bind
        (ProtocolView.atRank who setup.program control.execution.application.attempt.phase) =
      some (ProtocolState.observe who setup.program (checkpoint.residual.lift
        (ProtocolState.entry checkpoint.residual.tail checkpoint.source))) := by
  let inputs : PMF (serviceGraph setup mode).Inputs := setup.initialLaw.map encodeInputs
  have physicalTrace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  have exclusion := phaseExclusionRecord_history runtime leaks plan inputs horizon scheduler
    physicalTrace
  have stored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler
    physicalTrace
  have coverage := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler
    physicalTrace
  have bindingRecord := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler
    physicalTrace
  have retained := phaseHistoryCheckpoint_history runtime leaks plan inputs horizon scheduler
    physicalTrace
  obtain ⟨_input, native⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    scheduler physicalTrace
  have archives := PhaseRuntimeState.archivesBefore_history runtime leaks plan inputs horizon
    scheduler physicalTrace
  have survives : who ∉ control.execution.application.entry.excluded :=
    fun member => request.2.2.2.2 (coverage.inherited member)
  obtain ⟨phase, remaining, installed, kind, inside⟩ := phase_ready_binding_phase runtime leaks
    plan (serviceGraph_revealRelaxedOrdered setup mode) maximal inputs horizon scheduler
      physicalTrace who event payload binding request.2.2.1
  obtain ⟨selected, selectedEq, Δ, P, name, fresh, guard, next, earlier, atEnd, reconstruct⟩ :=
    checkpoint.ready_binding_prefix exclusion.frontier phase remaining installed kind event inside
      request.2.2.1 who payload binding
  have acting : (serviceGraph setup mode).actor? event = some who :=
    EventGraph.actor?_of_outputLayout_binding _ binding
  have notPublication : ¬ ((serviceGraph setup mode).outputLayout event).IsPublication := by
    rw [binding]
    exact id
  have saved : control.execution.application.entry.native.config.cut.IsPrefix
      control.execution.application.attempt.phase := by
    have positioned := exclusion.frontier.positioned
    rw [installed] at positioned
    simpa only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some] using positioned.1
  have readback := checkpoint.saved_view_of_ready_binding aligned archives fresh guard next earlier
    reconstruct stored survives selected atEnd (selectedEq.symm ▸ request.2.2.1)
    (selectedEq.symm ▸ acting) (selectedEq.symm ▸ notPublication) bindingRecord.active
    native.active.reachable retained saved
  rw [phaseSurvivingSourceView?_observed_of_history setup mode runtime leaks plan inputs horizon
    scheduler physicalTrace who event]
  simpa only [selectedEq] using readback

/-- Equal actual physical inputs determine the genuine saved focal source
views of their chosen archive-aligned checkpoints, even with permanent exclusions. -/
theorem phase_saved_source_views_eq_of_observed
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {first second}
    (firstTrace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some first))
    (secondTrace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some second))
    (left : RecoverySourceCheckpoint setup mode first.execution.application)
    (right : RecoverySourceCheckpoint setup mode second.execution.application)
    (leftAligned : left.ArchivedRecall) (rightAligned : right.ArchivedRecall)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (firstRequest : first.execution.application.SeedRequest who
      ⟨first.execution.application.attempt, event⟩)
    (secondRequest : second.execution.application.SeedRequest who
      ⟨second.execution.application.attempt, event⟩)
    (observed : first.execution.observe (phaseApplication runtime leaks) who =
      second.execution.observe (phaseApplication runtime leaks) who) :
    ProtocolState.observe who setup.program (left.residual.lift
        (ProtocolState.entry left.residual.tail left.source)) =
      ProtocolState.observe who setup.program (right.residual.lift
        (ProtocolState.entry right.residual.tail right.source)) := by
  have firstRead := left.saved_view_of_seed_request runtime leaks plan maximal horizon scheduler
    firstTrace leftAligned who event payload binding firstRequest
  have secondRead := right.saved_view_of_seed_request runtime leaks plan maximal horizon scheduler
    secondTrace rightAligned who event payload binding secondRequest
  have samePhase : first.execution.application.attempt.phase =
      second.execution.application.attempt.phase :=
    congrArg (fun view => view.application.2.attempt.phase) observed
  rw [observed, samePhase] at firstRead
  exact Option.some.inj (firstRead.symm.trans secondRead)

private theorem lift_entry_residual_cast
    {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {first second : ResidualProgram whole}
    (same : first = second) (source : SourceProgram.Config Player L first.context) :
    second.lift (ProtocolState.entry second.tail
        (cast (congrArg (fun residual : ResidualProgram whole =>
          SourceProgram.Config Player L residual.context) same) source)) =
      first.lift (ProtocolState.entry first.tail source) := by
  cases same
  rfl

/-- Actual equal physical inputs determine equal saved typed source decision
views after the derived residual cast; no source-view equality is supplied. -/
theorem phase_saved_source_config_views_eq_of_observed
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {first second}
    (firstTrace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some first))
    (secondTrace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some second))
    (left : RecoverySourceCheckpoint setup mode first.execution.application)
    (right : RecoverySourceCheckpoint setup mode second.execution.application)
    (leftAligned : left.ArchivedRecall) (rightAligned : right.ArchivedRecall)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (firstRequest : first.execution.application.SeedRequest who
      ⟨first.execution.application.attempt, event⟩)
    (secondRequest : second.execution.application.SeedRequest who
      ⟨second.execution.application.attempt, event⟩)
    (observed : first.execution.observe (phaseApplication runtime leaks) who =
      second.execution.observe (phaseApplication runtime leaks) who) :
    let samePhase : first.execution.application.attempt.phase =
        second.execution.application.attempt.phase :=
      congrArg (fun view => view.application.2.attempt.phase) observed
    (cast (congrArg (fun residual : ResidualProgram setup.program =>
        SourceProgram.Config Player L residual.context)
      (left.residual_eq_of_phase_eq right samePhase)) left.source).view who =
        right.source.view who := by
  intro samePhase
  have saved := phase_saved_source_views_eq_of_observed setup mode runtime leaks plan maximal
    horizon scheduler firstTrace secondTrace left right leftAligned rightAligned who event payload
    binding firstRequest secondRequest observed
  have localView := right.origin.observe_reflect who
    (ProtocolState.entry right.residual.tail
      (cast (congrArg (fun residual : ResidualProgram setup.program =>
        SourceProgram.Config Player L residual.context)
        (left.residual_eq_of_phase_eq right samePhase)) left.source))
    (ProtocolState.entry right.residual.tail right.source) (by
      rw [lift_entry_residual_cast (left.residual_eq_of_phase_eq right samePhase) left.source]
      exact saved)
  simpa only [ProtocolView.entryView_observe_entry] using
    congrArg (ProtocolView.entryView who right.residual.tail) localView

end Vegas
