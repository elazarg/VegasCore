/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseVirtualBindingView

/-! # The source query computed from an actual native binding input -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Failed publication read directly from the public typed output cell. -/
def PublicView.sourcePublicationFailed (view : PublicView graph) (event : graph.EventId) : Bool :=
  match nodeView graph event with
  | .resolve _owner _payload _binding _checks outputEq _ =>
      match view.observation.store (.inr event) with
      | none => false
      | some result =>
          match cast (congrArg EventField.Value outputEq) result with
          | .failure => true
          | .success _ => false
  | .bind .. | .sample .. => false

/-- Public completion masks determine both prefix and total failed-owner sets. -/
def PublicView.sourceFailureFootprint (view : PublicView graph) :
    (Nat → Finset Player) × Finset Player := by
  classical
  let failed := fun event => view.missedBinding event = true ∨
    view.sourcePublicationFailed event = true
  exact (fun rank => Finset.univ.filter fun owner => ∃ event : graph.EventId,
    event.val < rank ∧ graph.actor? event = some owner ∧ failed event,
    Finset.univ.filter fun owner => ∃ event : graph.EventId,
      graph.actor? event = some owner ∧ failed event)

omit [DecidableEq Player] [Fintype Player] in
theorem State.sourcePublicationFailed_read (state : State graph) (event : graph.EventId) :
    state.publicView.sourcePublicationFailed event =
      RecoveryState.publicationFailed state event := by
  cases view : nodeView graph event with
  | bind | sample => simp only [PublicView.sourcePublicationFailed,
      RecoveryState.publicationFailed, view]
  | resolve owner payload binding checks outputEq codeEq =>
      have visible : graph.fieldPublic (.inr event) := by
        change (graph.outputLayout event).IsPublic
        rw [outputEq]
        trivial
      simp only [PublicView.sourcePublicationFailed, RecoveryState.publicationFailed, view,
        State.publicView, EventGraph.publicObserve]
      rw [graph.publicStore_of_public _ _ visible]
      rfl

theorem State.sourceFailureFootprint_read (state : State graph) :
    state.publicView.sourceFailureFootprint = state.sourceFailureFootprint := by
  classical
  apply Prod.ext
  · funext rank
    change state.publicView.sourceFailureFootprint.1 rank = state.failureOwnersBefore rank
    simp only [PublicView.sourceFailureFootprint, State.failureOwnersBefore,
      State.PublicFailure, State.sourcePublicationFailed_read]
  · change state.publicView.sourceFailureFootprint.2 = state.failureOwners
    simp only [PublicView.sourceFailureFootprint, State.failureOwners,
      State.PublicFailure, State.sourcePublicationFailed_read]

/-- The numeric scan uses only the current public image and ordered public
attempt images; no private source witness or retired private word is read. -/
def PhasePublicView.sourcePublicAddressWord (plan : RuntimePhasePlan graph)
    (view : PhasePublicView graph) (eventRank : Nat) :
    List (Option Nat × (Finset Player × Nat × Nat)) :=
  let footprint := view.native.sourceFailureFootprint
  let records := view.retired.map fun record => (record.1, record.2.sourceFailureFootprint)
  let inherited := (records.map fun record => record.2.2).foldr (fun a b => a ∪ b) ∅
  let low := view.attempt.phase
  let saved := inherited ∪ footprint.1 low
  [(some 0, (∅, 0, 0))] ++
    plan.sourceArchiveAddresses footprint.1 view.attempt.generation low records 0 ∅ ++
    (List.range (eventRank - low)).map fun index =>
      (some (low + index + 1), saved, view.attempt.generation, low)

theorem PhaseRuntimeState.sourcePublicAddressWord_read (plan : RuntimePhasePlan graph)
    (state : PhaseRuntimeState graph) (eventRank : Nat) :
    state.publicView.sourcePublicAddressWord plan eventRank =
      state.sourcePublicAddressWord plan eventRank := by
  simp only [PhasePublicView.sourcePublicAddressWord, PhaseRuntimeState.publicView,
    PhaseRuntimeState.sourcePublicAddressWord, PhaseRuntimeState.sourceControlRecords,
    State.sourceFailureFootprint_read, List.map_map, Function.comp_def]

end Vegas.EventGraphRuntime

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The observable combined source label. Normalization is applied to an
erased label; the source table itself is indexed by genuine query images. -/
def phaseVirtualSourceQuery? (setup : Setup (Player := Player) (L := L))
    (mode : ExecutionMode) (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode)) (who : Player)
    (event : (serviceGraph setup mode).EventId)
    (view : (phaseApplication runtime leaks).PlayerView) :
    Option (setup.commitRecoveryModel.InfoState who) :=
  (phaseVirtualSourceView? setup mode runtime leaks who event view).map fun typed =>
    let publicView := view.application.2
    let footprint := publicView.native.sourceFailureFootprint
    let inherited := (publicView.retired.map fun record =>
      record.2.sourceFailureFootprint.2).foldr (fun a b => a ∪ b) ∅
    let controls := (inherited ∪ footprint.1 publicView.attempt.phase,
      publicView.attempt.generation, publicView.attempt.phase)
    let addresses := (publicView.sourcePublicAddressWord plan event.val).reverse ++
      [(none, (∅, 0, 0))]
    setup.commitRecoveryErasedInformation who (setup.commitRecoveryNoMissInformation who
      (setup.commitRecoveryErasedRead who typed controls addresses))

/-- Every actual surviving binding callback reads the combined label of a
genuine original source decision. The public scan is derived from the entire
initialized native trace; no decoder agreement or source endpoint is supplied. -/
theorem phaseVirtualSourceQuery?_genuine_of_ready_binding
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
    ∃ (current : CommitRecoveryState setup.program)
      (sourceTrace : setup.commitRecoveryProtocol.Trace (some current)),
      ProtocolState.actor setup.program current.point = some who ∧
      instructionCount setup.program - ProtocolState.remaining setup.program current.point =
        event.val ∧
      setup.commitRecoveryModel.IsDecisionInfo who
        (setup.commitRecoveryModel.infoOf who sourceTrace) ∧
      phaseVirtualSourceQuery? setup mode runtime leaks plan who event
          (control.execution.observe (phaseApplication runtime leaks) who) =
        some (setup.commitRecoveryErasedInformation who
          (setup.commitRecoveryNoMissInformation who
            (setup.commitRecoveryModel.infoOf who sourceTrace))) := by
  obtain ⟨_original, current, _originalTrace, sourceTrace, excluded, _generation,
    actor, position, played, typed, _publicRecall, controls, addresses⟩ :=
    phaseVirtualSourceView?_genuine_of_ready_binding setup mode runtime leaks plan maximal
      horizon scheduler trace who event payload binding request
  let inputs := setup.initialLaw.map encodeInputs
  have raw : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  have coverage := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler raw
  have active : who ∉ current.excluded := by
    rw [excluded]
    exact fun member => request.2.2.2.2 (coverage.inherited member)
  obtain ⟨phase, remaining, installed, _kind, _inside⟩ := phase_ready_binding_phase runtime leaks
    plan (serviceGraph_revealRelaxedOrdered setup mode) maximal inputs horizon scheduler
      raw who event payload binding request.2.2.1
  have saved := PhaseRuntimeState.saved_excluded_eq_public_failures
    (phaseArchivedExclusions_history runtime leaks plan inputs horizon scheduler raw)
    (phasePublicFailureCheckpoint_history runtime leaks plan inputs horizon scheduler raw)
    (phaseExclusionRecord_history runtime leaks plan inputs horizon scheduler raw).frontier
    phase remaining installed
  have inherited :
      (control.execution.application.publicView.retired.map fun record =>
        record.2.sourceFailureFootprint.2).foldr (fun a b => a ∪ b) ∅ =
      PhaseRuntimeState.archivedFailureOwners control.execution.application.retired := by
    have failures := PhaseRuntimeState.sourceRecordFailures_sourceControlRecords
      control.execution.application.retired
    simpa only [RuntimePhasePlan.sourceRecordFailures, PhaseRuntimeState.sourceControlRecords,
      PhaseRuntimeState.publicView, List.map_map, Function.comp_def,
      State.sourceFailureFootprint_read, State.sourceFailureFootprint] using failures
  have read := setup.commitRecovery_erasedInformation_read who current sourceTrace active
  rw [controls, addresses] at read
  refine ⟨current, sourceTrace, actor, position, played, ?_⟩
  unfold phaseVirtualSourceQuery?
  rw [typed, Option.map_some]
  change some (setup.commitRecoveryErasedInformation who
      (setup.commitRecoveryNoMissInformation who
        (setup.commitRecoveryErasedRead who
          (ProtocolView.eraseHistory who setup.program
            (ProtocolState.observe who setup.program current.point))
          (_, _, _)
          ((control.execution.application.publicView.sourcePublicAddressWord plan event.val).reverse
            ++ [(none, (∅, 0, 0))])))) = _
  dsimp only [ReactiveApplication.Execution.observe, phaseApplication, PhaseRuntimeState.playerView]
  rw [PhaseRuntimeState.sourcePublicAddressWord_read, inherited]
  dsimp only [PhaseRuntimeState.publicView]
  rw [State.sourceFailureFootprint_read]
  dsimp only [State.sourceFailureFootprint]
  rw [← saved]
  have erasedRead : setup.commitRecoveryErasedRead who
      (ProtocolView.eraseHistory who setup.program
        (ProtocolState.observe who setup.program current.point))
      (control.execution.application.entry.excluded, control.execution.application.generation,
        control.execution.application.attempt.phase)
      ((control.execution.application.sourcePublicAddressWord plan event.val).reverse ++
        [(none, (∅, 0, 0))]) =
      setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryModel.infoOf who sourceTrace) := by
    simpa only [Setup.commitRecoveryErasedRead, ProtocolView.eraseHistory_idempotent,
      ProtocolView.publicPadding_eraseHistory] using read.symm
  simpa only [PhaseRuntimeState.attempt, ← setup.commitRecoveryNoMissInformation_erased,
    setup.commitRecoveryErasedInformation_idempotent] using
    congrArg (fun information => some (setup.commitRecoveryErasedInformation who
      (setup.commitRecoveryNoMissInformation who information))) erasedRead

end Vegas
