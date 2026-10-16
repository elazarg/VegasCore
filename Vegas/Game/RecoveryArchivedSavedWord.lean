/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryArchivedRetry
import Vegas.Pending.PhaseArchivedSavedObservation
import Vegas.Pending.PhaseSurvivingHistory
import Vegas.EventGraph.ConfigRestriction

/-! # Original saved source words read below a retained native phase frontier -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A chosen checkpoint's surviving original source word is read by restricting
the retained native image before reinserting all earlier retired attempts.
Earlier voided actions at the same static addresses are preserved. The image
may be an internal drained endpoint and needs no fictitious initialized trace. -/
theorem RecoverySourceCheckpoint.saved_history_of_retained_image
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (aligned : checkpoint.ArchivedRecall) (who : Player)
    (active : who ∉ state.entry.excluded)
    (image : ((toEventGraph setup.program).withMode mode).Config)
    (retained : state.entry.native.config.history.IsPrefix image.history)
    (saved : state.entry.native.config.cut.IsPrefix state.attempt.phase) :
    checkpoint.source.history who =
      decodeHistory setup.program
        ((PhaseRuntimeState.archivedHistory state.retired
          (image.history.filter fun completion =>
            completion.event.val < state.attempt.phase)).map
          ((toEventGraph setup.program).fromModeCompletion mode)) who := by
  let graph := (toEventGraph setup.program).withMode mode
  have ownPrefix : (graph.ownCompletions who state.entry.native.config.history).IsPrefix
      (graph.ownCompletions who image.history) := by
    obtain ⟨later, complete⟩ := retained
    rw [← complete]
    simp only [EventGraph.ownCompletions, List.filter_append]
    exact ⟨_, rfl⟩
  have restricted := EventGraph.Config.ownCompletions_filter_eq_of_prefix
    state.entry.native.config image who ownPrefix
  have cutoff : (graph.ownCompletions who image.history).filter
        (fun completion => completion.event ∈ state.entry.native.config.cut.completed) =
      (graph.ownCompletions who image.history).filter
        (fun completion => completion.event.val < state.attempt.phase) := by
    apply List.filter_congr
    intro completion _member
    by_cases completed : completion.event ∈ state.entry.native.config.cut.completed
    · simp only [completed, (saved.2 completion.event).mp completed, decide_true]
    · have later : ¬ completion.event.val < state.attempt.phase :=
        fun before => completed ((saved.2 completion.event).mpr before)
      simp only [completed, later, decide_false]
  have nativeWord : graph.ownCompletions who
        (image.history.filter fun completion => completion.event.val < state.attempt.phase) =
      graph.ownCompletions who state.entry.native.config.history := by
    rw [show graph.ownCompletions who
          (image.history.filter fun completion => completion.event.val < state.attempt.phase) =
        (graph.ownCompletions who image.history).filter
          (fun completion => completion.event.val < state.attempt.phase) from
        List.filter_comm _ _ _, ← cutoff]
    exact restricted
  rw [aligned who active]
  exact decodeHistory_fromMode_congr setup.program mode _ _ who
    (PhaseRuntimeState.archivedHistory_own_congr state.retired _ _ who nativeWord).symm

/-- The whole saved source view is read from the real retained native image and
its original archived-prefix own word, with no supplied source-view equality. -/
theorem RecoverySourceCheckpoint.saved_view_of_retained_image
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (aligned : checkpoint.ArchivedRecall) (who : Player)
    (active : who ∉ state.entry.excluded)
    (image : ((toEventGraph setup.program).withMode mode).Config)
    (retained : state.entry.native.config.history.IsPrefix image.history)
    (saved : state.entry.native.config.cut.IsPrefix state.attempt.phase)
    (agrees : checkpoint.refs.Agrees checkpoint.source.state image.store)
    (nonempty : 0 < eventCount checkpoint.residual.tail) :
    decodeEventView? setup.program (ContextRefs.initial setup.context (outputLayout setup.program))
        (outputEmbedding setup.program).ref who (checkpoint.embedding.event ⟨0, nonempty⟩)
        ((toEventGraph setup.program).playerStore who image.store)
        (decodeHistory setup.program
          ((PhaseRuntimeState.archivedHistory state.retired
            (image.history.filter fun completion =>
              completion.event.val < state.attempt.phase)).map
            ((toEventGraph setup.program).fromModeCompletion mode)) who) =
      some (ProtocolState.observe who setup.program
        (checkpoint.residual.lift
          (ProtocolState.entry checkpoint.residual.tail checkpoint.source))) :=
  (congrArg (fun past => decodeEventView? setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputEmbedding setup.program).ref who (checkpoint.embedding.event ⟨0, nonempty⟩)
      ((toEventGraph setup.program).playerStore who image.store) past)
    (checkpoint.saved_history_of_retained_image aligned who active image retained saved)).symm.trans
      (checkpoint.views.decode_entry setup.program checkpoint.residual.tail checkpoint.refs
        checkpoint.embedding checkpoint.residual.lift nonempty who checkpoint.source
        image.store agrees)

/-- The literal full input at two actual histories determines the whole saved
source view at a matched archived checkpoint. Archive-prefix and retained-image
facts are native provenance data; no prior source-view equality is supplied. -/
theorem phase_archived_saved_source_views_eq_of_observed
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    (runtime : EventGraphRuntime ((toEventGraph setup.program).withMode mode))
    (leaks : Interaction.MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph setup.program).withMode mode)))
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (inputs : PMF ((toEventGraph setup.program).withMode mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {first second}
    (firstTrace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some first))
    (secondTrace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some second))
    (who : Player) (index : Nat)
    (left right : RetiredCommitAttempt ((toEventGraph setup.program).withMode mode))
    (firstSelected : first.execution.application.retired[index]? = some left)
    (secondSelected : second.execution.application.retired[index]? = some right)
    (observed : first.execution.observe (phaseApplication runtime leaks) who =
      second.execution.observe (phaseApplication runtime leaks) who)
    (leftSaved rightSaved : PhaseRuntimeState ((toEventGraph setup.program).withMode mode))
    (leftCheckpoint : RecoverySourceCheckpoint setup mode leftSaved)
    (rightCheckpoint : RecoverySourceCheckpoint setup mode rightSaved)
    (leftAligned : leftCheckpoint.ArchivedRecall) (rightAligned : rightCheckpoint.ArchivedRecall)
    (leftActive : who ∉ leftSaved.entry.excluded) (rightActive : who ∉ rightSaved.entry.excluded)
    (leftArchives : leftSaved.retired = first.execution.application.retired.take index)
    (rightArchives : rightSaved.retired = second.execution.application.retired.take index)
    (leftNamespace : leftSaved.attempt = left.attempt)
    (rightNamespace : rightSaved.attempt = right.attempt)
    (leftRetained : leftSaved.entry.native.config.history.IsPrefix left.state.config.history)
    (rightRetained : rightSaved.entry.native.config.history.IsPrefix right.state.config.history)
    (leftPrefix : leftSaved.entry.native.config.cut.IsPrefix leftSaved.attempt.phase)
    (rightPrefix : rightSaved.entry.native.config.cut.IsPrefix rightSaved.attempt.phase)
    (leftAgrees : leftCheckpoint.refs.Agrees leftCheckpoint.source.state left.state.config.store)
    (rightAgrees : rightCheckpoint.refs.Agrees rightCheckpoint.source.state
      right.state.config.store)
    (leftNonempty : 0 < eventCount leftCheckpoint.residual.tail)
    (rightNonempty : 0 < eventCount rightCheckpoint.residual.tail) :
    ProtocolState.observe who setup.program (leftCheckpoint.residual.lift
        (ProtocolState.entry leftCheckpoint.residual.tail leftCheckpoint.source)) =
      ProtocolState.observe who setup.program (rightCheckpoint.residual.lift
        (ProtocolState.entry rightCheckpoint.residual.tail rightCheckpoint.source)) := by
  let graph := (toEventGraph setup.program).withMode mode
  have recovered := phaseArchivedSavedObservations_eq_of_observed runtime leaks plan inputs
    horizon scheduler firstTrace secondTrace who index observed
  rw [firstSelected, secondSelected, Option.map_some, Option.map_some] at recovered
  have pair := Option.some.inj recovered
  have sameAttempt := congrArg Prod.fst pair
  have sameNative := congrArg Prod.snd pair
  have sameStore : (toEventGraph setup.program).playerStore who left.state.config.store =
      (toEventGraph setup.program).playerStore who right.state.config.store :=
    congrArg (fun observation : graph.PlayerObservation who => observation.store) sameNative
  let leftPast := PhaseRuntimeState.archivedHistory leftSaved.retired
    (left.state.config.history.filter fun completion =>
      completion.event.val < leftSaved.attempt.phase)
  let rightPast := PhaseRuntimeState.archivedHistory rightSaved.retired
    (right.state.config.history.filter fun completion =>
      completion.event.val < rightSaved.attempt.phase)
  have sameOwn : graph.ownCompletions who leftPast = graph.ownCompletions who rightPast := by
    simpa only [leftPast, rightPast, leftArchives, rightArchives, leftNamespace, rightNamespace]
      using congrArg (fun observation : graph.PlayerObservation who => observation.ownActions)
        sameNative
  have sameWord := decodeHistory_fromMode_congr setup.program mode leftPast rightPast who sameOwn
  have head : leftCheckpoint.embedding.event ⟨0, leftNonempty⟩ =
      rightCheckpoint.embedding.event ⟨0, rightNonempty⟩ := by
    apply Fin.ext
    rw [leftCheckpoint.compiled.rankEq, rightCheckpoint.compiled.rankEq]
    change leftSaved.attempt.phase + 0 = rightSaved.attempt.phase + 0
    rw [Nat.add_zero, Nat.add_zero, leftNamespace, rightNamespace]
    exact congrArg CommitAttemptId.phase sameAttempt
  have leftRead := leftCheckpoint.saved_view_of_retained_image leftAligned who leftActive
    left.state.config leftRetained leftPrefix leftAgrees leftNonempty
  have rightRead := rightCheckpoint.saved_view_of_retained_image rightAligned who rightActive
    right.state.config rightRetained rightPrefix rightAgrees rightNonempty
  have decoderEq :
      decodeEventView? setup.program
          (ContextRefs.initial setup.context (outputLayout setup.program))
          (outputEmbedding setup.program).ref who
          (leftCheckpoint.embedding.event ⟨0, leftNonempty⟩)
          ((toEventGraph setup.program).playerStore who left.state.config.store)
          (decodeHistory setup.program
            (leftPast.map ((toEventGraph setup.program).fromModeCompletion mode)) who) =
        decodeEventView? setup.program
          (ContextRefs.initial setup.context (outputLayout setup.program))
          (outputEmbedding setup.program).ref who
          (rightCheckpoint.embedding.event ⟨0, rightNonempty⟩)
          ((toEventGraph setup.program).playerStore who right.state.config.store)
          (decodeHistory setup.program
            (rightPast.map ((toEventGraph setup.program).fromModeCompletion mode)) who) := by
    rw [head, sameStore, sameWord]
  exact Option.some.inj (leftRead.symm.trans (decoderEq.trans rightRead))

end Vegas
