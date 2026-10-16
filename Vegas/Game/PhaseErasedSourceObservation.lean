/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryArchivedSavedWord
import Vegas.Game.RecoveryResidualUniqueness
import Vegas.Source.CommitRecoveryErasedStep

/-! # Saved semantic source observations in retained native stores -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- An actual checkpoint is decoded from any later native store retaining its
entry fields. Empty decoded memory recovers exactly its history-erased semantic
view; no earlier private signal or remembered choice is an input to this decoder. -/
theorem RecoverySourceCheckpoint.erased_saved_view_of_kept_store
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state) (who : Player)
    (image : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    (stored : KeepsStore state.entry.native image)
    (nonempty : 0 < eventCount checkpoint.residual.tail) :
    decodeEventView? setup.program (ContextRefs.initial setup.context (outputLayout setup.program))
        (outputEmbedding setup.program).ref who (checkpoint.embedding.event ⟨0, nonempty⟩)
        ((toEventGraph setup.program).playerStore who image.config.store) [] =
      some (ProtocolView.eraseHistory who setup.program
        (ProtocolState.observe who setup.program
          (checkpoint.residual.lift
            (ProtocolState.entry checkpoint.residual.tail checkpoint.source)))) := by
  let source := { checkpoint.source with history := fun _ => [] }
  have agrees : checkpoint.refs.Agrees source.state image.config.store := by
    intro name cell selected
    apply (checkpoint.refs.get selected).get?_preserved state.entry.native.config.store
      image.config.store stored
    exact checkpoint.agrees selected
  have decoded := checkpoint.views.decode_entry setup.program checkpoint.residual.tail
    checkpoint.refs checkpoint.embedding checkpoint.residual.lift nonempty who source
    image.config.store agrees
  have erased : ProtocolView.eraseHistory who setup.program
      (ProtocolState.observe who setup.program
        (checkpoint.residual.lift
          (ProtocolState.entry checkpoint.residual.tail checkpoint.source))) =
      ProtocolState.observe who setup.program
        (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail source)) := by
    rw [ProtocolView.eraseHistory_observe, ← checkpoint.withHistory,
      ProtocolState.withHistory_entry]
  rw [erased]
  exact decoded

/-- Equal observed native images at the same source boundary determine the
actual history-erased saved source views, including after nonarchiving phases.
The two genuine source prefixes and their retired private words are arbitrary. -/
theorem RecoverySourceCheckpoint.erased_saved_views_eq_of_kept_images
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {first second : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (left : RecoverySourceCheckpoint setup mode first)
    (right : RecoverySourceCheckpoint setup mode second)
    (same : first.attempt.phase = second.attempt.phase) (who : Player)
    (leftImage rightImage : EventGraphRuntime.State
      ((toEventGraph setup.program).withMode mode))
    (leftStored : KeepsStore first.entry.native leftImage)
    (rightStored : KeepsStore second.entry.native rightImage)
    (observed : ((toEventGraph setup.program).withMode mode).playerObserve who
        leftImage.config =
      ((toEventGraph setup.program).withMode mode).playerObserve who rightImage.config)
    (leftNonempty : 0 < eventCount left.residual.tail)
    (rightNonempty : 0 < eventCount right.residual.tail) :
    ProtocolView.eraseHistory who setup.program
        (ProtocolState.observe who setup.program
          (left.residual.lift (ProtocolState.entry left.residual.tail left.source))) =
      ProtocolView.eraseHistory who setup.program
        (ProtocolState.observe who setup.program
          (right.residual.lift (ProtocolState.entry right.residual.tail right.source))) := by
  have leftDecoded := left.erased_saved_view_of_kept_store who leftImage leftStored leftNonempty
  have rightDecoded := right.erased_saved_view_of_kept_store who rightImage rightStored
    rightNonempty
  have event : left.embedding.event ⟨0, leftNonempty⟩ =
      right.embedding.event ⟨0, rightNonempty⟩ := by
    apply Fin.ext
    rw [left.compiled.rankEq, right.compiled.rankEq, same]
  have stores := congrArg (fun view :
    ((toEventGraph setup.program).withMode mode).PlayerObservation who => view.store) observed
  change (toEventGraph setup.program).playerStore who leftImage.config.store =
    (toEventGraph setup.program).playerStore who rightImage.config.store at stores
  rw [event, stores] at leftDecoded
  exact Option.some.inj (leftDecoded.symm.trans rightDecoded)

end Vegas
