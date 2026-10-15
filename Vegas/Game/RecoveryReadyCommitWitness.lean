/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryCommitPrefixWitness
import Vegas.Game.CommitPrefixReadyRecall
import Vegas.Compile.CommitPrefixAtEvent

/-! # Actual source histories realizing clear ready commitment views -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Readiness identifies the filled source history with actual native own recall,
so the typed source trace requires no supplied filled-history equation. -/
theorem RecoverySourceCheckpoint.filled_prefix_history_of_ready
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    {Δ : SourceCtx Player L} {P : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} (fresh : name ∉ Δ.map Prod.fst)
    (guard : SourceGuard L Δ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Δ) (insert name P))
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (reconstruct : earlier.prepend (.commit name owner fresh guard next) = checkpoint.residual.tail)
    (clear : state.entry.excluded = ∅)
    (selected : Fin (eventCount checkpoint.residual.tail))
    (atEnd : selected.val = earlier.length)
    (ready : state.current.native.config.cut.Ready (checkpoint.embedding.event selected))
    (acting : (serviceGraph setup mode).actor? (checkpoint.embedding.event selected) = some owner)
    (valid : state.current.native.BindingInvariant) {inputs}
    (reachable : state.current.native.config.Reachable inputs)
    (retained : state.HistoryCheckpoint)
    (saved : state.entry.native.config.cut.IsPrefix state.attempt.phase) :
    let embedding := cast (congrArg
      (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) reconstruct.symm) checkpoint.embedding
    (fillCommitPrefix setup.program earlier (.commit name owner fresh guard next) embedding
      state.current.native.config.store checkpoint.source).history owner =
        decodeHistory setup.program (state.current.native.config.history.map
          (setup.eventGraph.fromModeCompletion mode)) owner := by
  have history := congrFun (checkpoint.historyAlignment clear) owner
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, entry, refs, registry, embedding, before,
    compiled, terminalAlignment, agrees, guards, failures, unique, ranks, actors, commits, owners,
    endpoints, automatic, histories, memories, steps, menus, readout, initialized, views,
    _savedHistory, _origin⟩
  dsimp only at *
  change SourceProgram.Config Player L Γ at entry
  change OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program
    at embedding
  change SourceProgram.CommitPrefix Γ O Δ P at earlier
  change Fin (eventCount program) at selected
  change earlier.prepend (.commit name owner fresh guard next) = program at reconstruct
  subst program
  exact fillCommitPrefix_history_of_ready setup.program mode earlier
    (.commit name owner fresh guard next) embedding state.attempt.phase compiled.rankEq
    state.entry.native state.current.native entry valid reachable retained saved owner
    history views.actionEq selected atEnd ready acting

/-- The actual source trace uses the filled own history derived from readiness. -/
theorem RecoverySourceCheckpoint.filled_prefix_trace_of_ready
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    {Δ : SourceCtx Player L} {P : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} (fresh : name ∉ Δ.map Prod.fst)
    (guard : SourceGuard L Δ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Δ) (insert name P))
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (reconstruct : earlier.prepend (.commit name owner fresh guard next) = checkpoint.residual.tail)
    (clear : state.entry.excluded = ∅) (stored : state.StoredCheckpoint)
    (selected : Fin (eventCount checkpoint.residual.tail))
    (atEnd : selected.val = earlier.length)
    (ready : state.current.native.config.cut.Ready (checkpoint.embedding.event selected))
    (acting : (serviceGraph setup mode).actor? (checkpoint.embedding.event selected) = some owner)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout
      (checkpoint.embedding.event selected)).IsPublication)
    (valid : state.current.native.BindingInvariant) {inputs}
    (reachable : state.current.native.config.Reachable inputs)
    (retained : state.HistoryCheckpoint)
    (saved : state.entry.native.config.cut.IsPrefix state.attempt.phase) :
    ∃ (source : CommitRecoveryState setup.program)
      (_trace : setup.commitRecoveryProtocol.Trace (some source)),
      source.excluded = ∅ ∧ source.generation = state.generation ∧
      ProtocolState.actor setup.program source.point = some owner ∧
      decodeEventView? setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (outputEmbedding setup.program).ref owner (checkpoint.embedding.event selected)
        ((serviceGraph setup mode).playerStore owner state.current.native.config.store)
        (decodeHistory setup.program (state.current.native.config.history.map
          (setup.eventGraph.fromModeCompletion mode)) owner) =
          some (ProtocolState.observe owner setup.program source.point) := by
  exact checkpoint.filled_prefix_trace fresh guard next earlier reconstruct clear stored selected
    atEnd ready acting notPublication _ (checkpoint.filled_prefix_history_of_ready fresh guard next
      earlier reconstruct clear selected atEnd ready acting valid reachable retained saved)

/-- The current phase's actual layouts determine the typed earlier prefix.
Foreign holes need no feasibility premise and no maximal-block decomposition
is supplied by the caller. -/
theorem RecoverySourceCheckpoint.ready_binding_trace
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (frontier : state.Frontier) (stored : state.StoredCheckpoint)
    (retained : state.HistoryCheckpoint)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : state.phases = phase :: remaining) (kind : phase.kind = .commitment)
    (event : (serviceGraph setup mode).EventId) (inside : event ∈ phase.events)
    (ready : state.current.native.config.cut.Ready event)
    (who : Player) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (clear : state.entry.excluded = ∅) (valid : state.current.native.BindingInvariant) {inputs}
    (reachable : state.current.native.config.Reachable inputs) :
    ∃ (source : CommitRecoveryState setup.program)
      (_trace : setup.commitRecoveryProtocol.Trace (some source)),
      source.excluded = ∅ ∧ source.generation = state.generation ∧
      ProtocolState.actor setup.program source.point = some who ∧
      decodeEventView? setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (outputEmbedding setup.program).ref who event
        ((serviceGraph setup mode).playerStore who state.current.native.config.store)
        (decodeHistory setup.program (state.current.native.config.history.map
          (setup.eventGraph.fromModeCompletion mode)) who) =
          some (ProtocolState.observe who setup.program source.point) := by
  obtain ⟨selected, selectedEq⟩ := checkpoint.native_event_index frontier event ready
  have low : state.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some]
  have positioned := frontier.positioned
  rw [installed] at positioned
  have saved : state.entry.native.config.cut.IsPrefix state.attempt.phase := by
    rw [low]
    exact positioned.1
  have interval := (phase.mem_events event).mp inside
  have bindings : ∀ index : Fin (eventCount checkpoint.residual.tail),
      index.val ≤ selected.val →
        ∃ owner value, outputLayout checkpoint.residual.tail index = .binding owner value := by
    intro index before
    have typed := phase.fields (checkpoint.embedding.event index)
      (by rw [checkpoint.compiled.rankEq, low]; omega)
      (by have rank := checkpoint.compiled.rankEq selected
          rw [selectedEq, low] at rank
          rw [checkpoint.compiled.rankEq, low]; omega)
    rw [kind] at typed
    obtain ⟨owner, value, layout⟩ := typed
    exact ⟨owner, value, (checkpoint.embedding.layout_eq index).symm.trans layout⟩
  have layout : outputLayout checkpoint.residual.tail selected = .binding who payload :=
    (checkpoint.embedding.layout_eq selected).symm.trans (selectedEq.symm ▸ binding)
  obtain ⟨Δ, P, name, fresh, guard, next, earlier, atEnd, reconstruct⟩ :=
    exists_commitPrefix_at_binding checkpoint.residual.tail selected who payload bindings layout
  have acting : (serviceGraph setup mode).actor? event = some who :=
    EventGraph.actor?_of_outputLayout_binding _ binding
  have notPublication : ¬ ((serviceGraph setup mode).outputLayout event).IsPublication := by
    rw [binding]
    exact id
  simpa only [selectedEq] using checkpoint.filled_prefix_trace_of_ready fresh guard next earlier
    reconstruct clear stored selected atEnd.symm (selectedEq.symm ▸ ready)
    (selectedEq.symm ▸ acting)
    (selectedEq.symm ▸ notPublication) valid reachable retained saved

end Vegas
