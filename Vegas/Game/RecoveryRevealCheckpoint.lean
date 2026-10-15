/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoverySourceCheckpoint
import Vegas.Game.RecoverySourceBoundary
import Vegas.Game.CompiledRevealTail
import Vegas.Game.CompiledViewTail
import Vegas.Game.CompiledRevealBoundary
import Vegas.Game.RevealRecoveryResidual
import Vegas.Source.CommitRecoveryPathLift

/-! # Saved source checkpoints after actual completed disclosure phases -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] in
private theorem next_phase_address {graph : Vegas.EventGraph Player L}
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph)) (generation : Nat)
    (image : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (adjacent : (phase :: remaining).IsChain fun before after => before.high = after.low)
    (last : ∀ final ∈ (phase :: remaining).getLast?, final.high = graph.order.eventCount) :
    (⟨remaining, generation, image, image, retired⟩ : PhaseRuntimeState graph).attempt.phase =
      phase.high := by
  cases remaining with
  | nil =>
      have ending := last phase (by simp only [List.getLast?_singleton, Option.mem_some_iff])
      simpa only [PhaseRuntimeState.attempt, List.head?_nil, Option.map_none, Option.getD_none]
        using ending.symm
  | cons next rest =>
      have boundary := adjacent.rel_head? (y := next) (by simp)
      simpa only [PhaseRuntimeState.attempt, List.head?_cons, Option.map_some, Option.getD_some]
        using boundary.symm

/-- Source-ordered readback of the completed native interval advances the
saved checkpoint through a genuine legal source recovery path. The hypotheses
are native reachability and existing execution invariants; no source path,
exclusion equality or typed next checkpoint is assumed. -/
theorem RecoverySourceCheckpoint.after_reveal
    {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (remaining : List (RuntimePhase ((toEventGraph setup.program).withMode mode)))
    (installed : state.phases = phase :: remaining) (kind : phase.kind = .reveal)
    (exclusion : state.ExclusionRecord) (stored : state.StoredCheckpoint)
    {inputs : ((toEventGraph setup.program).withMode mode).Inputs}
    (reachable : (phase.drain state.current).native.config.Reachable inputs)
    (ordered : (phase.drain state.current).OrderedPublicFailures phase.low state.entry.excluded)
    (finished : phase.Finished (phase.drain state.current)) :
    Nonempty (RecoverySourceCheckpoint setup mode
      (⟨remaining, state.generation, phase.drain state.current, phase.drain state.current,
        state.retired⟩ : PhaseRuntimeState ((toEventGraph setup.program).withMode mode))) := by
  let program := checkpoint.residual.tail
  let count := phase.high - phase.low
  let image := phase.drain state.current
  have low : phase.low = state.attempt.phase := by rw [PhaseRuntimeState.attempt, installed]; rfl
  have high : phase.high = state.attempt.phase + count := by
    dsimp only [count]
    have nonempty := phase.nonempty
    omega
  have member : phase ∈ state.phases.head? := by
    simp only [installed, List.head?_cons, Option.mem_some_iff]
  have sourceOrder : image.OrderedPublicFailures state.attempt.phase state.entry.excluded := by
    rw [← low]
    exact ordered
  have record : SuffixExclusionRecord state.attempt.phase state.entry.excluded image := by
    rw [← low]
    exact (exclusion.installed phase member).phase_drain phase
  have within := exclusion.frontier.positioned
  rw [installed] at within
  have prefixEnd : image.native.config.cut.IsPrefix (state.attempt.phase + count) := by
    rw [← high]
    exact phase.finished_prefix image (phase.drain_within state.current within.2) finished
  have entryAgree : checkpoint.refs.Agrees checkpoint.source.state image.native.config.store := by
    intro name cell selected
    apply (checkpoint.refs.get selected).get?_preserved state.entry.native.config.store
      image.native.config.store
      (fun field value present => phase.drain_keepsStore state.current field value
        (stored field value present))
    exact checkpoint.agrees selected
  let prefixed := checkpoint.compiled.revealPrefix_of_phase setup.program mode program
    checkpoint.refs checkpoint.source.revelations checkpoint.registry checkpoint.embedding
    checkpoint.before state.attempt.phase phase kind low count high
  obtain ⟨final, values, guards, failures, revelations, path, _legal⟩ :=
    sourceRecovery_of_completed_revealPhase setup mode program checkpoint.refs
      checkpoint.source.revelations checkpoint.registry checkpoint.embedding checkpoint.before
      state.attempt.phase checkpoint.compiled phase kind low count high image reachable
      state.entry.excluded record prefixEnd sourceOrder checkpoint.source entryAgree
      checkpoint.guards checkpoint.failures rfl checkpoint.unique
  let tail := Vegas.revealTail count program prefixed
  obtain ⟨ranks, actors, commits, owners, endpoints, automatic, history, memory, steps, menus,
    readout⟩ := revealTail_recovery count program prefixed
  let sourceInitial := setup.initialConfig setup.initialLaw.support_nonempty.choose
  have reached := CommitRecoveryState.reaches_of_lifted_nonCommit_path setup.program sourceInitial
    program checkpoint.residual.lift checkpoint.remaining checkpoint.atCommit checkpoint.step
    state.generation (ProtocolState.entry program checkpoint.source, state.entry.excluded)
    (tail.lift (ProtocolState.entry tail.tail final), image.excluded) path
  have sourceTrace := setup.recoveryTrace_of_reaches sourceInitial checkpoint.trace reached
  have adjacent := exclusion.frontier.adjacent
  have last := exclusion.frontier.last
  rw [installed] at adjacent last
  have address := next_phase_address phase remaining state.generation image state.retired
    adjacent last
  have graphTail := checkpoint.compiled.revealTailMany setup count program prefixed checkpoint.refs
    checkpoint.source.revelations checkpoint.registry checkpoint.embedding checkpoint.before
    state.attempt.phase
  have terminalTail := checkpoint.terminalAlignment.revealTailMany setup count program prefixed
    checkpoint.refs checkpoint.embedding
  refine ⟨
    { residual := ⟨tail.context, tail.names, tail.tail,
        fun point => checkpoint.residual.lift (tail.lift point)⟩
      source := final
      refs := revealTailRefs setup count program prefixed checkpoint.refs checkpoint.embedding
      registry := revealTailRegistry count program prefixed checkpoint.registry
      embedding := revealTailEmbedding setup count program prefixed checkpoint.embedding
      before := revealTailRefsBefore count program prefixed checkpoint.refs checkpoint.embedding
        checkpoint.before
      compiled := ?_
      terminalAlignment := terminalTail
      agrees := values
      guards := guards
      failures := failures
      unique := RevealPrefix.names_nodup count program prefixed checkpoint.unique
      remaining := fun point => (checkpoint.remaining _).trans (ranks point)
      actor := fun point => (checkpoint.actor _).trans (actors point)
      atCommit := fun point => (checkpoint.atCommit _).trans (commits point)
      owners := fun point => (checkpoint.owners _).trans (owners point)
      commitEnd := fun point => (checkpoint.commitEnd _).trans (endpoints point)
      automatic := fun point =>
        (congrArg checkpoint.residual.lift (automatic point)).trans (checkpoint.automatic _)
      history := fun point => (checkpoint.history _).trans (history point)
      withHistory := fun point past =>
        (congrArg checkpoint.residual.lift (memory point past)).trans (checkpoint.withHistory _ _)
      step := ?_
      menus := fun who point => (checkpoint.menus who _).trans (menus who point)
      readout := ?_
      trace := sourceTrace
      views := ProtocolViewSuffix.revealTailMany setup count program prefixed checkpoint.refs
        checkpoint.embedding checkpoint.residual.lift checkpoint.views }⟩
  · rw [address, high]
    rw [revelations]
    exact graphTail
  · intro point excluded joint
    rw [checkpoint.step, steps]
    simp only [PMF.map_comp, Function.comp_def, tail]
  · intro point
    rw [checkpoint.readout, readout, Option.map_map]
    congr 1
    funext terminal
    simp only [Function.comp_apply, cast_cast]

end Vegas
