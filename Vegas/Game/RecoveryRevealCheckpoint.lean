/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoverySourceCheckpoint
import Vegas.Game.CompiledRevealTail
import Vegas.Game.CompiledViewTail
import Vegas.Game.CompiledRevealBoundary
import Vegas.Pending.PhaseHistoryCheckpoint
import Vegas.Game.RevealRecoveryResidual
import Vegas.Source.CommitRecoveryNonCommitIntended
import Vegas.Game.PhaseProposalReplayPath
import GameTheory.Protocol.Backward

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
    (remembered : state.HistoryCheckpoint)
    {inputs : ((toEventGraph setup.program).withMode mode).Inputs}
    (reachable : (phase.drain state.current).native.config.Reachable inputs)
    (ordered : (phase.drain state.current).OrderedPublicFailures phase.low state.entry.excluded)
    (finished : phase.Finished (phase.drain state.current)) :
    ∃ next : RecoverySourceCheckpoint setup mode
      (⟨remaining, state.generation, phase.drain state.current, phase.drain state.current,
        state.retired⟩ : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)),
      (∃ fuel : Nat,
        setup.commitRecoveryProtocol.ReachesWithin fuel
          ⟨_, checkpoint.trace⟩ ⟨_, next.trace⟩) ∧
      Relation.ReflTransGen
        (NativePublicSourceStep (phase.drain state.current).native 0 setup.program)
        (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source),
          state.entry.excluded)
        (next.residual.lift (ProtocolState.entry next.residual.tail next.source),
          (phase.drain state.current).excluded) ∧
      (∃ states : List (ProtocolState setup.program × Finset Player),
        ((checkpoint.residual.lift
          (ProtocolState.entry checkpoint.residual.tail checkpoint.source),
          state.entry.excluded) :: states).IsChain
            (NativePublicSourceStep (phase.drain state.current).native 0 setup.program) ∧
        ((checkpoint.residual.lift
          (ProtocolState.entry checkpoint.residual.tail checkpoint.source),
          state.entry.excluded) :: states).getLast (List.cons_ne_nil _ _) =
          (next.residual.lift (ProtocolState.entry next.residual.tail next.source),
            (phase.drain state.current).excluded) ∧
        setup.recoveryAddressWord next.trace = setup.recoveryAddressWord checkpoint.trace ++
          states.map (fun point =>
            (CommitRecoveryState.atPoint point.1 point.2 state.generation).publicAddress)) ∧
      (∀ who, who ∉ (phase.drain state.current).excluded →
        next.source.history who = checkpoint.source.history who ++
          (decodeHistory setup.program ((phase.drain state.current).native.config.history.map
            ((toEventGraph setup.program).fromModeCompletion mode)) who).drop
              (decodeHistory setup.program (state.entry.native.config.history.map
                ((toEventGraph setup.program).fromModeCompletion mode)) who).length) ∧
      ((phase.drain state.current).excluded = ∅ →
      ProtocolState.Intended setup.program (checkpoint.residual.lift
        (ProtocolState.entry checkpoint.residual.tail checkpoint.source)) →
      ProtocolState.Intended setup.program (next.residual.lift
        (ProtocolState.entry next.residual.tail next.source))) ∧
      NativeSourceReplayExtension setup (phase.drain state.current).native state.generation
        checkpoint.trace next.trace := by
  let priorTrace := checkpoint.trace
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
  obtain ⟨final, values, guards, failures, revelations, path, _legal, word⟩ :=
    sourceRecovery_of_completed_revealPhase setup mode program checkpoint.refs
      checkpoint.source.revelations checkpoint.registry checkpoint.embedding checkpoint.before
      state.attempt.phase checkpoint.compiled phase kind low count high image reachable
      state.entry.excluded record prefixEnd sourceOrder checkpoint.source entryAgree
      checkpoint.guards checkpoint.failures rfl checkpoint.unique
  let tail := Vegas.revealTail count program prefixed
  obtain ⟨ranks, actors, commits, owners, endpoints, automatic, history, memory, steps, menus,
    readout⟩ := revealTail_recovery count program prefixed
  let sourceInitial := setup.initialConfig setup.initialLaw.support_nonempty.choose
  have publicPath : Relation.ReflTransGen
      (NativePublicSourceStep image.native 0 setup.program)
      (checkpoint.residual.lift (ProtocolState.entry program checkpoint.source),
        state.entry.excluded)
      (checkpoint.residual.lift (tail.lift (ProtocolState.entry tail.tail final)),
        image.excluded) := by
    apply Relation.ReflTransGen.lift
      (fun point : ProtocolState program × Finset Player =>
        (checkpoint.residual.lift point.1, point.2)) (fun left right moved => ?_) _ _ path
    obtain ⟨⟨running, notCommit, joint, supported⟩, update, readback,
      selectedJoint, selectedSupport, disclosure⟩ := moved
    refine ⟨⟨?_, ?_, joint, ?_⟩, ?_, ?_, selectedJoint, ?_, ?_⟩
    · intro stopped
      apply running
      apply (ProtocolState.remaining_zero_iff_terminal program left.1).mp
      rw [← checkpoint.remaining left.1]
      exact (ProtocolState.remaining_zero_iff_terminal setup.program _).mpr stopped
    · exact (checkpoint.atCommit left.1).trans notCommit
    · rw [checkpoint.step]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨right, supported, rfl⟩
    · intro selected ranked
      apply update selected ?_
      have count := checkpoint.compiled.countEq
      simp only [eventCount_eq_instructionCount] at count
      have bounded := ProtocolState.remaining_le_instructionCount program left.1
      rw [checkpoint.remaining] at ranked
      simp only [Nat.zero_add] at ranked
      dsimp only [program] at bounded ⊢
      omega
    · exact NativeProposalReadback.lift checkpoint.origin image.native 0 state.attempt.phase
        (by
          have count := checkpoint.compiled.countEq
          simp only [eventCount_eq_instructionCount] at count
          omega) left.1 readback
    · rw [checkpoint.step]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨right, selectedSupport, rfl⟩
    · exact NativeDisclosureReadback.lift checkpoint.origin image.native 0 state.attempt.phase
        (by
          have count := checkpoint.compiled.countEq
          simp only [eventCount_eq_instructionCount] at count
          omega) left.1 left.2 selectedJoint disclosure
  have rawPath := Relation.ReflTransGen.mono (fun _ _ moved => moved.1) _ _ path
  obtain ⟨sourceTrace, states, joints, events, chain, ending, reachedPrefix, _length, _word,
    numeric, replaySteps, replayAnnotations, eventCount, replayCursors⟩ :=
    native_public_path_history setup image.native sourceInitial state.generation _ _ publicPath
      priorTrace
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
        checkpoint.embedding checkpoint.residual.lift checkpoint.views
      origin := checkpoint.origin.compose
        (revealTail_protocolSuffix count program prefixed)
      historyAlignment := ?_ }, ?_, publicPath, ⟨states, chain, ending, numeric⟩, ?_, ?_, ?_⟩
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
  · intro clear
    have oldClear : state.entry.excluded = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro who member
      have excluded := (record.excluded who).mpr (Or.inl member)
      rw [clear] at excluded
      exact Finset.notMem_empty _ excluded
    have saved : state.entry.native.config.cut.IsPrefix state.attempt.phase := by
      rw [← low]
      exact within.1
    funext who
    exact RecordedSourceHistory.native_history setup.program mode
      state.entry.native.config image.native.config state.attempt.phase count
      checkpoint.source.history final.history image.excluded (word checkpoint.views.actionEq)
      reachable (remembered.trans (phase.drain_history_prefix state.current)) saved prefixEnd
      (fun owner _survives => congrFun (checkpoint.historyAlignment oldClear) owner) who
      (by rw [clear]; exact Finset.notMem_empty _)
  · exact ⟨joints.length, reachedPrefix⟩
  · intro who active
    have saved : state.entry.native.config.cut.IsPrefix state.attempt.phase := by
      rw [← low]
      exact within.1
    exact RecordedSourceHistory.native_history_extension setup.program mode
      state.entry.native.config image.native.config state.attempt.phase count
      checkpoint.source.history final.history image.excluded (word checkpoint.views.actionEq)
      reachable (remembered.trans (phase.drain_history_prefix state.current)) saved prefixEnd
      who active
  · intro clear intended
    exact checkpoint.origin.intended_of_clear_nonCommit_path _ _ rawPath intended clear
  · refine ⟨events, _, chain, rfl, replaySteps, replayAnnotations, ?_, ?_⟩
    · change events.length = sourceTrace.length - checkpoint.trace.length
      dsimp only [priorTrace] at _length
      omega
    · simpa only [Option.map_some, CommitRecoveryState.atPoint] using replayCursors

end Vegas
