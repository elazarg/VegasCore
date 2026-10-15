/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoverySourceBoundary
import Vegas.Game.CompiledCommitClosing
import Vegas.Game.CompiledCommitTail
import Vegas.Game.CompiledCommitMaximality
import Vegas.Source.CommitPhaseAutomaticAttempt
import Vegas.Source.CommitRecoveryBlockCloseLift

/-! # Saved source checkpoints after clean and exhausted physical binding phases -/

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

/-- A completed physical phase without a new owned miss saves the exact
source-ordered binding result and its initialized legal source recovery trace. -/
theorem RecoverySourceCheckpoint.after_commit_clean
    {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (committing : ProtocolState.atCommit checkpoint.residual.tail
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source) = true)
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (remaining : List (RuntimePhase ((toEventGraph setup.program).withMode mode)))
    (installed : state.phases = phase :: remaining)
    (maximal : state.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (binding : state.BindingRecord) (receipts : state.ReceiptRecord)
    (stored : state.StoredCheckpoint) (finished : phase.Finished (phase.drain state.current))
    (clean : ¬ (((phase.drain state.current).excluded \ state.entry.excluded) ∩
      phase.owners).Nonempty) :
    Nonempty (RecoverySourceCheckpoint setup mode
      (⟨remaining, state.generation, phase.drain state.current, phase.drain state.current,
        state.retired⟩ : PhaseRuntimeState ((toEventGraph setup.program).withMode mode))) ∧
      state.normalize = PhaseRuntimeState.settle remaining state.generation
        (phase.drain state.current) (phase.drain state.current) state.retired := by
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, source, refs, registry, embedding, before,
    compiled, aligned, agree, guards, failures, unique, ranks, actors, commits, owners, endpoints,
    automatic, history, memory, steps, menus, readout, sourceTrace⟩
  obtain ⟨Δ, P, suffix, block, reconstruct, boundary⟩ := commitPhase program
  subst program
  have positive : 0 < block.length := by
    cases block with
    | nil =>
        cases suffix with
        | ret => cases committing
        | sample => cases committing
        | reveal => cases committing
        | commit => cases boundary
    | commit => simp only [SourceProgram.CommitPrefix.length]; omega
  have low : phase.low = state.attempt.phase := by
    rw [PhaseRuntimeState.attempt, installed]
    rfl
  have adjacent := receipts.exclusion.frontier.adjacent
  have last := receipts.exclusion.frontier.last
  rw [installed] at adjacent last maximal
  have phaseEq := compiledCommitPhase_eq_of_maximal setup.program mode block suffix embedding
    compiled positive boundary phase remaining adjacent last maximal low
  subst phase
  let phase := compiledCommitPhase setup.program mode block suffix embedding compiled positive
  have ownerEq : phase.owners = block.owners :=
    compiledCommitPhase_owners setup.program mode block suffix embedding compiled positive
  have head : state.phases.head? = some phase := by rw [installed]; rfl
  obtain ⟨final, ⟨attempt⟩, values, finalGuards⟩ :=
    sourceAttempt_of_drained_bindingPhase setup.program mode block suffix embedding compiled
      positive state head binding.active receipts stored source agree guards finished
  have noFailure : attempt.failedOwners = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨who, failed⟩
    apply clean
    refine ⟨who, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · rwa [attempt.newly_excluded]
    · rw [ownerEq]
      exact attempt.failed_subset_owners failed
  let closed : block.Close (⟨source, state.entry.excluded, state.generation⟩ : CommitCheckpoint Γ)
      (.settled final (phase.drain state.current).excluded) := .clean attempt noFailure
  have normalized : state.normalize = PhaseRuntimeState.settle remaining state.generation
      (phase.drain state.current) (phase.drain state.current) state.retired := by
    change PhaseRuntimeState.settle state.phases state.generation state.entry state.current
      state.retired = _
    rw [installed]
    apply PhaseRuntimeState.settle_clean phase remaining state.generation state.entry state.current
      state.retired finished
    exact fun failed => clean failed.2
  let sourceInitial := setup.initialConfig setup.initialLaw.support_nonempty.choose
  have reached := closed.reaches_lift setup.program sourceInitial suffix boundary positive lift
    ranks actors (fun point who => menus who point) steps commits owners endpoints automatic
    history memory
  have reachedTrace := setup.recoveryTrace_of_reaches sourceInitial sourceTrace reached
  obtain ⟨finalEmbedding, finalBefore, finalCompiled, finalAlignment⟩ := attempt.compiledTail
    setup.program suffix refs registry embedding before state.attempt.phase compiled aligned
  obtain ⟨tailRanks, tailActors, tailCommits, tailOwners, tailEnds, tailAutomatic, tailHistory,
    tailMemory, tailSteps, tailMenus, tailReadout⟩ := block.liftPoint_recovery suffix
  have address := next_phase_address phase remaining state.generation (phase.drain state.current)
    state.retired adjacent last
  have finalFailures := attempt.preservesFailures failures
  refine ⟨?_, normalized⟩
  refine ⟨
    { residual := ⟨Δ, P, suffix, fun point => lift (block.liftPoint suffix point)⟩
      source := final
      refs := commitBlockRefs setup.program block suffix embedding refs
      registry := block.guardRegistry registry
      embedding := finalEmbedding
      before := finalBefore
      compiled := ?_
      terminalAlignment := finalAlignment
      agrees := values
      guards := finalGuards
      failures := finalFailures
      unique := block.names_nodup unique
      remaining := fun point => (ranks _).trans (tailRanks point)
      actor := fun point => (actors _).trans (tailActors point)
      atCommit := fun point => (commits _).trans (tailCommits point)
      owners := fun point => (owners _).trans (tailOwners point)
      commitEnd := fun point => (endpoints _).trans (tailEnds point)
      automatic := fun point =>
        (congrArg lift (tailAutomatic point)).trans (automatic _)
      history := fun point => (history _).trans (tailHistory point)
      withHistory := fun point past =>
        (congrArg lift (tailMemory point past)).trans (memory _ _)
      step := ?_
      menus := fun who point => (menus who _).trans (tailMenus who point)
      readout := ?_
      trace := reachedTrace }⟩
  · rw [address]
    exact finalCompiled
  · intro point excluded joint
    rw [steps, tailSteps]
    simp only [PMF.map_comp, Function.comp_def]
  · intro point
    rw [readout, tailReadout, Option.map_map]
    congr 1
    funext terminal
    simp only [Function.comp_apply, cast_cast]

/-- An actual exhausted physical phase rebuilds the saved source block with
only automatic excluded slots and preserves the retained attempted history.
No retry, source outcome, closure law or source path is supplied as a premise. -/
theorem RecoverySourceCheckpoint.after_commit_exhausted
    {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (committing : ProtocolState.atCommit checkpoint.residual.tail
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source) = true)
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (remaining : List (RuntimePhase ((toEventGraph setup.program).withMode mode)))
    (installed : state.phases = phase :: remaining)
    (maximal : state.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (binding : state.BindingRecord) (receipts : state.ReceiptRecord)
    (stored : state.StoredCheckpoint) (finished : phase.Finished (phase.drain state.current))
    (missed : (((phase.drain state.current).excluded \ state.entry.excluded) ∩
      phase.owners).Nonempty)
    (exhausted : ¬ (phase.owners \ (phase.drain state.current).excluded).Nonempty) :
    let image := phase.drain state.current
    let rebuilt := phase.drain (PhaseRuntimeState.restore state.entry image)
    let archive := state.retired ++ [⟨⟨phase.low, state.generation⟩, image.native⟩]
    Nonempty (RecoverySourceCheckpoint setup mode
      (⟨remaining, state.generation, rebuilt, rebuilt, archive⟩ :
        PhaseRuntimeState ((toEventGraph setup.program).withMode mode))) ∧
      state.normalize = PhaseRuntimeState.settle remaining state.generation rebuilt rebuilt
        archive := by
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, source, refs, registry, embedding, before,
    compiled, aligned, agree, guards, failures, unique, ranks, actors, commits, owners, endpoints,
    automatic, history, memory, steps, menus, readout, sourceTrace⟩
  obtain ⟨Δ, P, suffix, block, reconstruct, boundary⟩ := commitPhase program
  subst program
  have positive : 0 < block.length := by
    cases block with
    | nil =>
        cases suffix with
        | ret => cases committing
        | sample => cases committing
        | reveal => cases committing
        | commit => cases boundary
    | commit => simp only [SourceProgram.CommitPrefix.length]; omega
  have low : phase.low = state.attempt.phase := by
    rw [PhaseRuntimeState.attempt, installed]
    rfl
  have adjacent := receipts.exclusion.frontier.adjacent
  have last := receipts.exclusion.frontier.last
  rw [installed] at adjacent last maximal
  have phaseEq := compiledCommitPhase_eq_of_maximal setup.program mode block suffix embedding
    compiled positive boundary phase remaining adjacent last maximal low
  subst phase
  let phase := compiledCommitPhase setup.program mode block suffix embedding compiled positive
  have ownerEq : phase.owners = block.owners :=
    compiledCommitPhase_owners setup.program mode block suffix embedding compiled positive
  have missedSource : ((phase.drain state.current).excluded \ state.entry.excluded).Nonempty := by
    obtain ⟨who, member⟩ := missed
    exact ⟨who, (Finset.mem_inter.mp member).1⟩
  have noSource : ¬ (block.owners \ (phase.drain state.current).excluded).Nonempty := by
    rwa [← ownerEq]
  obtain ⟨final, closed, values, finalGuards, normalized⟩ :=
    sourceClose_of_exhausted_bindingPhase setup.program mode block suffix embedding compiled
      positive state remaining installed binding receipts stored source agree guards finished
      missedSource noSource
  let image := phase.drain state.current
  let rebuilt := phase.drain (PhaseRuntimeState.restore state.entry image)
  let restoredSource := { source with history := final.history }
  have allSource : block.owners ⊆ image.excluded := by
    intro who member
    by_contra outside
    exact noSource ⟨who, Finset.mem_sdiff.mpr ⟨member, outside⟩⟩
  let automaticAttempt := block.automaticAttempt restoredSource image.excluded allSource
  obtain ⟨finalEmbedding, finalBefore, finalCompiled, finalAlignment⟩ :=
    automaticAttempt.compiledTail setup.program suffix refs registry embedding before
      state.attempt.phase compiled aligned
  obtain ⟨tailRanks, tailActors, tailCommits, tailOwners, tailEnds, tailAutomatic, tailHistory,
    tailMemory, tailSteps, tailMenus, tailReadout⟩ := block.liftPoint_recovery suffix
  let sourceInitial := setup.initialConfig setup.initialLaw.support_nonempty.choose
  have reached := closed.reaches_lift setup.program sourceInitial suffix boundary positive lift
    ranks actors (fun point who => menus who point) steps commits owners endpoints automatic
    history memory
  have reachedTrace := setup.recoveryTrace_of_reaches sourceInitial sourceTrace reached
  have address := next_phase_address phase remaining state.generation rebuilt
    (state.retired ++ [⟨⟨phase.low, state.generation⟩, image.native⟩]) adjacent last
  have finalFailures := automaticAttempt.preservesFailures failures
  have finalTrace : Nonempty (setup.commitRecoveryProtocol.Trace
      (some (CommitRecoveryState.atPoint
        (lift (block.liftPoint suffix
          (ProtocolState.entry suffix (block.automatic restoredSource))))
        rebuilt.excluded state.generation))) := by
    rw [show rebuilt.excluded = image.excluded from phase.drain_excluded _]
    exact reachedTrace
  refine ⟨?_, normalized⟩
  refine ⟨
    { residual := ⟨Δ, P, suffix, fun point => lift (block.liftPoint suffix point)⟩
      source := block.automatic restoredSource
      refs := commitBlockRefs setup.program block suffix embedding refs
      registry := block.guardRegistry registry
      embedding := finalEmbedding
      before := finalBefore
      compiled := ?_
      terminalAlignment := finalAlignment
      agrees := values
      guards := finalGuards
      failures := finalFailures
      unique := block.names_nodup unique
      remaining := fun point => (ranks _).trans (tailRanks point)
      actor := fun point => (actors _).trans (tailActors point)
      atCommit := fun point => (commits _).trans (tailCommits point)
      owners := fun point => (owners _).trans (tailOwners point)
      commitEnd := fun point => (endpoints _).trans (tailEnds point)
      automatic := fun point =>
        (congrArg lift (tailAutomatic point)).trans (automatic _)
      history := fun point => (history _).trans (tailHistory point)
      withHistory := fun point past =>
        (congrArg lift (tailMemory point past)).trans (memory _ _)
      step := ?_
      menus := fun who point => (menus who _).trans (tailMenus who point)
      readout := ?_
      trace := finalTrace }⟩
  · rw [address]
    exact finalCompiled
  · intro point excluded joint
    rw [steps, tailSteps]
    simp only [PMF.map_comp, Function.comp_def]
  · intro point
    rw [readout, tailReadout, Option.map_map]
    congr 1
    funext terminal
    simp only [Function.comp_apply, cast_cast]

end Vegas
