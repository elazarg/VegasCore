/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledPhaseReadback
import Vegas.Source.CommitPhaseAutomatic
import Interaction.ReactiveRounds

/-! # Typed source closure of actual physical commitment phases -/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ Γ Δ : SourceCtx Player L} {wholeOpen O P : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeOpen) (mode : EventGraph.ExecutionMode)
  (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
  {refs : ContextRefs (graphLayout whole) Γ} {revelations : Revelations Γ}
  {registry : Registry Γ}
  (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
    (block.prepend suffix)) {refsBefore : ContextRefsBefore refs embedding} {offset : Nat}
  (compiled : CompiledSuffix whole (block.prepend suffix) refs revelations registry embedding
    refsBefore offset) (positive : 0 < block.length)


variable (state : PhaseRuntimeState ((toEventGraph whole).withMode mode))
  (remaining : List (RuntimePhase ((toEventGraph whole).withMode mode)))
  (installed : state.phases =
    compiledCommitPhase whole mode block suffix embedding compiled positive :: remaining)
  (binding : state.BindingRecord) (receipts : state.ReceiptRecord)
  (stored : state.StoredCheckpoint) (entry : SourceProgram.Config Player L Γ)
  (agree : refs.Agrees entry.state state.entry.native.config.store)
  (guards : Registry.FailureExtension entry.registry registry entry.state)
  (finished :
    (compiledCommitPhase whole mode block suffix embedding compiled positive).Finished
      ((compiledCommitPhase whole mode block suffix embedding compiled positive).drain
        state.current))

include installed binding receipts stored agree guards finished

/-- Exhaustion rebuilds exactly the automatic source block from the saved
semantic checkpoint. The actual physical dispatcher advances without a retry. -/
theorem sourceClose_of_exhausted_bindingPhase
    (missed : (((compiledCommitPhase whole mode block suffix embedding compiled positive).drain
      state.current).excluded \ state.entry.excluded).Nonempty)
    (exhausted : ¬ (block.owners \
      ((compiledCommitPhase whole mode block suffix embedding compiled positive).drain
        state.current).excluded).Nonempty) :
    let phase := compiledCommitPhase whole mode block suffix embedding compiled positive
    let image := phase.drain state.current
    let rebuilt := phase.drain (PhaseRuntimeState.restore state.entry image)
    let checkpoint : CommitCheckpoint Γ := ⟨entry, state.entry.excluded, state.generation⟩
    ∃ finalSource : SourceProgram.Config Player L Δ,
      finalSource = (decodeCommitAttempt whole mode block suffix embedding image.native entry
        state.entry.excluded).1 ∧
      block.Close checkpoint
        (.settled (block.automatic { entry with history := finalSource.history }) image.excluded) ∧
      (commitBlockRefs whole block suffix embedding refs).Agrees
        (block.automatic { entry with history := finalSource.history }).state
        rebuilt.native.config.store ∧
      Registry.FailureExtension
        (block.automatic { entry with history := finalSource.history }).registry
        (block.guardRegistry registry)
        (block.automatic { entry with history := finalSource.history }).state ∧
      state.normalize = PhaseRuntimeState.settle remaining state.generation rebuilt rebuilt
        (state.retired ++ [⟨⟨phase.low, state.generation⟩, image.native⟩]) := by
  let phase := compiledCommitPhase whole mode block suffix embedding compiled positive
  let image := phase.drain state.current
  let restored := PhaseRuntimeState.restore state.entry image
  let rebuilt := phase.drain restored
  have head : state.phases.head? = some phase := by rw [installed]; rfl
  obtain ⟨finalSource, finalSourceEq, ⟨attempt⟩, _values, _registry⟩ :=
    sourceAttempt_of_drained_bindingPhase whole mode block suffix embedding compiled positive
      state head binding.active receipts stored entry agree guards finished
  have failed : attempt.failedOwners.Nonempty := by rwa [← attempt.newly_excluded]
  have allSource : block.owners ⊆ image.excluded := by
    intro who member
    by_contra outside
    exact exhausted ⟨who, Finset.mem_sdiff.mpr ⟨member, outside⟩⟩
  have owners : phase.owners = block.owners :=
    compiledCommitPhase_owners whole mode block suffix embedding compiled positive
  have allPhysical : phase.owners ⊆ restored.excluded := by
    change phase.owners ⊆ image.excluded
    rw [owners]
    exact allSource
  have position := receipts.exclusion.frontier.positioned
  rw [installed] at position
  have saved : state.entry.native.config.cut.IsPrefix phase.low := position.1
  have within : restored.native.config.cut.Within phase.low phase.high :=
    saved.within phase.nonempty.le
  have restoredReceipts : restored.native.ReceiptsComplete := by
    intro event candidate accepted
    exact receipts.exclusion.saved event candidate accepted
  have fixed : KeepsFixedCandidates state.entry.native image.native := by
    intro candidate known
    change (phase.drain state.current).native.candidates.lookup candidate = _
    rw [(phase.drain_tables state.current).2.1]
    exact binding.fixed candidate known
  have restoredValid : restored.native.BindingInvariant :=
    PhaseRuntimeState.restore_bindingInvariant state.entry image binding.saved fixed
  have rebuiltFinished : phase.Finished rebuilt :=
    phase.drain_finished_of_excluded restored within rfl allPhysical
  let restoredSource := { entry with history := finalSource.history }
  have restoredAgree : refs.Agrees restoredSource.state rebuilt.native.config.store := by
    intro name cell source
    exact (refs.get source).get?_preserved restored.native.config.store _
      (phase.drain_keepsStore restored) _ (agree source)
  obtain ⟨automaticSource, _automaticSourceEq, ⟨automaticAttempt⟩, automaticValues,
    automaticGuards⟩ :=
    sourceAttempt_of_completed_bindings whole mode block suffix embedding compiled positive
      rebuilt restoredSource image.excluded (phase.drain_bindingInvariant restored restoredValid)
      ((BindingReceiptOrder.of_prefix restoredReceipts saved).congr
        (phase.drain_tables restored).1)
      ((SuffixExclusionRecord.of_prefix restoredReceipts saved rfl).phase_drain phase)
      (phase.drain_within restored within) rebuiltFinished restoredAgree guards
  have automaticEq := (automaticAttempt.eq_automatic_of_owners allSource).1
  refine ⟨finalSource, finalSourceEq, .exhausted attempt failed allSource, ?_, ?_, ?_⟩
  · intro name cell source
    simpa only [automaticEq] using automaticValues source
  · simpa only [automaticEq] using automaticGuards
  · change PhaseRuntimeState.settle state.phases state.generation state.entry state.current
      state.retired = _
    rw [installed]
    apply PhaseRuntimeState.settle_exhausted phase remaining state.generation state.entry
      state.current state.retired finished rfl
    · obtain ⟨who, member⟩ := failed
      refine ⟨who, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · rwa [attempt.newly_excluded]
      · rw [owners]
        exact attempt.failed_subset_owners member
    · simpa only [owners] using exhausted

end Vegas
