/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.CompiledAttemptExclusion
import Vegas.Game.CompiledCommitState
import Vegas.Game.CompiledCommitRegistry

/-! # Completed physical commitment intervals determine exact source attempts -/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime

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

/-- The compiled interval contains exactly the embedded source commitment slots. -/
theorem compiledCommitPhase_mem_iff (event : ((toEventGraph whole).withMode mode).EventId) :
    event ∈ (compiledCommitPhase whole mode block suffix embedding compiled positive).events ↔
      ∃ index : Fin (eventCount (block.prepend suffix)), index.val < block.length ∧
        embedding.event index = event := by
  constructor
  · intro member
    obtain ⟨lower, upper⟩ := (RuntimePhase.mem_events _ event).mp member
    change offset ≤ event.val at lower
    change event.val < offset + block.length at upper
    have total := compiled.countEq
    have counted := block.eventCount_prepend suffix
    let index : Fin (eventCount (block.prepend suffix)) := ⟨event.val - offset, by omega⟩
    refine ⟨index, by dsimp only [index]; omega, ?_⟩
    apply Fin.ext
    rw [compiled.rankEq]
    dsimp only [index]
    omega
  · rintro ⟨index, inside, rfl⟩
    apply (RuntimePhase.mem_events _ _).mpr
    change offset ≤ (embedding.event index).val ∧
      (embedding.event index).val < offset + block.length
    rw [compiled.rankEq]
    omega

/-- Public omission provenance fixes the decoder's exclusion set exactly at a
completed physical phase, with accepted unusable values left unexcluded. -/
theorem decodeCommitAttempt_excluded_eq_physical
    (physical : RecoveryState ((toEventGraph whole).withMode mode))
    (entry : SourceProgram.Config Player L Γ) (entryExcluded : Finset Player)
    (record : ExclusionEvidence offset entryExcluded physical)
    (within : physical.native.config.cut.Within offset (offset + block.length))
    (finished : (compiledCommitPhase whole mode block suffix embedding compiled positive).Finished
      physical) :
    (decodeCommitAttempt whole mode block suffix embedding physical.native entry
      entryExcluded).2.1 =
      physical.excluded := by
  let phase := compiledCommitPhase whole mode block suffix embedding compiled positive
  ext who
  rw [decodeCommitAttempt_excluded_eq, Finset.mem_union, mem_commitMissingOwners,
    record.commitment_owners phase rfl within who]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨index, inside, acting, omitted⟩
    have member := (compiledCommitPhase_mem_iff whole mode block suffix embedding compiled
      positive _).mpr ⟨index, inside, rfl⟩
    exact ⟨embedding.event index, member, finished member, omitted, acting⟩
  · rintro ⟨event, member, _completed, omitted, acting⟩
    obtain ⟨index, inside, rfl⟩ := (compiledCommitPhase_mem_iff whole mode block suffix embedding
      compiled positive event).mp member
    exact ⟨index, inside, acting, omitted⟩

/-- A physically finished interval supplies its source attempt, exact exclusion
set and typed source environment. No source-attempt existence is assumed. -/
theorem sourceAttempt_of_completed_bindings
    (physical : RecoveryState ((toEventGraph whole).withMode mode))
    (entry : SourceProgram.Config Player L Γ) (entryExcluded : Finset Player)
    (valid : physical.native.BindingInvariant)
    (receipts : BindingReceiptOrder offset entryExcluded physical.native.accepted)
    (record : ExclusionEvidence offset entryExcluded physical)
    (within : physical.native.config.cut.Within offset (offset + block.length))
    (finished : (compiledCommitPhase whole mode block suffix embedding compiled positive).Finished
      physical) (agree : refs.Agrees entry.state physical.native.config.store)
    (guards : Registry.FailureExtension entry.registry registry entry.state) :
    ∃ finalSource : SourceProgram.Config Player L Δ,
      finalSource = (decodeCommitAttempt whole mode block suffix embedding physical.native
        entry entryExcluded).1 ∧
      Nonempty (block.Attempt entry entryExcluded finalSource physical.excluded) ∧
        (commitBlockRefs whole block suffix embedding refs).Agrees finalSource.state
          physical.native.config.store ∧
        Registry.FailureExtension finalSource.registry (block.guardRegistry registry)
          finalSource.state := by
  let decoded := decodeCommitAttempt whole mode block suffix embedding physical.native entry
    entryExcluded
  have exclusion := decodeCommitAttempt_excluded_eq_physical whole mode block suffix embedding
    compiled positive physical entry entryExcluded record within finished
  refine ⟨decoded.1, rfl, ⟨exclusion ▸ decoded.2.2⟩, ?_, ?_⟩
  · apply decodeCommitAttempt_state_agrees whole mode block suffix embedding refs physical.native
      entry entryExcluded offset compiled.rankEq valid receipts agree
    intro index inside
    exact finished ((compiledCommitPhase_mem_iff whole mode block suffix embedding compiled
      positive _).mpr ⟨index, inside, rfl⟩)
  · exact decodeCommitAttempt_registry_extension whole mode block suffix embedding physical.native
      entry entryExcluded registry guards

end Vegas
