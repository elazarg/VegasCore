/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.CommitPhaseLayout
import Vegas.Compile.EventGraphSuffix
import Vegas.Pending.RuntimePhase
import Vegas.EventGraph.Sequential
import Vegas.Pending.ReactiveEventStability

/-! # Runtime phase descriptors from actual compiled source blocks -/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ Γ Δ : SourceCtx Player L} {wholeOpen O P : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeOpen)
  (mode : EventGraph.ExecutionMode)
  (block : SourceProgram.CommitPrefix Γ O Δ P)
  (suffix : SourceProgram Player L Δ P)
  {refs : ContextRefs (graphLayout whole) Γ} {revelations : Revelations Γ}
  {registry : Registry Γ}
  (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
    (block.prepend suffix))
  {refsBefore : ContextRefsBefore refs embedding} {offset : Nat}
  (compiled : CompiledSuffix whole (block.prepend suffix) refs revelations registry embedding
    refsBefore offset)

/-- The descriptor is the exact rank interval of a nonempty source commit block. -/
def compiledCommitPhase (positive : 0 < block.length) :
    RuntimePhase ((toEventGraph whole).withMode mode) where
  kind := .commitment
  low := offset
  high := offset + block.length
  nonempty := by omega
  bounded := by
    have counted := block.eventCount_prepend suffix
    have total := compiled.countEq
    change offset + block.length ≤ eventCount whole
    omega
  fields := by
    intro event lower upper
    have total := compiled.countEq
    let index : Fin (eventCount (block.prepend suffix)) := ⟨event.val - offset, by
      have counted := block.eventCount_prepend suffix
      omega⟩
    have atEvent : embedding.event index = event := by
      apply Fin.ext
      rw [compiled.rankEq]
      dsimp only [index]
      omega
    obtain ⟨owner, payload, _member, layout⟩ := block.binding_before_length suffix index (by
      dsimp only [index]
      omega)
    refine ⟨owner, payload, ?_⟩
    change outputLayout whole event = .binding owner payload
    rw [← atEvent, embedding.layout_eq]
    exact layout
  sample_singleton := by intro impossible; cases impossible

/-- A compiled phase exposes exactly its source commitment owners. -/
theorem compiledCommitPhase_owners (positive : 0 < block.length) :
    (compiledCommitPhase whole mode block suffix embedding compiled positive).owners =
      block.owners := by
  classical
  ext who
  change who ∈ (RuntimePhase.events _).biUnion
    (fun event => (((toEventGraph whole).withMode mode).actor? event).toFinset) ↔ _
  simp only [Finset.mem_biUnion, Option.mem_toFinset]
  constructor
  · rintro ⟨event, member, actor⟩
    have interval := Finset.mem_filter.mp member
    change _ ∧ (offset ≤ event.val ∧ event.val < offset + block.length) at interval
    have lower := interval.2.1
    have upper := interval.2.2
    have total := compiled.countEq
    let index : Fin (eventCount (block.prepend suffix)) := ⟨event.val - offset, by
      have counted := block.eventCount_prepend suffix
      omega⟩
    have atEvent : embedding.event index = event := by
      apply Fin.ext
      rw [compiled.rankEq]
      dsimp only [index]
      omega
    obtain ⟨owner, payload, ownerMember, layout⟩ := block.binding_before_length suffix index (by
      dsimp only [index]
      omega)
    have output : ((toEventGraph whole).withMode mode).outputLayout event =
        .binding owner payload := by
      change outputLayout whole event = _
      rw [← atEvent, embedding.layout_eq]
      exact layout
    have same := (EventGraph.actor?_of_outputLayout_binding _ output).symm.trans actor
    exact Option.some.inj same ▸ ownerMember
  · intro member
    obtain ⟨index, inside, payload, layout⟩ := (block.owner_iff_binding suffix who).mp member
    refine ⟨embedding.event index, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change offset ≤ (embedding.event index).val ∧
        (embedding.event index).val < offset + block.length
      rw [compiled.rankEq]
      omega
    · exact EventGraph.actor?_of_outputLayout_binding _
        ((embedding.layout_eq index).trans layout)

end Vegas
