/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.CompiledCommitPhase
import Vegas.Pending.PhaseReadiness

/-! # Installed maximal commitment phases and source telescopes -/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ Γ Δ : SourceCtx Player L} {wholeOpen O P : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeOpen)
  (mode : EventGraph.ExecutionMode)
  (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
  {refs : ContextRefs (graphLayout whole) Γ} {revelations : Revelations Γ}
  {registry : Registry Γ}
  (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
    (block.prepend suffix))
  {refsBefore : ContextRefsBefore refs embedding} {offset : Nat}
  (compiled : CompiledSuffix whole (block.prepend suffix) refs revelations registry embedding
    refsBefore offset)

/-- At a saved source checkpoint, the installed maximal phase is exactly the
compiled nonempty commitment telescope, including its kind and both endpoints. -/
theorem compiledCommitPhase_eq_of_maximal (positive : 0 < block.length)
    (boundary : IsCommitBoundary suffix)
    (phase : RuntimePhase ((toEventGraph whole).withMode mode))
    (remaining : List (RuntimePhase ((toEventGraph whole).withMode mode)))
    (adjacent : (phase :: remaining).IsChain fun before after => before.high = after.low)
    (last : ∀ final ∈ (phase :: remaining).getLast?,
      final.high = ((toEventGraph whole).withMode mode).order.eventCount)
    (maximal : (phase :: remaining).IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (start : phase.low = offset) :
    phase = compiledCommitPhase whole mode block suffix embedding compiled positive := by
  have counted := block.eventCount_prepend suffix
  have total := compiled.countEq
  let first : Fin (eventCount (block.prepend suffix)) := ⟨0, by omega⟩
  obtain ⟨owner, payload, _member, binding⟩ :=
    block.binding_before_length suffix first positive
  have firstRank : (embedding.event first).val = offset := by
    rw [compiled.rankEq]
    exact Nat.add_zero _
  have firstBinding : ((toEventGraph whole).withMode mode).outputLayout
      (embedding.event first) = .binding owner payload :=
    (embedding.layout_eq first).trans binding
  have firstFields := phase.fields (embedding.event first) (by omega)
    (by have nonempty := phase.nonempty; omega)
  have kind : phase.kind = .commitment := by
    cases actual : phase.kind with
    | commitment => rfl
    | reveal =>
        rw [actual] at firstFields
        obtain ⟨other, layout⟩ := firstFields
        rw [firstBinding] at layout
        cases layout
    | sample =>
        rw [actual] at firstFields
        obtain ⟨other, layout⟩ := firstFields
        rw [firstBinding] at layout
        cases layout
  have lower : offset + block.length ≤ phase.high := by
    by_contra early
    let index : Fin (eventCount (block.prepend suffix)) := ⟨phase.high - offset, by omega⟩
    have atEnd : (embedding.event index).val = phase.high := by
      rw [compiled.rankEq]
      dsimp only [index]
      have nonempty := phase.nonempty
      omega
    have isPublic := (PhaseRuntimeState.phase_boundaries phase remaining adjacent last maximal).1
      kind (embedding.event index) atEnd
    obtain ⟨other, otherPayload, _member, output⟩ :=
      block.binding_before_length suffix index (by dsimp only [index]; omega)
    change (outputLayout whole (embedding.event index)).IsPublic at isPublic
    rw [embedding.layout_eq, output] at isPublic
    exact isPublic
  have upper : phase.high ≤ offset + block.length := by
    by_contra late
    have bounded := phase.bounded
    change phase.high ≤ eventCount whole at bounded
    let index : Fin (eventCount (block.prepend suffix)) := ⟨block.length, by omega⟩
    have isPublic := block.public_at_length suffix boundary index rfl
    have typed := phase.fields (embedding.event index)
      (by rw [compiled.rankEq]; dsimp only [index]; omega)
      (by rw [compiled.rankEq]; dsimp only [index]; omega)
    rw [kind] at typed
    obtain ⟨other, otherPayload, output⟩ := typed
    change outputLayout whole (embedding.event index) = _ at output
    rw [embedding.layout_eq] at output
    rw [output] at isPublic
    exact isPublic
  have finish : phase.high = offset + block.length := by omega
  cases phase with
  | mk actual low high nonempty bounded fields singleton =>
      dsimp only at kind start finish
      subst actual
      subst low
      subst high
      rfl

end Vegas
