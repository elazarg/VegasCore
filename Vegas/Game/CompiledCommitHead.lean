/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledCommitAttempt

/-! # The actual first binding of a physical commitment attempt -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeO) (mode : ExecutionMode)

/-- Continue the actual decoder from its exact one-binding prefix. The tail
embedding is the compiler's existing tail, and both the full configuration and
processed exclusion set agree with the whole decoder. -/
theorem decodeCommitAttempt_commit_tail
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (rest : SourceProgram.CommitPrefix ((name, .commitment owner payload) :: Γ)
      (insert name O) Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (.commit name owner fresh guard (rest.prepend suffix)))
    (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (entry : SourceProgram.Config Player L Γ) (excluded : Finset Player) :
    let head : SourceProgram.CommitPrefix Γ O ((name, .commitment owner payload) :: Γ)
      (insert name O) := .commit name owner fresh guard .nil
    let first := decodeCommitAttempt whole mode head (rest.prepend suffix) embedding native entry
      excluded
    let tailEmbedding := embedding.tail (rest.prepend suffix)
      (by simp only [eventCount]) (fun _ => rfl)
    let later := decodeCommitAttempt whole mode rest suffix tailEmbedding native first.1 first.2.1
    let complete := decodeCommitAttempt whole mode (.commit name owner fresh guard rest) suffix
      embedding native entry excluded
    later.1 = complete.1 ∧ later.2.1 = complete.2.1 := by
  intro head first tailEmbedding later complete
  by_cases inactive : owner ∈ excluded
  · dsimp only [later, first, head, complete, decodeCommitAttempt]
    rw [dite_eq_left inactive, dite_eq_left inactive]
    dsimp only
    exact ⟨rfl, rfl⟩
  · dsimp only [later, first, head, complete, decodeCommitAttempt]
    rw [dite_eq_right inactive, dite_eq_right inactive]
    dsimp only
    exact ⟨rfl, rfl⟩

end Vegas
