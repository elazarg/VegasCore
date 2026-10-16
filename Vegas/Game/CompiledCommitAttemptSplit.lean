/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledCommitAttempt
import Vegas.Source.CommitPrefixWord

/-! # Exact prefix composition of the physical commitment decoder -/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeOpen) (mode : EventGraph.ExecutionMode)

private theorem cast_commit_head
    {Γ : SourceCtx Player L} {O : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    {first second : SourceProgram Player L ((name, .commitment owner payload) :: Γ)
      (insert name O)} (same : first = second)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (.commit name owner fresh guard first)) :
    (cast (congrArg (OutputEmbedding (inputLayout wholeΓ) (outputLayout whole))
      (congrArg (SourceProgram.commit name owner fresh guard) same)) embedding).event
        ⟨0, by simp only [eventCount]; omega⟩ =
      embedding.event ⟨0, by simp only [eventCount]; omega⟩ := by
  cases same
  rfl

private theorem cast_commit_tail
    {Γ : SourceCtx Player L} {O : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    {first second : SourceProgram Player L ((name, .commitment owner payload) :: Γ)
      (insert name O)} (same : first = second)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (.commit name owner fresh guard first)) :
    (cast (congrArg (OutputEmbedding (inputLayout wholeΓ) (outputLayout whole))
      (congrArg (SourceProgram.commit name owner fresh guard) same)) embedding).tail second
        (by simp only [eventCount]) (fun _ => rfl) =
      cast (congrArg (OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)) same)
        (embedding.tail first (by simp only [eventCount]) (fun _ => rfl)) := by
  cases same
  rfl

/-- Decoding a concatenated telescope continues from the exact configuration
and exclusion set of its actual physical prefix decoder. The suffix decoder
retains the complete registry, history and original physical missing flags. -/
theorem decodeCommitAttempt_append
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    (earlier : SourceProgram.CommitPrefix Γ O Δ P)
    (later : SourceProgram.CommitPrefix Δ P Ξ Q) (suffix : SourceProgram Player L Ξ Q)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      ((earlier.append later).prepend suffix))
    (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (entry : SourceProgram.Config Player L Γ) (excluded : Finset Player) :
    let prefixEmbedding := cast
      (congrArg (OutputEmbedding (inputLayout wholeΓ) (outputLayout whole))
        (earlier.prepend_append later suffix)) embedding
    let decodedEarlier := decodeCommitAttempt whole mode earlier (later.prepend suffix)
      prefixEmbedding native entry excluded
    let complete := decodeCommitAttempt whole mode (earlier.append later) suffix
      embedding native entry excluded
    ∃ tailEmbedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
        (later.prepend suffix),
      (decodeCommitAttempt whole mode later suffix tailEmbedding native
        decodedEarlier.1 decodedEarlier.2.1).1 = complete.1 ∧
        (decodeCommitAttempt whole mode later suffix tailEmbedding native
          decodedEarlier.1 decodedEarlier.2.1).2.1 = complete.2.1 := by
  induction earlier generalizing excluded with
  | nil => exact ⟨embedding, rfl, rfl⟩
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      let nextEmbedding := embedding.tail ((rest.append later).prepend suffix)
        (by simp only [SourceProgram.CommitPrefix.append, SourceProgram.CommitPrefix.prepend,
          eventCount]) (fun _ => rfl)
      have tail := cast_commit_tail whole fresh guard (rest.prepend_append later suffix) embedding
      have head := cast_commit_head whole fresh guard (rest.prepend_append later suffix) embedding
      by_cases inactive : owner ∈ excluded
      · dsimp only [decodeCommitAttempt, SourceProgram.CommitPrefix.append,
          SourceProgram.CommitPrefix.prepend]
        rw [dite_eq_left inactive, dite_eq_left inactive]
        rw [tail]
        exact ih later nextEmbedding (automaticCommit name owner payload entry) excluded
      · dsimp only [decodeCommitAttempt, SourceProgram.CommitPrefix.append,
          SourceProgram.CommitPrefix.prepend]
        rw [dite_eq_right inactive, dite_eq_right inactive]
        dsimp only
        rw [tail, head]
        exact ih later nextEmbedding _ _

/-- The actual earlier decoder is the middle of a genuine remaining typed
attempt ending at the whole physical decoder, with the same exclusion set. -/
theorem decodeCommitAttempt_append_attempt
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    (earlier : SourceProgram.CommitPrefix Γ O Δ P)
    (later : SourceProgram.CommitPrefix Δ P Ξ Q) (suffix : SourceProgram Player L Ξ Q)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      ((earlier.append later).prepend suffix))
    (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (entry : SourceProgram.Config Player L Γ) (excluded : Finset Player) :
    let prefixEmbedding := cast
      (congrArg (OutputEmbedding (inputLayout wholeΓ) (outputLayout whole))
        (earlier.prepend_append later suffix)) embedding
    let decodedEarlier := decodeCommitAttempt whole mode earlier (later.prepend suffix)
      prefixEmbedding native entry excluded
    let complete := decodeCommitAttempt whole mode (earlier.append later) suffix
      embedding native entry excluded
    Nonempty (later.Attempt decodedEarlier.1 decodedEarlier.2.1 complete.1 complete.2.1) := by
  intro prefixEmbedding decodedEarlier complete
  obtain ⟨tailEmbedding, sameConfig, sameExcluded⟩ :=
    decodeCommitAttempt_append whole mode earlier later suffix embedding native entry excluded
  have actual := (decodeCommitAttempt whole mode later suffix tailEmbedding native
    decodedEarlier.1 decodedEarlier.2.1).2.2
  have moved : later.Attempt decodedEarlier.1 decodedEarlier.2.1 complete.1
      (decodeCommitAttempt whole mode later suffix tailEmbedding native
        decodedEarlier.1 decodedEarlier.2.1).2.1 :=
    cast (congrArg (fun config => later.Attempt decodedEarlier.1 decodedEarlier.2.1 config
      (decodeCommitAttempt whole mode later suffix tailEmbedding native
        decodedEarlier.1 decodedEarlier.2.1).2.1) sameConfig) actual
  exact ⟨cast (congrArg (fun owners => later.Attempt decodedEarlier.1 decodedEarlier.2.1
    complete.1 owners) sameExcluded) moved⟩

end Vegas
