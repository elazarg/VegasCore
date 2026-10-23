/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitAttemptObservation
import Vegas.Source.CommitPrefixWord
import Vegas.Source.ProtocolSuffix

/-! # Actual commitment attempt prefixes and remembered source ranks -/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolView

/-- The existing rank projection at zero reads precisely the suffix entry view. -/
theorem atRank_zero_of_entryView {Γ : SourceCtx Player L} {O : Finset VarId}
    (who : Player) (program : SourceProgram Player L Γ O) (view : ProtocolView who program)
    (entry : Config Player L Γ) (same : entryView who program view = entry.view who) :
    atRank who program 0 view =
      some (ProtocolState.observe who program (ProtocolState.entry program entry)) := by
  cases program with
  | ret payoffs => exact congrArg some same
  | sample name fresh law next =>
      exact congrArg (fun prior => some (Sum.inl prior)) same
  | commit name owner fresh guard next =>
      exact congrArg (fun prior => some (Sum.inl prior)) same
  | reveal published owner name fresh source unresolved next =>
      exact congrArg (fun prior => some (Sum.inl prior)) same

end ProtocolView

namespace CommitPrefix

omit [IExpr.ResultTypes L] in
/-- Split a real typed attempt at a chosen static commitment prefix. Both
pieces retain the actual omissions, exclusions and original failed typed results. -/
theorem Attempt.split {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    (earlier : CommitPrefix Γ O Δ P) (later : CommitPrefix Δ P Ξ Q)
    {entry : Config Player L Γ} {excluded : Finset Player}
    {finished : Config Player L Ξ} {after : Finset Player}
    (attempt : (earlier.append later).Attempt entry excluded finished after) :
    ∃ (middle : Config Player L Δ) (owners : Finset Player),
      Nonempty (earlier.Attempt entry excluded middle owners) ∧
        Nonempty (later.Attempt middle owners finished after) := by
  induction earlier generalizing excluded with
  | nil => exact ⟨entry, excluded, ⟨.nil entry excluded⟩, ⟨attempt⟩⟩
  | commit name owner fresh guard rest ih =>
      cases attempt with
      | active active choice missed missingFailure remaining =>
          obtain ⟨middle, owners, ⟨first⟩, ⟨second⟩⟩ := ih later remaining
          exact ⟨middle, owners, ⟨.active active choice missed missingFailure first⟩, ⟨second⟩⟩
      | excluded inactive remaining =>
          obtain ⟨middle, owners, ⟨first⟩, ⟨second⟩⟩ := ih later remaining
          exact ⟨middle, owners, ⟨.excluded inactive first⟩, ⟨second⟩⟩

/-- A surviving owner's observation at any actual internal attempt boundary
is recovered by the existing source rank projection of its final observation. -/
theorem Attempt.atRank_lift {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    (earlier : CommitPrefix Γ O Δ P) {later : CommitPrefix Δ P Ξ Q}
    {entry : Config Player L Δ} {excluded : Finset Player}
    {finished : Config Player L Ξ} {after : Finset Player}
    (attempt : later.Attempt entry excluded finished after)
    (suffix : SourceProgram Player L Ξ Q) (who : Player) (survives : who ∉ after) :
    ProtocolView.atRank who (earlier.prepend (later.prepend suffix)) earlier.length
        (ProtocolState.observe who (earlier.prepend (later.prepend suffix))
          (earlier.liftPoint (later.prepend suffix)
            (later.liftPoint suffix (ProtocolState.entry suffix finished)))) =
      some (ProtocolState.observe who (earlier.prepend (later.prepend suffix))
        (earlier.liftPoint (later.prepend suffix)
          (ProtocolState.entry (later.prepend suffix) entry))) := by
  induction earlier with
  | nil =>
      exact ProtocolView.atRank_zero_of_entryView who (later.prepend suffix) _ entry
        (attempt.entryView suffix who survives)
  | commit name owner fresh guard rest ih =>
      change (ProtocolView.atRank who (rest.prepend (later.prepend suffix)) rest.length
        (ProtocolState.observe who (rest.prepend (later.prepend suffix))
          (rest.liftPoint (later.prepend suffix)
            (later.liftPoint suffix (ProtocolState.entry suffix finished))))).map Sum.inr = _
      rw [ih attempt]
      rfl

end CommitPrefix

namespace ProtocolSuffix

/-- An authentic residual suffix consumes only original source instructions. -/
theorem instructionCount_le {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    {whole : SourceProgram Player L Γ O} {program : SourceProgram Player L Δ P}
    {lift : ProtocolState program → ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) :
    instructionCount program ≤ instructionCount whole := by
  induction origin with
  | initial => exact le_rfl
  | sampleTail fresh law next previous ih =>
      change instructionCount next + 1 ≤ _ at ih
      omega
  | commitTail fresh guard next previous ih =>
      change instructionCount next + 1 ≤ _ at ih
      omega
  | revealTail fresh selected unresolved next previous ih =>
      change instructionCount next + 1 ≤ _ at ih
      omega

/-- Existing rank reconstruction commutes with the exact original-program
suffix lift, including the original control-point tag and full owned word. -/
theorem atRank_lift {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    {whole : SourceProgram Player L Γ O} {program : SourceProgram Player L Δ P}
    {lift : ProtocolState program → ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) (who : Player) :
    ∀ (before later : ProtocolState program) (rank : Nat),
      ProtocolView.atRank who program rank (ProtocolState.observe who program later) =
          some (ProtocolState.observe who program before) →
      ProtocolView.atRank who whole
          (instructionCount whole - instructionCount program + rank)
          (ProtocolState.observe who whole (lift later)) =
        some (ProtocolState.observe who whole (lift before)) := by
  induction origin with
  | initial =>
      intro before later rank reconstructed
      simpa only [Nat.sub_self, Nat.zero_add, id_eq] using reconstructed
  | sampleTail fresh law next previous ih =>
      intro before later rank reconstructed
      have bounded := previous.instructionCount_le
      have earlier := ih (Sum.inr before) (Sum.inr later) (rank + 1) (by
        simpa only [ProtocolState.observe, Sum.elim_inr, ProtocolView.atRank,
          Option.map_some] using congrArg (Option.map Sum.inr) reconstructed)
      have address : instructionCount whole - instructionCount next + rank =
          instructionCount whole - instructionCount (.sample _ fresh law next) + (rank + 1) := by
        simp only [instructionCount] at bounded ⊢
        omega
      rw [address]
      exact earlier
  | commitTail fresh guard next previous ih =>
      intro before later rank reconstructed
      have bounded := previous.instructionCount_le
      have earlier := ih (Sum.inr before) (Sum.inr later) (rank + 1) (by
        simpa only [ProtocolState.observe, Sum.elim_inr, ProtocolView.atRank,
          Option.map_some] using congrArg (Option.map Sum.inr) reconstructed)
      have address : instructionCount whole - instructionCount next + rank =
          instructionCount whole -
            instructionCount (.commit _ _ fresh guard next) + (rank + 1) := by
        simp only [instructionCount] at bounded ⊢
        omega
      rw [address]
      exact earlier
  | revealTail fresh selected unresolved next previous ih =>
      intro before later rank reconstructed
      have bounded := previous.instructionCount_le
      have earlier := ih (Sum.inr before) (Sum.inr later) (rank + 1) (by
        simpa only [ProtocolState.observe, Sum.elim_inr, ProtocolView.atRank,
          Option.map_some] using congrArg (Option.map Sum.inr) reconstructed)
      have address : instructionCount whole - instructionCount next + rank =
          instructionCount whole - instructionCount
            (.reveal _ _ _ fresh selected unresolved next) + (rank + 1) := by
        simp only [instructionCount] at bounded ⊢
        omega
      rw [address]
      exact earlier

end ProtocolSuffix

end Vegas.SourceProgram
