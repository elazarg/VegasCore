/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledCommitHead
import Vegas.Game.CompiledCommitAttemptSplit
import Vegas.Pending.PhaseRecordedBindingMaterial
import Vegas.Pending.PhaseBindingFreshness
import Vegas.Source.IntendedBetween

/-! # Emitted typed values at their exact rank in the whole decoded attempt -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime
open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeO) (mode : ExecutionMode)

open Classical in
/-- The original rank in the complete decoded word retains its literal accepted
handle, typed result and omission bit. The middle exclusion set is the actual
earlier decoder, including every inherited automatic coordinate. -/
theorem decodeCommitAttempt_joint_at_rank
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (earlier : CommitPrefix Γ O Δ P) (fresh : name ∉ Δ.map Prod.fst)
    (guard : SourceGuard L Δ owner name payload)
    (rest : CommitPrefix ((name, .commitment owner payload) :: Δ) (insert name P) Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      ((earlier.append (.commit name owner fresh guard rest)).prepend suffix))
    (offset : Nat) (ranked : ∀ index, (embedding.event index).val = offset + index.val)
    (selected : Fin (eventCount
      ((earlier.append (.commit name owner fresh guard rest)).prepend suffix)))
    (atRank : selected.val = earlier.length)
    (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (entry : SourceProgram.Config Player L Γ) (excluded : Finset Player)
    (source : CommitRecoveryState whole) :
    let later : CommitPrefix Δ P Ξ Q := .commit name owner fresh guard rest
    let prefixEmbedding := cast
      (congrArg (OutputEmbedding (inputLayout wholeΓ) (outputLayout whole))
        (earlier.prepend_append later suffix)) embedding
    let middle := decodeCommitAttempt whole mode earlier (later.prepend suffix) prefixEmbedding
      native entry excluded
    let complete := decodeCommitAttempt whole mode (earlier.append later) suffix embedding native
      entry excluded
    source.excluded = middle.2.1 →
      complete.2.2.joints[earlier.length]? =
        some (source.commitJoint owner name payload
          ((native.accepted (.inr (embedding.event selected))).elim PublicationResult.failure
            (fun candidate => native.bindingResult candidate payload))
          (native.accepted (.inr (embedding.event selected))).isNone) ∧
      ((Δ.map Prod.fst).Nodup → owner ∉ source.excluded →
        SourceProgram.State.cell? complete.1.state name (.commitment owner payload) =
          some ((native.accepted (.inr (embedding.event selected))).elim
            PublicationResult.failure
              (fun candidate => native.bindingResult candidate payload))) := by
  intro later prefixEmbedding middle complete inherited
  obtain ⟨tailEmbedding, sameConfig, _sameExcluded, word, positioned⟩ :=
    decodeCommitAttempt_append whole mode earlier later suffix embedding native entry excluded
  let zero : Fin (eventCount (later.prepend suffix)) :=
    ⟨0, by simp only [later, CommitPrefix.prepend, eventCount]; omega⟩
  have event : tailEmbedding.event zero = embedding.event selected := by
    apply Fin.ext
    rw [positioned offset ranked zero, ranked selected, atRank]
    simp only [zero, Nat.add_zero]
  let head : CommitPrefix Δ P ((name, .commitment owner payload) :: Δ) (insert name P) :=
    .commit name owner fresh guard .nil
  have headWord : (decodeCommitAttempt whole mode head (rest.prepend suffix) tailEmbedding
      native middle.1 middle.2.1).2.2.joints =
        [source.commitJoint owner name payload
          ((native.accepted (.inr (embedding.event selected))).elim PublicationResult.failure
            (fun candidate => native.bindingResult candidate payload))
          (native.accepted (.inr (embedding.event selected))).isNone] := by
    rw [← inherited, decodeCommitAttempt_head_joints]
    change [source.commitJoint owner name payload
      ((native.accepted (.inr (tailEmbedding.event zero))).elim PublicationResult.failure
        (fun candidate => native.bindingResult candidate payload))
      (native.accepted (.inr (tailEmbedding.event zero))).isNone] = _
    rw [event]
  have tailWord := (decodeCommitAttempt_commit_tail whole mode fresh guard rest suffix
    tailEmbedding native middle.1 middle.2.1).2.2
  constructor
  · rw [word, tailWord, headWord]
    have length := middle.2.2.joints_length
    rw [← length, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  · intro unique active
    have preserved : ∀ {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
        {block : CommitPrefix Γ O Δ P} {entry : Config Player L Γ}
        {excluded : Finset Player} {finished : Config Player L Δ} {after : Finset Player},
        block.Attempt entry excluded finished after → (Γ.map Prod.fst).Nodup →
        ∀ {name : VarId} {kind : CellTy Player L} (selected : HasVar Γ name kind),
          SourceProgram.State.cell? finished.state name kind = some (entry.state.get selected) := by
      intro Γ Δ O P block entry excluded finished after attempt
      induction attempt with
      | nil entry excluded =>
          intro unique name kind selected
          exact SourceProgram.State.cell?_eq_of_hasVar selected unique entry.state
      | @active Γ Δ O P name owner payload fresh guard rest entry excluded finished after
          active choice missed missingFailure later ih =>
          intro unique readName kind selected
          exact ih (List.nodup_cons.mpr ⟨fresh, unique⟩) (.there selected)
      | @excluded Γ Δ O P name owner payload fresh guard rest entry excluded finished after
          inactive later ih =>
          intro unique readName kind selected
          exact ih (List.nodup_cons.mpr ⟨fresh, unique⟩) (.there selected)
    have enabled : owner ∉ middle.2.1 := by simpa only [← inherited] using active
    rw [← sameConfig]
    dsimp only [later, decodeCommitAttempt]
    rw [dite_eq_right enabled]
    dsimp only
    have kept := preserved
      (decodeCommitAttempt whole mode rest suffix
        (tailEmbedding.tail (rest.prepend suffix) (by rfl) (fun _ => rfl)) native
        (commitSuccessor name guard middle.1
          ((native.accepted (.inr (tailEmbedding.event zero))).elim PublicationResult.failure
            (fun candidate => native.bindingResult candidate payload)))
        (excludeCommit middle.2.1 owner
          (native.accepted (.inr (tailEmbedding.event zero))).isNone)).2.2
      (List.nodup_cons.mpr ⟨fresh, unique⟩) (.here : HasVar
        ((name, .commitment owner payload) :: Δ) name (.commitment owner payload))
    simpa only [commitSuccessor, Env.get, Env.cons, event] using kept


end Vegas
