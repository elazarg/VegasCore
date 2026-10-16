/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledCommitAttempt
import Vegas.Source.CommitRecoveryCommitStep

/-! # Legal source successors of an actual physical commitment decoder -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A single actual decoded binding has a genuine source recovery successor,
including physical missing receipts and automatic excluded-owner slots. -/
theorem decoded_commit_successor
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeO) (initial : SourceProgram.Config Player L wholeΓ)
    (mode : ExecutionMode) {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (tail : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (.commit name owner fresh guard tail))
    (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (entry : SourceProgram.Config Player L Γ) (state : CommitRecoveryState whole)
    (lift : ProtocolState (.commit name owner fresh guard tail) → ProtocolState whole)
    (atEntry : state.point = lift (Sum.inl entry))
    (ranks : ∀ point, ProtocolState.remaining whole (lift point) =
      ProtocolState.remaining (.commit name owner fresh guard tail) point)
    (actors : ∀ point, ProtocolState.actor whole (lift point) =
      ProtocolState.actor (.commit name owner fresh guard tail) point)
    (menus : ∀ point who, ProtocolView.recoveryAvailable who whole
      (ProtocolState.observe who whole (lift point)) =
      ProtocolView.recoveryAvailable who (.commit name owner fresh guard tail)
        (ProtocolState.observe who (.commit name owner fresh guard tail) point))
    (steps : ∀ point excluded joint, ProtocolState.recoveryStep whole (lift point) excluded joint =
      (ProtocolState.recoveryStep (.commit name owner fresh guard tail) point excluded joint).map
        (fun result => (lift result.1, result.2))) :
    let block : SourceProgram.CommitPrefix Γ O
        ((name, .commitment owner payload) :: Γ) (insert name O) :=
      .commit name owner fresh guard .nil
    let decoded := decodeCommitAttempt whole mode block tail embedding native entry state.excluded
    (commitRecoveryProtocol whole initial).Successor
      (state.install (lift (Sum.inr (ProtocolState.entry tail decoded.1)), decoded.2.1)
        (fun _ member => decoded.2.2.excluded_subset member)).close state := by
  intro block decoded
  let event := embedding.event ⟨0, by simp only [eventCount]; omega⟩
  let accepted := native.accepted (.inr event)
  let choice := accepted.elim PublicationResult.failure (fun candidate =>
    native.bindingResult candidate payload)
  have missingFailure : accepted.isNone = true → choice = .failure := by
    cases found : accepted <;>
      simp only [choice, found, Option.isNone_none, Option.isNone_some, Option.elim_none,
        Bool.false_eq_true, false_implies, implies_true]
  obtain ⟨monotone, reached⟩ := lifted_commit_successor whole initial guard tail lift ranks actors
    menus steps entry state atEntry choice accepted.isNone missingFailure
  have configEq : decoded.1 = if owner ∈ state.excluded then
      automaticCommit name owner payload entry else commitSuccessor name guard entry choice := by
    dsimp only [decoded, block, decodeCommitAttempt]
    split <;> rfl
  have excludedEq : decoded.2.1 = if owner ∈ state.excluded then state.excluded
      else excludeCommit state.excluded owner accepted.isNone := by
    dsimp only [decoded, block, decodeCommitAttempt]
    by_cases inactive : owner ∈ state.excluded
    · rw [dite_eq_left inactive]
      exact (ite_eq_left inactive).symm
    · rw [dite_eq_right inactive]
      exact (ite_eq_right inactive).symm
  have installCongr (first second : ProtocolState whole × Finset Player)
      (firstMono : state.excluded ⊆ first.2) (secondMono : state.excluded ⊆ second.2)
      (same : first = second) :
      state.install first firstMono = state.install second secondMono := by
    cases same
    rfl
  have rawEq := installCongr
    (lift (Sum.inr (ProtocolState.entry tail decoded.1)), decoded.2.1)
    (lift (Sum.inr (ProtocolState.entry tail (if owner ∈ state.excluded then
      automaticCommit name owner payload entry else commitSuccessor name guard entry choice))),
        if owner ∈ state.excluded then state.excluded
          else excludeCommit state.excluded owner accepted.isNone)
    (fun _ member => decoded.2.2.excluded_subset member) monotone
    (Prod.ext (congrArg (fun config => lift (Sum.inr (ProtocolState.entry tail config))) configEq)
      excludedEq)
  rw [show (state.install (lift (Sum.inr (ProtocolState.entry tail decoded.1)), decoded.2.1)
      (fun _ member => decoded.2.2.excluded_subset member)).close = _ from
    congrArg CommitRecoveryState.close rawEq]
  exact reached

end Vegas
