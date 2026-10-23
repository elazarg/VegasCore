/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryAttemptReset

/-! # Deterministic source transitions at owned instructions -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

theorem ProtocolState.recoveryStep_owned_pure :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program)
      (excluded : Finset Player) (joint : Player → Option (CommitRecoveryMove Player L))
      (owner : Player), ProtocolState.actor program point = some owner →
        ∃ result, ProtocolState.recoveryStep program point excluded joint = PMF.pure result := by
  intro Γ O program
  induction program with
  | ret payoffs => intro point excluded joint owner impossible; cases impossible
  | sample name fresh law next ih =>
      intro point excluded joint owner acting
      cases point with
      | inl config => cases acting
      | inr later =>
          obtain ⟨result, pure⟩ := ih later excluded joint owner acting
          exact ⟨(Sum.inr result.1, result.2), by
            simp only [ProtocolState.recoveryStep, Sum.elim_inr, pure,
            PMF.pure_map]⟩
  | commit name owner fresh guard next ih =>
      intro point excluded joint who acting
      cases point with
      | inl config =>
          simp only [ProtocolState.recoveryStep, Sum.elim_inl]
          split <;> exact ⟨_, rfl⟩
      | inr later =>
          obtain ⟨result, pure⟩ := ih later excluded joint who acting
          exact ⟨(Sum.inr result.1, result.2), by
            simp only [ProtocolState.recoveryStep, Sum.elim_inr, pure,
            PMF.pure_map]⟩
  | reveal published owner name fresh selected unresolved next ih =>
      intro point excluded joint who acting
      cases point with
      | inl config => exact ⟨_, rfl⟩
      | inr later =>
          obtain ⟨result, pure⟩ := ih later excluded joint who acting
          exact ⟨(Sum.inr result.1, result.2), by
            simp only [ProtocolState.recoveryStep, Sum.elim_inr, pure,
            PMF.pure_map]⟩

theorem Setup.commitRecovery_step_unique_of_actor
    (setup : Setup (Player := Player) (L := L))
    (current : CommitRecoveryState setup.program) (owner : Player)
    (acting : ProtocolState.actor setup.program current.point = some owner)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (first second : CommitRecoveryState setup.program)
    (left : first ∈ (current.step joint).support)
    (right : second ∈ (current.step joint).support) : first = second := by
  obtain ⟨l, lm, rfl⟩ := current.step_raw_result joint first left
  obtain ⟨r, rm, rfl⟩ := current.step_raw_result joint second right
  obtain ⟨result, pure⟩ := ProtocolState.recoveryStep_owned_pure setup.program
    current.point current.excluded
    joint owner acting
  rw [pure, PMF.mem_support_pure_iff] at lm rm
  have equal : l = r := Subtype.ext (lm.trans rm.symm)
  cases equal
  rfl

end Vegas.SourceProgram
