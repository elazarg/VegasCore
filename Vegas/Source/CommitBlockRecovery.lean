/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitBlockInformation

/-! # Clear recovery successors within a hidden commitment block -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

theorem HiddenBindings.control (who : Player) : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (first second : ProtocolState program),
    HiddenBindings who program first second →
      remaining program first = remaining program second ∧
        (terminal program first ↔ terminal program second)
  | _, _, .ret _, _, _, _ => ⟨rfl, Iff.rfl⟩
  | _, _, .sample _ _ _ next, first, second, related => by
      cases first <;> cases second
      · exact ⟨rfl, Iff.rfl⟩
      · exact related.elim
      · exact related.elim
      · exact control who next _ _ related
  | _, _, .commit _ _ _ _ next, first, second, related => by
      cases first <;> cases second
      · exact ⟨rfl, Iff.rfl⟩
      · exact related.elim
      · exact related.elim
      · exact control who next _ _ related
  | _, _, .reveal _ _ _ _ _ _ next, first, second, related => by
      cases first <;> cases second
      · exact ⟨rfl, Iff.rfl⟩
      · exact related.elim
      · exact related.elim
      · exact control who next _ _ related

theorem recoveryStep_missed_excludes (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (point : ProtocolState program) (excluded : Finset Player)
      (joint : Player → Option (CommitRecoveryMove Player L)),
    atCommit program point = true → actor program point = some who →
    CommitRecoveryMove.missed (joint who) = true →
    ∀ result ∈ (recoveryStep program point excluded joint).support, who ∈ result.2
  | _, _, .ret _, _, _, _, active, _, _, _, _ => by cases active
  | _, _, .sample _ _ _ next, point, excluded, joint, active, acting, missed,
      result, reached => by
      cases point with
      | inl _ => cases active
      | inr point =>
          simp only [recoveryStep, Sum.elim_inr, PMF.support_map] at reached
          obtain ⟨result, reached, rfl⟩ := reached
          exact recoveryStep_missed_excludes who next point excluded joint active acting
            missed result reached
  | _, _, .commit _ owner _ _ next, point, excluded, joint, active, acting, missed,
      result, reached => by
      cases point with
      | inl _ =>
          have same : owner = who := Option.some.inj acting
          subst owner
          by_cases already : who ∈ excluded
          · simp only [recoveryStep, Sum.elim_inl, already, ↓reduceIte,
              PMF.mem_support_pure_iff] at reached
            subst result
            exact already
          · simp only [recoveryStep, Sum.elim_inl, already, ↓reduceIte, missed,
              PMF.mem_support_pure_iff] at reached
            subst result
            exact Finset.mem_insert_self _ _
      | inr point =>
          simp only [recoveryStep, Sum.elim_inr, PMF.support_map] at reached
          obtain ⟨result, reached, rfl⟩ := reached
          exact recoveryStep_missed_excludes who next point excluded joint active acting
            missed result reached
  | _, _, .reveal _ _ _ _ _ _ next, point, excluded, joint, active, acting, missed,
      result, reached => by
      cases point with
      | inl _ => cases active
      | inr point =>
          simp only [recoveryStep, Sum.elim_inr, PMF.support_map] at reached
          obtain ⟨result, reached, rfl⟩ := reached
          exact recoveryStep_missed_excludes who next point excluded joint active acting
            missed result reached

end ProtocolState

namespace CommitRecoveryState

variable {Γ : SourceCtx Player L} {O : Finset VarId} {program : SourceProgram Player L Γ O}

/-- An actual missing commitment is a permanent exclusion even if its block
closes and immediately restores a saved semantic checkpoint. -/
theorem missed_excludes (who : Player) (state : CommitRecoveryState program)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (active : ProtocolState.atCommit program state.point = true)
    (acting : ProtocolState.actor program state.point = some who)
    (missed : CommitRecoveryMove.missed (joint who) = true)
    (next : CommitRecoveryState program) (reached : next ∈ (state.step joint).support) :
    who ∈ next.excluded := by
  obtain ⟨result, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  have raw : result.1 ∈
      (ProtocolState.recoveryStep program state.point state.excluded joint).support := by
    rw [← map_val_pmfToSubtype
      (ProtocolState.recoveryStep program state.point state.excluded joint)
      (fun result supported => ProtocolState.recoveryStep_excluded_monotone program state.point
        state.excluded joint result supported)]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, supported, rfl⟩
  rw [close_excluded]
  exact ProtocolState.recoveryStep_missed_excludes who program state.point state.excluded
    joint active acting missed result.1 raw

/-- No actual omission during a commitment instruction means no reset; its
typed successor is the ordinary source successor, regardless of its values. -/
theorem commit_noMiss_support (state : CommitRecoveryState program)
    (clear : state.excluded = ∅) (active : ProtocolState.atCommit program state.point = true)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (noMiss : ∀ who, CommitRecoveryMove.missed (joint who) = false)
    (next : CommitRecoveryState program) (reached : next ∈ (state.step joint).support) :
    next.excluded = ∅ ∧ next.point ∈
      (ProtocolState.step program state.point (fun who => (joint who).map (·.action))).support := by
  obtain ⟨result, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  have raw : result.1 ∈
      (ProtocolState.recoveryStep program state.point state.excluded joint).support := by
    rw [← map_val_pmfToSubtype
      (ProtocolState.recoveryStep program state.point state.excluded joint)
      (fun result supported => ProtocolState.recoveryStep_excluded_monotone program state.point
        state.excluded joint result supported)]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, supported, rfl⟩
  have law : ProtocolState.recoveryStep program state.point state.excluded joint =
      (ProtocolState.step program state.point (fun who => (joint who).map (·.action))).map
        (fun target => (target, ∅)) := by
    rw [clear, ProtocolState.recoveryStep_commit_joint program state.point joint active noMiss]
  rw [law, PMF.support_map] at raw
  obtain ⟨point, member, equality⟩ := raw
  have resultClear : result.1.2 = ∅ := congrArg Prod.snd equality.symm
  have noFailure : ¬ (state.install result.1 result.2).NewFailure := by
    simp only [NewFailure, install, resultClear, Finset.empty_sdiff,
      Finset.not_nonempty_empty, not_false_eq_true]
  refine ⟨?_, ?_⟩
  · simpa only [close_excluded, install] using resultClear
  · rw [close_point_of_no_new_failure _ noFailure]
    change result.1.1 ∈ _
    rw [← congrArg Prod.fst equality]
    exact member

end CommitRecoveryState
end Vegas.SourceProgram
