/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitAttemptObservation

/-! # Earlier source observations retained by actual recovery instructions -/

noncomputable section

namespace Vegas.SourceProgram.ProtocolView

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [IExpr.ResultTypes L] in
private theorem back_automaticReveal_view {Γ : SourceCtx Player L} {name : VarId}
    {owner : Player} {payload : L.Ty} (who : Player) (different : owner ≠ who)
    (published : VarId) (selected : HasVar Γ name (.commitment owner payload))
    (config : Config Player L Γ) :
    (({ revealSuccessor published selected config false with history := config.history }).view
        who).back (decide (owner = who)) = config.view who := by
  simp only [Config.view, revealSuccessor, back_sourceObserve, different, decide_false,
    Bool.false_eq_true, ↓reduceIte]

private theorem entryView_recovery_commit {Γ : SourceCtx Player L} {O : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty} (who : Player)
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    (previous : ∀ (point : ProtocolState next) (excluded : Finset Player)
      (joint : Player → Option (CommitRecoveryMove Player L))
      (result : ProtocolState next × Finset Player),
      result ∈ (ProtocolState.recoveryStep next point excluded joint).support → who ∉ excluded →
      entryView who next (ProtocolState.observe who next result.1) =
        entryView who next (ProtocolState.observe who next point))
    (point : ProtocolState (.commit name owner fresh guard next)) (excluded : Finset Player)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (result : ProtocolState (.commit name owner fresh guard next) × Finset Player)
    (reached : result ∈ (ProtocolState.recoveryStep _ point excluded joint).support)
    (survives : who ∉ excluded) :
    entryView who _ (ProtocolState.observe who _ result.1) =
      entryView who _ (ProtocolState.observe who _ point) := by
  cases point with
  | inl config =>
      by_cases inactive : owner ∈ excluded
      · have different : owner ≠ who := fun same => survives (same ▸ inactive)
        simp only [ProtocolState.recoveryStep, Sum.elim_inl, inactive, ↓reduceIte,
          PMF.mem_support_pure_iff] at reached
        subst result
        simp only [ProtocolState.observe, Sum.elim_inr, Sum.elim_inl, entryView, id_eq,
          entryView_observe_entry]
        exact back_automaticCommit_view who owner different name config
      · simp only [ProtocolState.recoveryStep, Sum.elim_inl, inactive, ↓reduceIte,
          PMF.mem_support_pure_iff] at reached
        subst result
        simp only [ProtocolState.observe, Sum.elim_inr, Sum.elim_inl, entryView, id_eq,
          entryView_observe_entry]
        exact back_commit_view who name guard config
          (OwnAction.binding owner name _ ((joint owner).map (·.action)))
  | inr point =>
      obtain ⟨after, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      exact congrArg (DecisionView.back (decide (owner = who)))
        (previous point excluded joint after supported survives)

private theorem entryView_recovery_reveal {Γ : SourceCtx Player L} {O : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty} (who : Player)
    (fresh : published ∉ Γ.map Prod.fst) (source : HasVar Γ name (.commitment owner payload))
    (unresolved : name ∈ O)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name))
    (previous : ∀ (point : ProtocolState next) (excluded : Finset Player)
      (joint : Player → Option (CommitRecoveryMove Player L))
      (result : ProtocolState next × Finset Player),
      result ∈ (ProtocolState.recoveryStep next point excluded joint).support → who ∉ excluded →
      entryView who next (ProtocolState.observe who next result.1) =
        entryView who next (ProtocolState.observe who next point))
    (point : ProtocolState (.reveal published owner name fresh source unresolved next))
    (excluded : Finset Player) (joint : Player → Option (CommitRecoveryMove Player L))
    (result : ProtocolState (.reveal published owner name fresh source unresolved next) ×
      Finset Player)
    (reached : result ∈ (ProtocolState.recoveryStep _ point excluded joint).support)
    (survives : who ∉ excluded) :
    entryView who _ (ProtocolState.observe who _ result.1) =
      entryView who _ (ProtocolState.observe who _ point) := by
  cases point with
  | inl config =>
      by_cases inactive : owner ∈ excluded
      · have different : owner ≠ who := fun same => survives (same ▸ inactive)
        simp only [ProtocolState.recoveryStep, Sum.elim_inl, inactive, ↓reduceIte,
          PMF.mem_support_pure_iff] at reached
        have nextPoint := congrArg Prod.fst reached
        rw [nextPoint]
        simp only [ProtocolState.observe, Sum.elim_inr, Sum.elim_inl, entryView, id_eq,
          entryView_observe_entry]
        exact back_automaticReveal_view who different published source config
      · simp only [ProtocolState.recoveryStep, Sum.elim_inl, inactive, ↓reduceIte,
          PMF.mem_support_pure_iff] at reached
        have nextPoint := congrArg Prod.fst reached
        rw [nextPoint]
        simp only [ProtocolState.observe, Sum.elim_inr, Sum.elim_inl, entryView, id_eq,
          entryView_observe_entry]
        apply back_reveal_view
  | inr point =>
      obtain ⟨after, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      exact congrArg (DecisionView.back (decide (owner = who)))
        (previous point excluded joint after supported survives)


/-- An actual source recovery instruction preserves the existing suffix-entry
view of any owner not already excluded. Foreign automatic actions remain invisible. -/
theorem entryView_recoveryStep (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program)
      (excluded : Finset Player) (joint : Player → Option (CommitRecoveryMove Player L))
      (result : ProtocolState program × Finset Player),
      result ∈ (ProtocolState.recoveryStep program point excluded joint).support →
      who ∉ excluded →
      entryView who program (ProtocolState.observe who program result.1) =
        entryView who program (ProtocolState.observe who program point)
  | _, _, .ret _, point, excluded, joint, result, reached, _survives => by
      simp only [ProtocolState.recoveryStep, PMF.mem_support_pure_iff] at reached
      subst result
      rfl
  | _, _, .sample name fresh law next, point, excluded, joint, result, reached, survives => by
      cases point with
      | inl config =>
          obtain ⟨value, _drawn, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
          simp only [ProtocolState.observe, Sum.elim_inr, Sum.elim_inl, entryView, id_eq,
            entryView_observe_entry, back_sample_view]
      | inr point =>
          obtain ⟨after, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
          exact congrArg (DecisionView.back false)
            (entryView_recoveryStep who next point excluded joint after supported survives)
  | _, _, .commit name owner fresh guard next, point, excluded, joint, result, reached,
      survives =>
      entryView_recovery_commit who fresh guard next
        (fun point excluded joint result reached survives =>
          entryView_recoveryStep who next point excluded joint result reached survives)
        point excluded joint result reached survives
  | _, _, .reveal published owner name fresh source unresolved next, point, excluded, joint,
      result, reached, survives =>
      entryView_recovery_reveal who fresh source unresolved next
        (fun point excluded joint result reached survives =>
          entryView_recoveryStep who next point excluded joint result reached survives)
        point excluded joint result reached survives

/-- Every reached private source rank is preserved by the actual raw
instruction, including automatic slots of already excluded foreign owners. -/
theorem atRank_recoveryStep (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program)
      (excluded : Finset Player) (joint : Player → Option (CommitRecoveryMove Player L))
      (result : ProtocolState program × Finset Player),
      result ∈ (ProtocolState.recoveryStep program point excluded joint).support →
      who ∉ excluded → (rank : Nat) →
      rank ≤ position who program (ProtocolState.observe who program point) →
      atRank who program rank (ProtocolState.observe who program result.1) =
        atRank who program rank (ProtocolState.observe who program point)
  | _, _, .ret _, point, excluded, joint, result, reached, _survives, _, _within => by
      simp only [ProtocolState.recoveryStep, PMF.mem_support_pure_iff] at reached
      subst result
      rfl
  | _, _, .sample name fresh law next, point, excluded, joint, result, reached, survives,
      rank, within => by
      cases rank with
      | zero =>
          exact congrArg (fun view => some (Sum.inl view))
            (entryView_recoveryStep who (.sample name fresh law next) point excluded joint result
              reached survives)
      | succ rank =>
          cases point with
          | inl config => simp [ProtocolState.observe, position] at within
          | inr point =>
              obtain ⟨after, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
              have earlier : rank ≤ position who next (ProtocolState.observe who next point) := by
                simpa only [ProtocolState.observe, Sum.elim_inr, position,
                  Nat.add_le_add_iff_right] using within
              exact congrArg (Option.map Sum.inr)
                (atRank_recoveryStep who next point excluded joint after supported survives rank
                  earlier)
  | _, _, .commit name owner fresh guard next, point, excluded, joint, result, reached, survives,
      rank, within => by
      cases rank with
      | zero =>
          exact congrArg (fun view => some (Sum.inl view))
            (entryView_recoveryStep who (.commit name owner fresh guard next) point excluded joint
              result reached survives)
      | succ rank =>
          cases point with
          | inl config => simp [ProtocolState.observe, position] at within
          | inr point =>
              obtain ⟨after, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
              have earlier : rank ≤ position who next (ProtocolState.observe who next point) := by
                simpa only [ProtocolState.observe, Sum.elim_inr, position,
                  Nat.add_le_add_iff_right] using within
              exact congrArg (Option.map Sum.inr)
                (atRank_recoveryStep who next point excluded joint after supported survives rank
                  earlier)
  | _, _, .reveal published owner name fresh source unresolved next, point, excluded, joint,
      result, reached, survives, rank, within => by
      cases rank with
      | zero =>
          exact congrArg (fun view => some (Sum.inl view))
            (entryView_recoveryStep who (.reveal published owner name fresh source unresolved next)
              point excluded joint result reached survives)
      | succ rank =>
          cases point with
          | inl config => simp [ProtocolState.observe, position] at within
          | inr point =>
              obtain ⟨after, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
              have earlier : rank ≤ position who next (ProtocolState.observe who next point) := by
                simpa only [ProtocolState.observe, Sum.elim_inr, position,
                  Nat.add_le_add_iff_right] using within
              exact congrArg (Option.map Sum.inr)
                (atRank_recoveryStep who next point excluded joint after supported survives rank
                  earlier)

end Vegas.SourceProgram.ProtocolView
