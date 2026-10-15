/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryProtocol
import Vegas.Source.FailedBindingDeviation

/-! # Debt retained in saved recovery frontiers survives every later retry -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace Config

omit [IExpr.ResultTypes L] in
/-- Automatic excluded slots weaken old obligations without discarding debt. -/
theorem Indebted.automaticCommit {Γ : SourceCtx Player L} {O : Finset VarId}
    {who owner : Player} {name : VarId} {payload : L.Ty}
    {config : Config Player L Γ} (owed : config.Indebted who O)
    (fresh : name ∉ Γ.map Prod.fst) :
    (automaticCommit name owner payload config).Indebted who (insert name O) where
  unique := List.nodup_cons.mpr ⟨fresh, owed.unique⟩
  accounted := Accounted.commit fresh owed.accounted
  publishes := PublishesBindings.weaken _ owed.publishes
  pending := by
    obtain ⟨obligation, member, own, unrevealed, value, bound, rejected⟩ := owed.pending
    exact ⟨obligation.weaken, List.mem_map_of_mem member, own,
      (Obligation.revealed_weaken _ _).trans unrevealed, value, bound,
      (SourceGuard.predicts_weaken _ _ _ _).trans rejected⟩

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- Automatic slots leave every earlier unresolved failed binding immutable. -/
theorem FailedBinding.automaticCommit {Γ : SourceCtx Player L} {O : Finset VarId}
    {who owner : Player} {name : VarId} {payload : L.Ty}
    {config : Config Player L Γ} (owed : config.FailedBinding who O)
    (fresh : name ∉ Γ.map Prod.fst) :
    (automaticCommit name owner payload config).FailedBinding who (insert name O) where
  unique := List.nodup_cons.mpr ⟨fresh, owed.unique⟩
  pending := by
    obtain ⟨subject, payload, source, pending, bound⟩ := owed.pending
    exact ⟨subject, payload, .there source, Finset.mem_insert_of_mem pending, bound⟩

omit [IExpr.ResultTypes L] in
theorem indebted_withHistory {Γ : SourceCtx Player L} {O : Finset VarId} (who : Player)
    (config : Config Player L Γ) (past : History Player L) :
    Indebted who O { config with history := past } ↔ Indebted who O config :=
  ⟨fun owed => ⟨owed.unique, owed.accounted, owed.publishes, owed.pending⟩,
    fun owed => ⟨owed.unique, owed.accounted, owed.publishes, owed.pending⟩⟩

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem failedBinding_withHistory {Γ : SourceCtx Player L} {O : Finset VarId} (who : Player)
    (config : Config Player L Γ) (past : History Player L) :
    FailedBinding who O { config with history := past } ↔ FailedBinding who O config :=
  ⟨fun owed => ⟨owed.unique, owed.pending⟩, fun owed => ⟨owed.unique, owed.pending⟩⟩

end Config

namespace ProtocolState

/-- Replacing recall alone changes no semantic entry cell. -/
theorem base_withHistory : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (past : History Player L), base program (withHistory program point past) = base program point
  | _, _, .ret _, _, _ => rfl
  | _, _, .sample _ _ _ next, point, past => by
      cases point with
      | inl _ => rfl
      | inr point => simp only [withHistory, base, Sum.elim_inr, base_withHistory next point past]
  | _, _, .commit _ _ _ _ next, point, past => by
      cases point with
      | inl _ => rfl
      | inr point => simp only [withHistory, base, Sum.elim_inr, base_withHistory next point past]
  | _, _, .reveal _ _ _ _ _ _ next, point, past => by
      cases point with
      | inl _ => rfl
      | inr point => simp only [withHistory, base, Sum.elim_inr, base_withHistory next point past]

theorem indebted_withHistory (who : Player) : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (past : History Player L),
    Indebted who program (withHistory program point past) ↔ Indebted who program point
  | _, _, .ret _, config, past => Config.indebted_withHistory who config past
  | _, _, .sample _ _ _ next, point, past => by
      cases point with
      | inl config => exact Config.indebted_withHistory who config past
      | inr point => exact indebted_withHistory who next point past
  | _, _, .commit _ _ _ _ next, point, past => by
      cases point with
      | inl config => exact Config.indebted_withHistory who config past
      | inr point => exact indebted_withHistory who next point past
  | _, _, .reveal _ _ _ _ _ _ next, point, past => by
      cases point with
      | inl config => exact Config.indebted_withHistory who config past
      | inr point =>
          change (_ ∨ Indebted who next (withHistory next point past)) ↔
            (_ ∨ Indebted who next point)
          rw [base_withHistory, indebted_withHistory who next point past]

theorem failedBinding_withHistory (who : Player) : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (past : History Player L),
    FailedBinding who program (withHistory program point past) ↔ FailedBinding who program point
  | _, _, .ret _, config, past => Config.failedBinding_withHistory who config past
  | _, _, .sample _ _ _ next, point, past => by
      cases point with
      | inl config => exact Config.failedBinding_withHistory who config past
      | inr point => exact failedBinding_withHistory who next point past
  | _, _, .commit _ _ _ _ next, point, past => by
      cases point with
      | inl config => exact Config.failedBinding_withHistory who config past
      | inr point => exact failedBinding_withHistory who next point past
  | _, _, .reveal _ _ _ _ _ _ next, point, past => by
      cases point with
      | inl config => exact Config.failedBinding_withHistory who config past
      | inr point =>
          change (_ ∨ FailedBinding who next (withHistory next point past)) ↔
            (_ ∨ FailedBinding who next point)
          rw [base_withHistory, failedBinding_withHistory who next point past]

/-- A retry's retained private actions do not erase semantic debt. -/
theorem owesFailure_withHistory (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (past : History Player L) :
    OwesFailure who program (withHistory program point past) ↔ OwesFailure who program point :=
  or_congr (indebted_withHistory who program point past)
    (failedBinding_withHistory who program point past)

/-- Recovery instructions leave every previously stored source entry cell intact. -/
theorem base_recoveryStep : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (excluded : Finset Player) (joint : Player → Option (CommitRecoveryMove Player L))
    (result : ProtocolState program × Finset Player),
    result ∈ (recoveryStep program point excluded joint).support →
      base program result.1 = base program point
  | _, _, .ret _, _, _, _, _, reached => by
      rw [recoveryStep, PMF.mem_support_pure_iff] at reached
      cases reached
      rfl
  | _, _, .sample _ _ _ next, point, excluded, joint, result, reached => by
      cases point with
      | inl config =>
          simp only [recoveryStep, Sum.elim_inl, PMF.support_map, Set.mem_image] at reached
          obtain ⟨value, _, rfl⟩ := reached
          change (fun _ _ cell => (base next (entry next _)).get (.there cell)) = config.state
          rw [base_entry]
          rfl
      | inr point =>
          simp only [recoveryStep, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          simp only [base, Sum.elim_inr,
            base_recoveryStep next point excluded joint after supported]
  | _, _, .commit _ _ _ _ next, point, excluded, joint, result, reached => by
      cases point with
      | inl config =>
          simp only [recoveryStep, Sum.elim_inl] at reached
          split at reached <;> rw [PMF.mem_support_pure_iff] at reached <;> cases reached <;>
            change (fun _ _ cell => (base next (entry next _)).get (.there cell)) = config.state <;>
            rw [base_entry] <;> rfl
      | inr point =>
          simp only [recoveryStep, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          simp only [base, Sum.elim_inr,
            base_recoveryStep next point excluded joint after supported]
  | _, _, .reveal _ owner _ _ _ _ next, point, excluded, joint, result, reached => by
      cases point with
      | inl config =>
          simp only [recoveryStep, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          cases reached
          by_cases inactive : owner ∈ excluded <;> simp only [inactive, ↓reduceIte] <;>
            change (fun _ _ cell => (base next (entry next _)).get (.there cell)) = config.state <;>
            rw [base_entry] <;> rfl
      | inr point =>
          simp only [recoveryStep, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          simp only [base, Sum.elim_inr,
            base_recoveryStep next point excluded joint after supported]

theorem indebted_recoveryStep (who : Player) : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (excluded : Finset Player) (joint : Player → Option (CommitRecoveryMove Player L))
    (result : ProtocolState program × Finset Player),
    Indebted who program point → result ∈ (recoveryStep program point excluded joint).support →
      Indebted who program result.1
  | _, _, .ret _, _, _, _, _, owed, reached => by
      rw [recoveryStep, PMF.mem_support_pure_iff] at reached
      cases reached
      exact owed
  | _, _, .sample _ fresh _ next, point, excluded, joint, result, owed, reached => by
      cases point with
      | inl config =>
          simp only [recoveryStep, Sum.elim_inl, PMF.support_map, Set.mem_image] at reached
          obtain ⟨value, _, rfl⟩ := reached
          exact indebted_entry next _ (Config.Indebted.sample owed fresh value)
      | inr point =>
          simp only [recoveryStep, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact indebted_recoveryStep who next point excluded joint after owed supported
  | _, _, .commit _ _ fresh guard next, point, excluded, joint, result, owed, reached => by
      cases point with
      | inl config =>
          simp only [recoveryStep, Sum.elim_inl] at reached
          split at reached
          · rw [PMF.mem_support_pure_iff] at reached
            cases reached
            exact indebted_entry next _ (Config.Indebted.automaticCommit owed fresh)
          · rw [PMF.mem_support_pure_iff] at reached
            cases reached
            exact indebted_entry next _ (Config.Indebted.commit owed fresh guard _)
      | inr point =>
          simp only [recoveryStep, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact indebted_recoveryStep who next point excluded joint after owed supported
  | _, _, .reveal _ owner _ fresh source _ next, point, excluded, joint, result, owed, reached => by
      cases point with
      | inl config =>
          simp only [recoveryStep, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          cases reached
          by_cases inactive : owner ∈ excluded
          · simp only [inactive, ↓reduceIte]
            rcases Config.Indebted.reveal owed fresh source false with forfeited | debt
            · exact Or.inl ⟨forfeited.1, by rw [base_entry]; exact forfeited.2⟩
            · exact Or.inr (indebted_entry next _
                ((Config.indebted_withHistory who _ config.history).mpr debt))
          · simp only [inactive, ↓reduceIte]
            rcases Config.Indebted.reveal owed fresh source _ with forfeited | debt
            · exact Or.inl ⟨forfeited.1, by rw [base_entry]; exact forfeited.2⟩
            · exact Or.inr (indebted_entry next _ debt)
      | inr point =>
          simp only [recoveryStep, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          rcases owed with ⟨own, publication⟩ | debt
          · exact Or.inl ⟨own,
              (base_recoveryStep next point excluded joint after supported).symm ▸ publication⟩
          · exact Or.inr (indebted_recoveryStep who next point excluded joint after debt supported)

theorem failedBinding_recoveryStep (who : Player) : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (excluded : Finset Player) (joint : Player → Option (CommitRecoveryMove Player L))
    (result : ProtocolState program × Finset Player),
    FailedBinding who program point → result ∈ (recoveryStep program point excluded joint).support →
      FailedBinding who program result.1
  | _, _, .ret _, _, _, _, _, owed, reached => by
      rw [recoveryStep, PMF.mem_support_pure_iff] at reached
      cases reached
      exact owed
  | _, _, .sample _ fresh _ next, point, excluded, joint, result, owed, reached => by
      cases point with
      | inl config =>
          simp only [recoveryStep, Sum.elim_inl, PMF.support_map, Set.mem_image] at reached
          obtain ⟨value, _, rfl⟩ := reached
          exact failedBinding_entry next _ (Config.FailedBinding.sample owed fresh value)
      | inr point =>
          simp only [recoveryStep, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact failedBinding_recoveryStep who next point excluded joint after owed supported
  | _, _, .commit _ _ fresh guard next, point, excluded, joint, result, owed, reached => by
      cases point with
      | inl config =>
          simp only [recoveryStep, Sum.elim_inl] at reached
          split at reached
          · rw [PMF.mem_support_pure_iff] at reached
            cases reached
            exact failedBinding_entry next _ (Config.FailedBinding.automaticCommit owed fresh)
          · rw [PMF.mem_support_pure_iff] at reached
            cases reached
            exact failedBinding_entry next _ (Config.FailedBinding.commit owed fresh guard _)
      | inr point =>
          simp only [recoveryStep, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact failedBinding_recoveryStep who next point excluded joint after owed supported
  | _, _, .reveal _ owner _ fresh source _ next, point, excluded, joint, result, owed, reached => by
      cases point with
      | inl config =>
          simp only [recoveryStep, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          cases reached
          by_cases inactive : owner ∈ excluded
          · simp only [inactive, ↓reduceIte]
            rcases Config.FailedBinding.reveal owed fresh source false with forfeited | debt
            · exact Or.inl ⟨forfeited.1, by rw [base_entry]; exact forfeited.2⟩
            · exact Or.inr (failedBinding_entry next _
                ((Config.failedBinding_withHistory who _ config.history).mpr debt))
          · simp only [inactive, ↓reduceIte]
            rcases Config.FailedBinding.reveal owed fresh source _ with forfeited | debt
            · exact Or.inl ⟨forfeited.1, by rw [base_entry]; exact forfeited.2⟩
            · exact Or.inr (failedBinding_entry next _ debt)
      | inr point =>
          simp only [recoveryStep, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          rcases owed with ⟨own, publication⟩ | debt
          · exact Or.inl ⟨own,
              (base_recoveryStep next point excluded joint after supported).symm ▸ publication⟩
          · exact Or.inr (failedBinding_recoveryStep who next point excluded joint after
              debt supported)

/-- Every actual raw recovery instruction preserves existing own source debt. -/
theorem owesFailure_recoveryStep (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (excluded : Finset Player) (joint : Player → Option (CommitRecoveryMove Player L))
    (result : ProtocolState program × Finset Player) (owed : OwesFailure who program point)
    (reached : result ∈ (recoveryStep program point excluded joint).support) :
    OwesFailure who program result.1 :=
  owed.elim (fun debt => Or.inl (indebted_recoveryStep who program point excluded joint result
      debt reached))
    (fun debt => Or.inr (failedBinding_recoveryStep who program point excluded joint result
      debt reached))

/-- Completing only automatic commitments does not rewrite earlier source cells. -/
theorem base_automaticCommitBlock : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program),
    base program (automaticCommitBlock program point) = base program point
  | _, _, .ret _, _ => rfl
  | _, _, .sample _ _ _ next, point => by
      cases point with
      | inl _ => rfl
      | inr point => simp only [automaticCommitBlock, base, Sum.elim_inr,
          base_automaticCommitBlock next point]
  | _, _, .commit _ _ _ _ next, point => by
      cases point with
      | inl config =>
          change (fun _ _ cell =>
            (base next (automaticCommitBlock next (entry next _))).get (.there cell)) = config.state
          rw [base_automaticCommitBlock, base_entry]
          rfl
      | inr point => simp only [automaticCommitBlock, base, Sum.elim_inr,
          base_automaticCommitBlock next point]
  | _, _, .reveal _ _ _ _ _ _ next, point => by
      cases point with
      | inl _ => rfl
      | inr point => simp only [automaticCommitBlock, base, Sum.elim_inr,
          base_automaticCommitBlock next point]

/-- Exhausting a later block cannot erase debt inherited from its saved frontier. -/
theorem owesFailure_automaticCommitBlock (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program),
    OwesFailure who program point → OwesFailure who program (automaticCommitBlock program point)
  | _, _, .ret _, _, owed => owed
  | _, _, .sample _ _ _ next, point, owed => by
      cases point with
      | inl _ => exact owed
      | inr point => exact owesFailure_automaticCommitBlock who next point owed
  | _, _, .commit _ _ fresh _ next, point, owed => by
      cases point with
      | inl config =>
          apply owesFailure_automaticCommitBlock who next (entry next _)
          rcases owed with indebted | failed
          · exact Or.inl (indebted_entry next _ (Config.Indebted.automaticCommit indebted fresh))
          · exact Or.inr (failedBinding_entry next _
              (Config.FailedBinding.automaticCommit failed fresh))
      | inr point => exact owesFailure_automaticCommitBlock who next point owed
  | _, _, .reveal _ owner _ _ _ _ next, point, owed => by
      cases point with
      | inl _ => exact owed
      | inr point =>
          have splitDebt : (owner = who ∧ (base next point).get .here = .failure) ∨
              OwesFailure who next point := by
            rcases owed with (past | debt) | (past | debt)
            · exact Or.inl past
            · exact Or.inr (Or.inl debt)
            · exact Or.inl past
            · exact Or.inr (Or.inr debt)
          rcases splitDebt with past | debt
          · exact Or.inl (Or.inl ⟨past.1,
              (base_automaticCommitBlock next point).symm ▸ past.2⟩)
          · rcases owesFailure_automaticCommitBlock who next point debt with indebted | failed
            · exact Or.inl (Or.inr indebted)
            · exact Or.inr (Or.inr failed)

end ProtocolState

namespace CommitRecoveryState

variable {Γ : SourceCtx Player L} {O : Finset VarId}
  {program : SourceProgram Player L Γ O}

/-- Once debt is in both the saved and live point, every closure retains it.
A later retry replaces recall but restores the already indebted saved semantics. -/
theorem close_preserves_owesFailure (who : Player) (state : CommitRecoveryState program)
    (saved : ProtocolState.OwesFailure who program state.saved)
    (live : ProtocolState.OwesFailure who program state.point) :
    ProtocolState.OwesFailure who program state.close.saved ∧
      ProtocolState.OwesFailure who program state.close.point := by
  unfold close
  split
  · split
    · split
      · have debt := (ProtocolState.owesFailure_withHistory who program state.saved
          (ProtocolState.history program state.point)).mpr saved
        exact ⟨debt, debt⟩
      · have debt := ProtocolState.owesFailure_automaticCommitBlock who program _
          ((ProtocolState.owesFailure_withHistory who program state.saved
            (ProtocolState.history program state.point)).mpr saved)
        exact ⟨debt, debt⟩
    · exact ⟨live, live⟩
  · split
    · exact ⟨saved, live⟩
    · exact ⟨live, live⟩

/-- Arbitrary later source moves and resets retain checkpointed own debt.
There is no intended-play or copied-foreign-policy hypothesis. -/
theorem step_preserves_owesFailure (who : Player) (state : CommitRecoveryState program)
    (saved : ProtocolState.OwesFailure who program state.saved)
    (live : ProtocolState.OwesFailure who program state.point)
    (joint : Player → Option (CommitRecoveryMove Player L)) (next : CommitRecoveryState program)
    (supported : next ∈ (state.step joint).support) :
    ProtocolState.OwesFailure who program next.saved ∧
      ProtocolState.OwesFailure who program next.point := by
  obtain ⟨result, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have raw : result.1 ∈
      (ProtocolState.recoveryStep program state.point state.excluded joint).support := by
    rw [← map_val_pmfToSubtype
      (ProtocolState.recoveryStep program state.point state.excluded joint)
      (fun result supported => ProtocolState.recoveryStep_excluded_monotone program state.point
        state.excluded joint result supported)]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, member, rfl⟩
  exact (state.install result.1 result.2).close_preserves_owesFailure who saved
    (ProtocolState.owesFailure_recoveryStep who program state.point state.excluded joint
      result.1 live raw)

/-- Public exclusion or checkpointed latent debt remains permanent under every
later move, including arbitrary foreign actions at newly reached information. -/
theorem step_preserves_excluded_or_owesFailure (who : Player)
    (state : CommitRecoveryState program)
    (owed : who ∈ state.excluded ∨
      (ProtocolState.OwesFailure who program state.saved ∧
        ProtocolState.OwesFailure who program state.point))
    (joint : Player → Option (CommitRecoveryMove Player L)) (next : CommitRecoveryState program)
    (supported : next ∈ (state.step joint).support) :
    who ∈ next.excluded ∨
      (ProtocolState.OwesFailure who program next.saved ∧
        ProtocolState.OwesFailure who program next.point) := by
  rcases owed with excluded | debt
  · exact Or.inl (state.step_excluded_monotone joint next supported excluded)
  · exact Or.inr (state.step_preserves_owesFailure who debt.1 debt.2 joint next supported)

end CommitRecoveryState
end Vegas.SourceProgram
