/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryNonCommitValues
import Vegas.Source.CommitRecoveryCommitEntry
import Vegas.Source.CommitRecoveryAttemptDebt
import Vegas.Source.CommitRecoveryNoMissInformation

/-! # Successful live bindings or a literal own failed binding -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem binding_extension_alternative
    {Γ : SourceCtx Player L} (O : Finset VarId) (who owner : Player) (name : VarId)
    {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst) (unique : (Γ.map Prod.fst).Nodup)
    (config : Config Player L Γ) (value : PublicationResult (L.Val payload))
    (next : Config Player L ((name, .commitment owner payload) :: Γ))
    (state : next.state = Env.cons value config.state) (proper : config.BindingsHoldValues who) :
    next.BindingsHoldValues who ∨ next.FailedBinding who (insert name O) := by
  classical
  by_cases own : owner = who
  · subst owner
    cases value with
    | failure =>
        right
        refine ⟨List.nodup_cons.mpr ⟨fresh, unique⟩, name, payload, .here,
          Finset.mem_insert_self _ _, ?_⟩
        rw [state]
        rfl
    | success value =>
        left
        intro selected ty cell
        rw [state]
        cases cell with
        | here => exact ⟨value, rfl⟩
        | there cell => exact proper cell
  · left
    intro selected ty cell
    rw [state]
    cases cell with
    | here => exact (own rfl).elim
    | there cell => exact proper cell

private theorem binding_alternative_withHistory (who : Player)
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (point : ProtocolState program) (past : History Player L)
    (alternative : ProtocolState.BindingsHoldValues who program point ∨
      ProtocolState.FailedBinding who program point) :
    ProtocolState.BindingsHoldValues who program (ProtocolState.withHistory program point past) ∨
      ProtocolState.FailedBinding who program (ProtocolState.withHistory program point past) :=
  alternative.imp
    (ProtocolState.bindingsHoldValues_withHistory who program point past).mpr
    (ProtocolState.failedBinding_withHistory who program point past).mpr

private theorem recoveryStep_binding_alternative
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (unique : (Γ.map Prod.fst).Nodup) (who : Player) (point : ProtocolState program)
    (excluded : Finset Player) (joint : Player → Option (CommitRecoveryMove Player L))
    (result : ProtocolState program × Finset Player)
    (alternative : ProtocolState.BindingsHoldValues who program point ∨
      ProtocolState.FailedBinding who program point)
    (supported : result ∈ (ProtocolState.recoveryStep program point excluded joint).support) :
    ProtocolState.BindingsHoldValues who program result.1 ∨
      ProtocolState.FailedBinding who program result.1 := by
  classical
  rcases alternative with proper | failed
  · by_cases committing : ProtocolState.atCommit program point = true
    · obtain ⟨Δ, P, name, owner, payload, fresh, guard, suffix, lift, entry, origin,
        atEntry, names⟩ := ProtocolState.exists_committing_entry program point unique committing
      subst point
      have localProper : entry.BindingsHoldValues who :=
        (origin.bindingsHoldValues_lift who _).mp proper
      rw [origin.recoveryStep_lift] at supported
      obtain ⟨target, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      have embed (config : Config Player L ((name, .commitment owner payload) :: Δ))
          (alternative : config.BindingsHoldValues who ∨ config.FailedBinding who (insert name P)) :
          ProtocolState.BindingsHoldValues who program
              (lift (.inr (ProtocolState.entry suffix config))) ∨
            ProtocolState.FailedBinding who program
              (lift (.inr (ProtocolState.entry suffix config))) := by
        rcases alternative with values | debt
        · exact Or.inl ((origin.bindingsHoldValues_lift who _).mpr
            ((ProtocolState.bindingsHoldValues_entry who suffix config).mpr values))
        · exact Or.inr (origin.failedBinding_lift who _
            (ProtocolState.failedBinding_entry suffix config debt))
      simp only [ProtocolState.recoveryStep, ProtocolState.entry, Sum.elim_inl] at member
      split at member
      · rw [PMF.mem_support_pure_iff] at member
        subst target
        exact embed _ (binding_extension_alternative P who owner name fresh names entry .failure
          (automaticCommit name owner payload entry) rfl localProper)
      · rw [PMF.mem_support_pure_iff] at member
        subst target
        exact embed _ (binding_extension_alternative P who owner name fresh names entry _
          (commitSuccessor name guard entry
            (OwnAction.binding owner name payload ((joint owner).map (·.action)))) rfl localProper)
    · exact Or.inl (ProtocolState.recoveryStep_noncommit_bindingsHoldValues program point
        excluded joint result who (Bool.eq_false_iff.mpr committing) proper supported)
  · exact Or.inr (ProtocolState.failedBinding_recoveryStep who program point excluded joint result
      failed supported)

private theorem automatic_binding_alternative (who : Player)
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (unique : (Γ.map Prod.fst).Nodup) (point : ProtocolState program)
    (alternative : ProtocolState.BindingsHoldValues who program point ∨
      ProtocolState.FailedBinding who program point) :
    (ProtocolState.BindingsHoldValues who program
      (ProtocolState.automaticCommitBlock program point)) ∨
      ProtocolState.FailedBinding who program
        (ProtocolState.automaticCommitBlock program point) := by
  induction program with
  | ret => exact alternative
  | sample name fresh law next ih =>
      cases point with
      | inl => exact alternative
      | inr point => exact ih (List.nodup_cons.mpr ⟨fresh, unique⟩) point alternative
  | @commit Γ O name owner payload fresh guard next ih =>
      have names := List.nodup_cons.mpr ⟨fresh, unique⟩
      cases point with
      | inl config =>
          have alternative : (automaticCommit name owner payload config).BindingsHoldValues who ∨
              (automaticCommit name owner payload config).FailedBinding who (insert name O) := by
            rcases alternative with proper | failed
            · exact binding_extension_alternative O who owner name fresh unique config .failure
                _ rfl proper
            · exact Or.inr (Config.FailedBinding.automaticCommit failed fresh)
          apply ih names (ProtocolState.entry next _)
          exact alternative.imp (ProtocolState.bindingsHoldValues_entry who next _).mpr
            (ProtocolState.failedBinding_entry next _)
      | inr point => exact ih names point alternative
  | reveal published owner name fresh selected unresolved next ih =>
      cases point with
      | inl => exact alternative
      | inr point =>
          rcases alternative with proper | past | failed
          · exact (ih (List.nodup_cons.mpr ⟨fresh, unique⟩) point (Or.inl proper)).imp id Or.inr
          · exact Or.inr (Or.inl ⟨past.1,
              (ProtocolState.base_automaticCommitBlock next point).symm ▸ past.2⟩)
          · exact (ih (List.nodup_cons.mpr ⟨fresh, unique⟩) point (Or.inr failed)).imp id Or.inr

private theorem close_binding_alternative
    {Γ : SourceCtx Player L} {O : Finset VarId} {program : SourceProgram Player L Γ O}
    (unique : (Γ.map Prod.fst).Nodup) (who : Player) (state : CommitRecoveryState program)
    (saved : ProtocolState.BindingsHoldValues who program state.saved ∨
      ProtocolState.FailedBinding who program state.saved)
    (live : ProtocolState.BindingsHoldValues who program state.point ∨
      ProtocolState.FailedBinding who program state.point) :
    (ProtocolState.BindingsHoldValues who program state.close.saved ∨
      ProtocolState.FailedBinding who program state.close.saved) ∧
    (ProtocolState.BindingsHoldValues who program state.close.point ∨
      ProtocolState.FailedBinding who program state.close.point) := by
  unfold CommitRecoveryState.close
  split
  · split
    · split
      · have restored := binding_alternative_withHistory who program state.saved
          (ProtocolState.history program state.point) saved
        exact ⟨restored, restored⟩
      · have restored := automatic_binding_alternative who program unique _
          (binding_alternative_withHistory who program state.saved
            (ProtocolState.history program state.point) saved)
        exact ⟨restored, restored⟩
    · exact ⟨live, live⟩
  · split
    · exact ⟨saved, live⟩
    · exact ⟨live, live⟩

/-- An initialized original source history has either successful own bindings
or a literal failed binding, separately at its saved and live points. Earlier
canceled choices remain in history; close selects its actual saved or live
branch before the alternative is propagated further. -/
theorem Setup.commitRecovery_bindingsHoldValues_or_failedBinding
    (setup : Setup (Player := Player) (L := L)) (wellFormed : setup.WellFormed)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) (who : Player) :
    ∀ current, state = some current →
      (ProtocolState.BindingsHoldValues who setup.program current.saved ∨
        ProtocolState.FailedBinding who setup.program current.saved) ∧
      (ProtocolState.BindingsHoldValues who setup.program current.point ∨
        ProtocolState.FailedBinding who setup.program current.point) := by
  induction trace with
  | start => intro current impossible; cases impossible
  | @extend before after prior joint _ supported ih =>
      intro current equality
      cases before with
      | none =>
          obtain ⟨inputs, member, target⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          have same := Option.some.inj (target.trans equality)
          subst current
          have initial : ProtocolState.BindingsHoldValues who setup.program
              (ProtocolState.entry setup.program (setup.initialConfig inputs)) :=
            (ProtocolState.bindingsHoldValues_entry who setup.program _).mpr
              (fun cell => wellFormed.initialValues inputs member cell)
          exact ⟨Or.inl initial, Or.inl initial⟩
      | some previous =>
          obtain ⟨next, member, target⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          have same := Option.some.inj (target.trans equality)
          subst current
          obtain ⟨result, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
          have raw : result.1 ∈
              (ProtocolState.recoveryStep setup.program previous.point previous.excluded
                joint).support := by
            rw [← map_val_pmfToSubtype
              (ProtocolState.recoveryStep setup.program previous.point previous.excluded joint)
              (fun result supported => ProtocolState.recoveryStep_excluded_monotone setup.program
                previous.point previous.excluded joint result supported)]
            exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, reached, rfl⟩
          exact close_binding_alternative setup.namesNodup who _ (ih previous rfl).1
            (recoveryStep_binding_alternative setup.program setup.namesNodup who previous.point
              previous.excluded joint result.1 (ih previous rfl).2 raw)

end Vegas.SourceProgram
