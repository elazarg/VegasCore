/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryVoluntaryFailure

/-! # Original owned action words through source recovery transitions -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

/-- Equal complete source observations identify the original owned word,
regardless of foreign exclusions or earlier rollback generations. -/
theorem history_eq_of_observe (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (first second : ProtocolState program),
      observe who program first = observe who program second →
        history program first who = history program second who
  | _, _, .ret _, first, second, same => congrArg Prod.snd same
  | _, _, .sample _ _ _ next, first, second, same => by
      cases first <;> cases second
      · exact congrArg Prod.snd (Sum.inl.inj same)
      · cases same
      · cases same
      · exact history_eq_of_observe who next _ _ (Sum.inr.inj same)
  | _, _, .commit _ _ _ _ next, first, second, same => by
      cases first <;> cases second
      · exact congrArg Prod.snd (Sum.inl.inj same)
      · cases same
      · cases same
      · exact history_eq_of_observe who next _ _ (Sum.inr.inj same)
  | _, _, .reveal _ _ _ _ _ _ next, first, second, same => by
      cases first <;> cases second
      · exact congrArg Prod.snd (Sum.inl.inj same)
      · cases same
      · cases same
      · exact history_eq_of_observe who next _ _ (Sum.inr.inj same)

/-- A genuine recovery instruction records exactly the active surviving
observer's original action. Foreign automatic failures record no action for it. -/
theorem recoveryStep_own_history (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program)
      (excluded : Finset Player) (joint : Player → Option (CommitRecoveryMove Player L)),
      IsLegalJoint (fun owner => actor program point = some owner ∧ owner ∉ excluded)
        (fun owner => ProtocolView.recoveryAvailable owner program (observe owner program point))
        joint → who ∉ excluded →
      ∀ result ∈ (recoveryStep program point excluded joint).support,
      history program result.1 who = history program point who ++
        ((joint who).map (·.action)).toList
  | _, _, .ret _, point, excluded, joint, legal, _survives, result, supported => by
      have chosen : joint who = none := by
        cases selected : joint who with
        | none => rfl
        | some move => have active := (legal who); rw [selected] at active; cases active.1.1
      simp only [recoveryStep, PMF.mem_support_pure_iff] at supported
      subst result
      simp only [chosen, Option.map_none, Option.toList_none, List.append_nil]
  | _, _, .sample name fresh law next, point, excluded, joint, legal, survives,
      result, supported => by
      cases point with
      | inl config =>
          have chosen : joint who = none := by
            cases selected : joint who with
            | none => rfl
            | some move => have active := legal who; rw [selected] at active; cases active.1.1
          obtain ⟨value, _drawn, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          simp only [history, Sum.elim_inl, Sum.elim_inr, history_entry, sampleSuccessor,
            chosen, Option.map_none, Option.toList_none, List.append_nil]
      | inr point =>
          obtain ⟨after, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          exact recoveryStep_own_history who next point excluded joint legal survives after reached
  | _, _, .commit name owner fresh guard next, point, excluded, joint, legal, survives,
      result, supported => by
      cases point with
      | inl config =>
          by_cases own : owner = who
          · subst owner
            cases selected : joint who with
            | none =>
                have denied := legal who
                rw [selected] at denied
                exact (denied ⟨rfl, survives⟩).elim
            | some move =>
                have offered := legal who
                rw [selected] at offered
                obtain ⟨choice, _admitted, action⟩ := offered.2.1
                simp only [recoveryStep, Sum.elim_inl, survives, ↓reduceIte,
                  PMF.mem_support_pure_iff] at supported
                subst result
                simp only [history, Sum.elim_inl, Sum.elim_inr, history_entry, commitSuccessor,
                  Function.update_self, selected, Option.map_some, action, OwnAction.binding_commit,
                  Option.toList_some]
          · have chosen : joint who = none := by
              cases selected : joint who with
              | none => rfl
              | some move =>
                  have active := legal who
                  rw [selected] at active
                  exact (own (Option.some.inj active.1.1)).elim
            simp only [recoveryStep, Sum.elim_inl] at supported
            split at supported
            · rw [PMF.mem_support_pure_iff] at supported
              subst result
              simp only [history, Sum.elim_inl, Sum.elim_inr, history_entry, automaticCommit,
                chosen, Option.map_none, Option.toList_none, List.append_nil]
            · rw [PMF.mem_support_pure_iff] at supported
              subst result
              simp only [history, Sum.elim_inl, Sum.elim_inr, history_entry, commitSuccessor,
                Function.update_of_ne (Ne.symm own), chosen, Option.map_none, Option.toList_none,
                List.append_nil]
      | inr point =>
          obtain ⟨after, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          exact recoveryStep_own_history who next point excluded joint legal survives after reached
  | _, _, .reveal published owner name fresh source unresolved next, point, excluded, joint,
      legal, survives, result, supported => by
      cases point with
      | inl config =>
          by_cases own : owner = who
          · subst owner
            cases selected : joint who with
            | none =>
                have denied := legal who
                rw [selected] at denied
                exact (denied ⟨rfl, survives⟩).elim
            | some move =>
                have offered := legal who
                rw [selected] at offered
                obtain ⟨disclose, action⟩ := offered.2.1
                simp only [recoveryStep, Sum.elim_inl, survives, ↓reduceIte,
                  PMF.mem_support_pure_iff] at supported
                subst result
                simp only [history, Sum.elim_inl, Sum.elim_inr, history_entry, revealSuccessor,
                  Function.update_self, selected, Option.map_some, action, OwnAction.disclosure,
                  Option.toList_some]
          · have chosen : joint who = none := by
              cases selected : joint who with
              | none => rfl
              | some move =>
                  have active := legal who
                  rw [selected] at active
                  exact (own (Option.some.inj active.1.1)).elim
            simp only [recoveryStep, Sum.elim_inl, PMF.mem_support_pure_iff] at supported
            subst result
            split
            · simp only [history, Sum.elim_inl, Sum.elim_inr, history_entry, chosen,
                Option.map_none, Option.toList_none, List.append_nil]
            · simp only [history, Sum.elim_inl, Sum.elim_inr, history_entry, revealSuccessor,
                Function.update_of_ne (Ne.symm own), chosen, Option.map_none, Option.toList_none,
                List.append_nil]
      | inr point =>
          obtain ⟨after, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          exact recoveryStep_own_history who next point excluded joint legal survives after reached

end ProtocolState

namespace CommitRecoveryState

/-- Actual source phase closure preserves the exact owned word produced by
its instruction, including a retry's complete original attempted actions. -/
theorem step_own_history {Γ : SourceCtx Player L} {O : Finset VarId}
    {program : SourceProgram Player L Γ O} (state : CommitRecoveryState program)
    (who : Player) (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : IsLegalJoint state.Active state.available joint)
    (next : CommitRecoveryState program) (supported : next ∈ (state.step joint).support)
    (survives : who ∉ next.excluded) :
    ProtocolState.history program next.point who =
      ProtocolState.history program state.point who ++ ((joint who).map (·.action)).toList := by
  have before : who ∉ state.excluded := fun excluded =>
    survives (state.step_excluded_monotone joint next supported excluded)
  obtain ⟨result, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have rawMember : result.1 ∈
      (ProtocolState.recoveryStep program state.point state.excluded joint).support := by
    rw [← map_val_pmfToSubtype
      (ProtocolState.recoveryStep program state.point state.excluded joint)
      (fun result supported => ProtocolState.recoveryStep_excluded_monotone
        program state.point state.excluded joint result supported)]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, reached, rfl⟩
  rw [close_history]
  exact ProtocolState.recoveryStep_own_history who program state.point state.excluded joint
    legal before result.1 rawMember

end CommitRecoveryState

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

/-- An original move by an owner that survives this source transition has
no omission marker, including when foreign owners were already excluded. -/
theorem commitRecovery_surviving_joint_lift
    {before after : setup.commitRecoveryProtocol.State}
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal before joint)
    (supported : after ∈ (setup.commitRecoveryProtocol.step before ⟨joint, legal⟩).support)
    (who : Player) (survives : who ∉ (setup.commitRecoveryPublic after).1) :
    joint who = CommitRecoveryMove.lift ((joint who).map (·.action)) := by
  cases before with
  | none =>
      have offered := legal.2 who
      cases chosen : joint who with
      | none => rfl
      | some move => rw [chosen] at offered; exact offered.1.elim
  | some current =>
      obtain ⟨next, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      have offered := legal.2 who
      cases chosen : joint who with
      | none => rfl
      | some move =>
          rw [chosen] at offered
          have noMiss : move.missing = false := by
            by_cases active : ProtocolState.atCommit setup.program current.point = true
            · cases missing : move.missing with
              | false => rfl
              | true =>
                  exact (survives (current.missed_excludes who joint active offered.1.1
                    (by simp only [chosen, CommitRecoveryMove.missed, Option.elim_some, missing])
                    next reached)).elim
            · have notCommit : ProtocolState.atCommit setup.program current.point = false :=
                Bool.eq_false_iff.mpr active
              simpa only [CommitRecoveryState.available, ProtocolView.recoveryAvailable,
                Set.mem_ofPred_eq, ProtocolState.atCommit_observe, notCommit,
                Bool.false_eq_true, ↓reduceIte] using offered.2.2
          simp only [CommitRecoveryMove.lift, Option.map_some]
          cases move
          simp_all

/-- Permanent source exclusions are monotone across the original setup draw
and every actual recovery transition. -/
theorem commitRecovery_step_excluded_subset
    {before after : setup.commitRecoveryProtocol.State}
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal before joint)
    (supported : after ∈ (setup.commitRecoveryProtocol.step before ⟨joint, legal⟩).support) :
    (setup.commitRecoveryPublic before).1 ⊆ (setup.commitRecoveryPublic after).1 := by
  cases before with
  | none => exact Finset.empty_subset _
  | some current =>
      obtain ⟨next, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact current.step_excluded_monotone joint next reached

end Setup

end Vegas.SourceProgram
