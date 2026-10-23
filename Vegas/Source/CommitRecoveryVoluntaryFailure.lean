/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryContinuingMenu
import Vegas.Source.CommitBlockRecovery

/-! # Actual permanent exclusion after source omission or withholding -/

noncomputable section

namespace Vegas.SourceProgram.ProtocolState

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

theorem recoveryStep_withholding_excludes (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (point : ProtocolState program) (excluded : Finset Player)
      (joint : Player → Option (CommitRecoveryMove Player L)) (move : CommitRecoveryMove Player L),
      joint who = some move → actor program point = some who →
      move ∈ ProtocolView.recoveryAvailable who program (observe who program point) →
      atCommit program point = false → move.action.IsFailure →
      ∀ result ∈ (recoveryStep program point excluded joint).support, who ∈ result.2
  | _, _, .ret _, _, _, _, _, _, acting, _, _, _, _, _ => by cases acting
  | _, _, .sample _ _ _ next, point, excluded, joint, move, chosen, acting, offered,
      notCommit, failure, result, reached => by
      cases point with
      | inl _ => cases acting
      | inr point =>
          simp only [recoveryStep, Sum.elim_inr, PMF.support_map] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact recoveryStep_withholding_excludes who next point excluded joint move chosen
            acting offered notCommit failure after supported
  | _, _, .commit _ _ _ _ next, point, excluded, joint, move, chosen, acting, offered,
      notCommit, failure, result, reached => by
      cases point with
      | inl _ => cases notCommit
      | inr point =>
          simp only [recoveryStep, Sum.elim_inr, PMF.support_map] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact recoveryStep_withholding_excludes who next point excluded joint move chosen
            acting offered notCommit failure after supported
  | _, _, .reveal published owner name _ source _ next, point, excluded, joint, move,
      chosen, acting, offered, notCommit, failure, result, reached => by
      cases point with
      | inl config =>
          have own : owner = who := Option.some.inj acting
          subst owner
          by_cases already : who ∈ excluded
          · exact recoveryStep_excluded_monotone _ _ _ _ _ reached already
          · obtain ⟨disclose, selected⟩ := offered.1
            have withheld : disclose = false := by
              simpa only [selected, OwnAction.IsFailure] using failure
            have packet : (joint who).map (·.action) = some (.reveal who name false) := by
              rw [chosen]
              simp only [Option.map_some]
              rw [selected, withheld]
            have failed : (revealSuccessor published source config false).state.get .here =
                .failure := by simp [revealSuccessor]
            simp only [recoveryStep, Sum.elim_inl, already, ↓reduceIte, packet,
              OwnAction.disclosure, failed, PMF.mem_support_pure_iff] at reached
            subst result
            exact Finset.mem_insert_self _ _
      | inr point =>
          simp only [recoveryStep, Sum.elim_inr, PMF.support_map] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact recoveryStep_withholding_excludes who next point excluded joint move chosen
            acting offered notCommit failure after supported

theorem recoveryStep_voluntaryFailure_excludes
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (point : ProtocolState program) (excluded : Finset Player) (who : Player)
    (joint : Player → Option (CommitRecoveryMove Player L)) (move : CommitRecoveryMove Player L)
    (chosen : joint who = some move) (acting : actor program point = some who)
    (offered : move ∈ ProtocolView.recoveryAvailable who program (observe who program point))
    (failure : move.missing = true ∨ (atCommit program point = false ∧ move.action.IsFailure))
    (result : ProtocolState program × Finset Player)
    (reached : result ∈ (recoveryStep program point excluded joint).support) :
    who ∈ result.2 := by
  rcases failure with missing | ⟨notCommit, withholding⟩
  · have committing : atCommit program point = true := by
      cases current : atCommit program point with
      | true => rfl
      | false =>
          have noMiss := offered.2
          simp only [atCommit_observe, current, Bool.false_eq_true, ↓reduceIte] at noMiss
          rw [missing] at noMiss
          cases noMiss
    exact recoveryStep_missed_excludes who program point excluded joint committing acting
      (by simpa only [CommitRecoveryMove.missed, chosen, Option.elim_some] using missing)
      result reached
  · exact recoveryStep_withholding_excludes who program point excluded joint move chosen
      acting offered notCommit withholding result reached

end Vegas.SourceProgram.ProtocolState

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- At every genuine source site, a choice outside the continuing menu puts
the acting owner in the actual permanent excluded set after this one step. -/
theorem commitRecovery_voluntaryFailure_step (who : Player)
    {state : setup.commitRecoveryProtocol.State} (trace : setup.commitRecoveryProtocol.Trace state)
    (choice : setup.commitRecoveryModel.Choice who (setup.commitRecoveryModel.infoOf who trace))
    (fails : ¬ setup.CommitRecoveryContinues who
      (setup.commitRecoveryModel.infoOf who trace) choice.1)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal state joint) (chosen : joint who = choice.1)
    (target : setup.commitRecoveryProtocol.State)
    (reached : target ∈ (setup.commitRecoveryProtocol.step state ⟨joint, legal⟩).support) :
    who ∈ (setup.commitRecoveryPublic target).1 := by
  classical
  cases selected : choice.1 with
  | none =>
      exact (fails (fun _ impossible => by rw [selected] at impossible; cases impossible)).elim
  | some move =>
      have failure : move.missing = true ∨
          ((setup.commitRecoveryModel.infoOf who trace).1.1.1.elim false
            (ProtocolView.atCommit who setup.program) = false ∧ move.action.IsFailure) := by
        by_cases missing : move.missing = true
        · exact Or.inl missing
        · right
          have noMiss : move.missing = false := Bool.eq_false_iff.mpr missing
          by_contra denied
          apply fails
          intro action equality
          rw [selected] at equality
          cases Option.some.inj equality
          exact ⟨noMiss, fun notCommit failed => denied ⟨notCommit, failed⟩⟩
      have permitted := legal.2 who
      rw [chosen, selected] at permitted
      cases state with
      | none => exact permitted.1.elim
      | some current =>
          rw [setup.commitRecovery_atCommit_info who trace] at failure
          change move.missing = true ∨
            (ProtocolState.atCommit setup.program current.point = false ∧
              move.action.IsFailure) at failure
          obtain ⟨after, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
          obtain ⟨raw, rawSupport, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          have rawMember : raw.1 ∈ (ProtocolState.recoveryStep setup.program current.point
              current.excluded joint).support := by
            rw [← map_val_pmfToSubtype
              (ProtocolState.recoveryStep setup.program current.point current.excluded joint)
              (fun result supported => ProtocolState.recoveryStep_excluded_monotone
                setup.program current.point current.excluded joint result supported)]
            exact (PMF.mem_support_map_iff _ _ _).mpr ⟨raw, rawSupport, rfl⟩
          change who ∈ (current.install raw.1 raw.2).close.excluded
          rw [CommitRecoveryState.close_excluded]
          exact ProtocolState.recoveryStep_voluntaryFailure_excludes setup.program current.point
            current.excluded who joint move (chosen.trans selected) permitted.1.1 permitted.2
            failure raw.1 rawMember

end Vegas.SourceProgram.Setup
