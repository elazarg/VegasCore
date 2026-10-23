/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryNoMiss
import Vegas.Source.CommitRecoveryCommitUnique

/-! # Actual commitment steps replayed with the saved exclusion set

Only new foreign omissions are removed. The surviving owner's original raw
choice and complete typed view are retained. Automatic foreign slots may be
replaced by active accepted failed bindings without revealing a private value.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace Config

omit [IExpr.ResultTypes L] in
private theorem automaticCommit_view_eq_commit {Γ : SourceCtx Player L} {payload : L.Ty}
    (who owner : Player) (different : owner ≠ who) (name : VarId)
    (guard : SourceGuard L Γ owner name payload) (config : Config Player L Γ)
    (choice : PublicationResult (L.Val payload)) :
    (automaticCommit name owner payload config).view who =
      (commitSuccessor name guard config choice).view who := by
  apply (Config.automaticCommit_view_eq_failure who owner different name guard config).trans
  exact Config.view_commit_congr name guard config config rfl .failure choice
    (fun same => (different same).elim)

end Config

namespace ProtocolState

/-- Replaying one real source commitment with no new omissions preserves the
surviving owner's entire typed view. No equality of foreign private values or
of the original/current exclusion sets is assumed. -/
theorem recoveryStep_noMiss_observe (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (first second : ProtocolState program),
      observe who program first = observe who program second →
      atCommit program first = true →
      ∀ (leftExcluded saved : Finset Player), who ∉ leftExcluded → who ∉ saved →
      ∀ (left right : Player → Option (CommitRecoveryMove Player L)), left who = right who →
      (∀ owner, CommitRecoveryMove.missed (right owner) = false) →
      ∀ l ∈ (recoveryStep program first leftExcluded left).support,
      ∀ r ∈ (recoveryStep program second saved right).support,
        observe who program l.1 = observe who program r.1 ∧ r.2 = saved
  | _, _, .ret _, _, _, _, committing, _, _, _, _, _, _, _, _, _, _, _, _ => by
      cases committing
  | _, _, .sample _ _ _ next, first, second, same, committing, leftExcluded, saved,
      leftSurvives, savedSurvives, left, right, ownChoice, noMiss, l, lm, r, rm => by
      cases first with
      | inl _ => cases committing
      | inr first =>
          cases second with
          | inl _ => cases same
          | inr second =>
              simp only [recoveryStep, Sum.elim_inr] at lm rm
              obtain ⟨lowerLeft, lowerLeftMember, leftShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next first leftExcluded left) _).mp lm
              obtain ⟨lowerRight, lowerRightMember, rightShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next second saved right) _).mp rm
              subst l; subst r
              obtain ⟨view, excluded⟩ := recoveryStep_noMiss_observe who next first second
                (Sum.inr.inj same) committing leftExcluded saved leftSurvives savedSurvives
                left right ownChoice noMiss lowerLeft lowerLeftMember lowerRight lowerRightMember
              exact ⟨congrArg Sum.inr view, excluded⟩
  | _, _, .commit name owner fresh guard next, first, second, same, committing, leftExcluded,
      saved, leftSurvives, savedSurvives, left, right, ownChoice, noMiss, l, lm, r, rm => by
      cases first with
      | inl first =>
          cases second with
          | inr _ => cases same
          | inl second =>
              have old := Sum.inl.inj same
              simp only [recoveryStep, Sum.elim_inl] at lm rm
              by_cases leftInactive : owner ∈ leftExcluded
              · by_cases rightInactive : owner ∈ saved
                · rw [ite_eq_left leftInactive, PMF.mem_support_pure_iff] at lm
                  rw [ite_eq_left rightInactive, PMF.mem_support_pure_iff] at rm
                  subst l; subst r
                  exact ⟨congrArg Sum.inr (ProtocolState.observe_entry_congr who next _ _
                    (Config.view_automaticCommit_congr who owner name _ first second old)), rfl⟩
                · have foreign : owner ≠ who := fun equal => leftSurvives (equal ▸ leftInactive)
                  rw [ite_eq_left leftInactive, PMF.mem_support_pure_iff] at lm
                  rw [ite_eq_right rightInactive, PMF.mem_support_pure_iff] at rm
                  subst l; subst r
                  refine ⟨congrArg Sum.inr (ProtocolState.observe_entry_congr who next _ _ ?_), ?_⟩
                  · exact (Config.view_automaticCommit_congr who owner name _
                      first second old).trans
                      (Config.automaticCommit_view_eq_commit who owner foreign name guard second _)
                  · simp only [noMiss owner, Bool.false_eq_true, ↓reduceIte]
              · by_cases rightInactive : owner ∈ saved
                · have foreign : owner ≠ who := fun equal => savedSurvives (equal ▸ rightInactive)
                  rw [ite_eq_right leftInactive, PMF.mem_support_pure_iff] at lm
                  rw [ite_eq_left rightInactive, PMF.mem_support_pure_iff] at rm
                  subst l; subst r
                  refine ⟨congrArg Sum.inr (ProtocolState.observe_entry_congr who next _ _ ?_), rfl⟩
                  exact (Config.automaticCommit_view_eq_commit who owner foreign name guard
                    first _).symm.trans
                    (Config.view_automaticCommit_congr who owner name _ first second old)
                · rw [ite_eq_right leftInactive, PMF.mem_support_pure_iff] at lm
                  rw [ite_eq_right rightInactive, PMF.mem_support_pure_iff] at rm
                  subst l; subst r
                  refine ⟨congrArg Sum.inr (ProtocolState.observe_entry_congr who next _ _ ?_), ?_⟩
                  · exact Config.view_commit_congr name guard first second old _ _ (fun equal => by
                      subst owner
                      rw [ownChoice])
                  · simp only [noMiss owner, Bool.false_eq_true, ↓reduceIte]
      | inr first =>
          cases second with
          | inl _ => cases same
          | inr second =>
              simp only [recoveryStep, Sum.elim_inr] at lm rm
              obtain ⟨lowerLeft, lowerLeftMember, leftShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next first leftExcluded left) _).mp lm
              obtain ⟨lowerRight, lowerRightMember, rightShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next second saved right) _).mp rm
              subst l; subst r
              obtain ⟨view, excluded⟩ := recoveryStep_noMiss_observe who next first second
                (Sum.inr.inj same) committing leftExcluded saved leftSurvives savedSurvives
                left right ownChoice noMiss lowerLeft lowerLeftMember lowerRight lowerRightMember
              exact ⟨congrArg Sum.inr view, excluded⟩
  | _, _, .reveal _ _ _ _ _ _ next, first, second, same, committing, leftExcluded, saved,
      leftSurvives, savedSurvives, left, right, ownChoice, noMiss, l, lm, r, rm => by
      cases first with
      | inl _ => cases committing
      | inr first =>
          cases second with
          | inl _ => cases same
          | inr second =>
              simp only [recoveryStep, Sum.elim_inr] at lm rm
              obtain ⟨lowerLeft, lowerLeftMember, leftShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next first leftExcluded left) _).mp lm
              obtain ⟨lowerRight, lowerRightMember, rightShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next second saved right) _).mp rm
              subst l; subst r
              obtain ⟨view, excluded⟩ := recoveryStep_noMiss_observe who next first second
                (Sum.inr.inj same) committing leftExcluded saved leftSurvives savedSurvives
                left right ownChoice noMiss lowerLeft lowerLeftMember lowerRight lowerRightMember
              exact ⟨congrArg Sum.inr view, excluded⟩

end ProtocolState
namespace CommitRecoveryState

variable {Γ : SourceCtx Player L} {O : Finset VarId}
  {program : SourceProgram Player L Γ O}

/-- Existing source progress can be chosen with no new omission flag. This
changes neither the action menu nor the original transition kernel. -/
theorem exists_noMiss_joint (state : CommitRecoveryState program) :
    ∃ joint, IsLegalJoint state.Active state.available joint ∧
      ∀ owner, CommitRecoveryMove.missed (joint owner) = false := by
  obtain ⟨original, legal⟩ := state.progress
  let repaired := fun owner => (original owner).map
    (fun move => ({ move with missing := false } : CommitRecoveryMove Player L))
  refine ⟨repaired, ?_, ?_⟩
  · intro owner
    have offered := legal owner
    cases chosen : original owner with
    | none => simpa only [repaired, chosen, Option.map_none] using offered
    | some move =>
        rw [chosen] at offered
        simp only [repaired, chosen, Option.map_some]
        refine ⟨offered.1, offered.2.1, ?_⟩
        split
        · intro impossible
          cases impossible
        · rfl
  · intro owner
    cases chosen : original owner <;>
      simp only [repaired, chosen, Option.map_none, Option.map_some,
        CommitRecoveryMove.missed, Option.elim_none, Option.elim_some]

/-- A genuinely legal surviving owner's choice can be retained verbatim in a
legal no-new-omission joint action. The remaining players use source progress. -/
theorem exists_noMiss_joint_with (state : CommitRecoveryState program) (who : Player)
    (choice : Option (CommitRecoveryMove Player L))
    (offered : match choice with
      | none => ¬ state.Active who
      | some move => state.Active who ∧ move ∈ state.available who)
    (notMissing : CommitRecoveryMove.missed choice = false) :
    ∃ joint, IsLegalJoint state.Active state.available joint ∧ joint who = choice ∧
      ∀ owner, CommitRecoveryMove.missed (joint owner) = false := by
  obtain ⟨original, legal, noMiss⟩ := state.exists_noMiss_joint
  refine ⟨Function.update original who choice, ?_, Function.update_self .., ?_⟩
  · intro owner
    by_cases same : owner = who
    · subst owner
      cases choice <;> simpa only [Function.update_self] using offered
    · simpa only [Function.update_of_ne same] using legal owner
  · intro owner
    by_cases same : owner = who
    · subst owner
      simpa only [Function.update_self] using notMissing
    · simpa only [Function.update_of_ne same] using noMiss owner

/-- A real source commitment has a legal no-new-miss replay from an equal
surviving-owner view. The original choice, including accepted failure, is
retained and the resulting observation follows from the actual kernels. -/
theorem noMiss_instruction (who : Player) (first second : CommitRecoveryState program)
    (sameView : ProtocolState.observe who program first.point =
      ProtocolState.observe who program second.point)
    (committing : ProtocolState.atCommit program first.point = true)
    (leftSurvives : who ∉ first.excluded) (rightSurvives : who ∉ second.excluded)
    (left : Player → Option (CommitRecoveryMove Player L))
    (legal : IsLegalJoint first.Active first.available left)
    (result : ProtocolState program × Finset Player)
    (supported : result ∈
      (ProtocolState.recoveryStep program first.point first.excluded left).support)
    (survives : who ∉ result.2) :
    ∃ right : Player → Option (CommitRecoveryMove Player L),
      IsLegalJoint second.Active second.available right ∧ right who = left who ∧
      (∀ owner, CommitRecoveryMove.missed (right owner) = false) ∧
      ∃ next ∈ (ProtocolState.recoveryStep program second.point second.excluded right).support,
        ProtocolState.observe who program result.1 = ProtocolState.observe who program next.1 ∧
          next.2 = second.excluded := by
  have actors :
      ProtocolState.actor program first.point = ProtocolState.actor program second.point :=
    (ProtocolState.actor_observe_eq program first.point who).symm.trans
      ((congrArg (ProtocolView.actor who program) sameView).trans
        (ProtocolState.actor_observe_eq program second.point who))
  have active : first.Active who ↔ second.Active who := by
    simp only [Active, actors, leftSurvives, rightSurvives, not_false_eq_true, and_true]
  have offered : match left who with
      | none => ¬ second.Active who
      | some move => second.Active who ∧ move ∈ second.available who := by
    have original := legal who
    cases chosen : left who with
    | none =>
        rw [chosen] at original
        exact fun yes => original (active.mpr yes)
    | some move =>
        rw [chosen] at original
        exact ⟨active.mp original.1, by
          simpa only [available, ← sameView] using original.2⟩
  have notMissing : CommitRecoveryMove.missed (left who) = false := by
    cases chosen : left who with
    | none => rfl
    | some move =>
        have original := legal who
        rw [chosen] at original
        by_cases missing : move.missing = true
        · exact (survives (ProtocolState.recoveryStep_missed_excludes who program first.point
            first.excluded left committing original.1.1
              (by simp only [chosen, CommitRecoveryMove.missed, Option.elim_some, missing])
              result supported)).elim
        · exact Bool.eq_false_iff.mpr missing
  obtain ⟨right, rightLegal, ownChoice, noMiss⟩ :=
    second.exists_noMiss_joint_with who (left who) offered notMissing
  have secondCommit : ProtocolState.atCommit program second.point = true := by
    rw [← ProtocolState.atCommit_observe program second.point who, ← sameView,
      ProtocolState.atCommit_observe, committing]
  obtain ⟨next, pure⟩ := ProtocolState.recoveryStep_commit_pure program second.point
    second.excluded right secondCommit
  have nextMember : next ∈
      (ProtocolState.recoveryStep program second.point second.excluded right).support := by
    rw [pure, PMF.mem_support_pure_iff]
  refine ⟨right, rightLegal, ownChoice, noMiss, next, nextMember, ?_⟩
  exact ProtocolState.recoveryStep_noMiss_observe who program first.point second.point sameView
    committing first.excluded second.excluded leftSurvives rightSurvives left right ownChoice.symm
    noMiss result supported next nextMember

end CommitRecoveryState

end Vegas.SourceProgram
