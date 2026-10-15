/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryClear
import Vegas.Source.IntendedPlay

/-! # Intended source actions have no recovery exclusions or retries -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

/-- With intended source choices and no physical omission, the complete joint
source-point/exclusion law is the original source law paired with no exclusion. -/
theorem recoveryStep_intended_joint : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (joint : Player → Option (CommitRecoveryMove Player L)),
    Intended program point →
    (∀ who, ProtocolView.intendedMenu who program (observe who program point)
      ((joint who).map (·.action))) →
    (∀ who, CommitRecoveryMove.missed (joint who) = false) →
    recoveryStep program point ∅ joint =
      (step program point (fun who => (joint who).map (·.action))).map
        (fun target => (target, ∅))
  | _, _, .ret _, _, _, _, _, _ => by simp [recoveryStep, step, PMF.pure_map]
  | _, _, .sample _ _ _ next, point, joint, intended, legal, noMiss => by
      cases point with
      | inl _ => simp only [recoveryStep, step, Sum.elim_inl, PMF.map_comp]; rfl
      | inr later =>
          simp only [recoveryStep, step, Sum.elim_inr]
          rw [recoveryStep_intended_joint next later joint intended legal noMiss,
            PMF.map_comp, PMF.map_comp]
          rfl
  | _, _, .commit _ owner _ _ next, point, joint, intended, legal, noMiss => by
      cases point with
      | inl _ => simp [recoveryStep, step, noMiss owner, PMF.pure_map]
      | inr later =>
          simp only [recoveryStep, step, Sum.elim_inr]
          rw [recoveryStep_intended_joint next later joint intended legal noMiss,
            PMF.map_comp, PMF.map_comp]
          rfl
  | _, _, .reveal published owner name fresh source _ next, point, joint, intended,
      legal, noMiss => by
      cases point with
      | inl config =>
          have move := legal owner
          simp only [ProtocolView.intendedMenu, ProtocolView.actor, observe, Sum.elim_inl]
            at move
          cases chosen : (joint owner).map (·.action) with
          | none => simp only [chosen] at move; exact (move rfl).elim
          | some action =>
              rw [chosen] at move
              have opening : action = OwnAction.reveal owner name true := move.2
              obtain ⟨value, success⟩ := (Config.Intended.reveal intended.1 fresh source).2
              simp only [recoveryStep, step, Sum.elim_inl, Finset.notMem_empty, ↓reduceIte,
                chosen, opening, OwnAction.disclosure, success, PMF.pure_map]
      | inr later =>
          simp only [recoveryStep, step, Sum.elim_inr]
          rw [recoveryStep_intended_joint next later joint intended.2 legal noMiss,
            PMF.map_comp, PMF.map_comp]
          rfl

end ProtocolState

namespace CommitRecoveryState

variable {Γ : SourceCtx Player L} {O : Finset VarId} {program : SourceProgram Player L Γ O}

theorem step_intended_point (state : CommitRecoveryState program)
    (empty : state.excluded = ∅) (intended : ProtocolState.Intended program state.point)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : ∀ who, ProtocolView.intendedMenu who program
      (ProtocolState.observe who program state.point) ((joint who).map (·.action)))
    (noMiss : ∀ who, CommitRecoveryMove.missed (joint who) = false) :
    (state.step joint).map (·.point) =
      ProtocolState.step program state.point (fun who => (joint who).map (·.action)) := by
  apply state.step_empty_point empty joint
  intro result member
  rw [empty, ProtocolState.recoveryStep_intended_joint program state.point joint
    intended legal noMiss, PMF.support_map] at member
  obtain ⟨point, _supported, rfl⟩ := member
  rfl

/-- Honest transitions retain intendedness and never advance the retry
generation, even when the current commitment block closes. -/
theorem step_intended_support (state : CommitRecoveryState program)
    (empty : state.excluded = ∅) (intended : ProtocolState.Intended program state.point)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : ∀ who, ProtocolView.intendedMenu who program
      (ProtocolState.observe who program state.point) ((joint who).map (·.action)))
    (noMiss : ∀ who, CommitRecoveryMove.missed (joint who) = false)
    (next : CommitRecoveryState program) (supported : next ∈ (state.step joint).support) :
    next.excluded = ∅ ∧ next.generation = state.generation ∧
      ProtocolState.Intended program next.point := by
  obtain ⟨result, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have rawMember : result.1 ∈
      (ProtocolState.recoveryStep program state.point state.excluded joint).support := by
    rw [← map_val_pmfToSubtype
      (ProtocolState.recoveryStep program state.point state.excluded joint)
      (fun result supported => ProtocolState.recoveryStep_excluded_monotone program state.point
        state.excluded joint result supported)]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, member, rfl⟩
  have jointLaw : ProtocolState.recoveryStep program state.point state.excluded joint =
      (ProtocolState.step program state.point (fun who => (joint who).map (·.action))).map
        (fun target => (target, ∅)) := by
    rw [empty, ProtocolState.recoveryStep_intended_joint program state.point joint
      intended legal noMiss]
  rw [jointLaw, PMF.support_map] at rawMember
  obtain ⟨target, targetMember, pair⟩ := rawMember
  have noFailure : ¬ (state.install result.1 result.2).NewFailure := by
    simp only [NewFailure, install, ← pair, Finset.empty_sdiff, Finset.not_nonempty_empty,
      not_false_eq_true]
  refine ⟨?_, close_generation_of_no_new_failure _ noFailure, ?_⟩
  · rw [close_excluded]
    exact congrArg Prod.snd pair.symm
  · rw [close_point_of_no_new_failure _ noFailure]
    change ProtocolState.Intended program result.1.1
    rw [← pair]
    exact ProtocolState.intended_step program state.point _ target intended legal targetMember

end CommitRecoveryState
end Vegas.SourceProgram
