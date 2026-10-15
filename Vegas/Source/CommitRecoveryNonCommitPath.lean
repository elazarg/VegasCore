/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryProtocol
import GameTheory.Protocol.Backward

/-! # Legal recovery paths through sample and reveal phases -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Math.Probability
open ProtocolState CommitRecoveryState

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Noncommitment kernels depend only on the correctly addressed disclosure
bit, or are chance-only. Their raw joint action can therefore be replaced by
a legal one, with no change to the transition law or retained history. -/
theorem ProtocolState.recoveryStep_legalize_nonCommit :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (excluded : Finset Player) (joint : Player → Option (CommitRecoveryMove Player L)),
    atCommit program point = false →
    ∃ legalJoint,
      IsLegalJoint (CommitRecoveryState.atPoint point excluded 0).Active
        (CommitRecoveryState.atPoint point excluded 0).available legalJoint ∧
      recoveryStep program point excluded legalJoint =
        recoveryStep program point excluded joint := by
  intro Γ O program
  induction program with
  | ret payoff =>
      intro point excluded joint _notCommit
      refine ⟨fun _ => none, ?_, rfl⟩
      intro who
      change ¬ (none = some who ∧ who ∉ excluded)
      simp only [reduceCtorEq, false_and, not_false_eq_true]
  | sample name fresh law next ih =>
      intro point excluded joint notCommit
      cases point with
      | inl entry =>
          refine ⟨fun _ => none, ?_, rfl⟩
          intro who
          change ¬ (none = some who ∧ who ∉ excluded)
          simp only [reduceCtorEq, false_and, not_false_eq_true]
      | inr later =>
          obtain ⟨legalJoint, legal, same⟩ := ih later excluded joint notCommit
          refine ⟨legalJoint, legal, ?_⟩
          simp only [recoveryStep, Sum.elim_inr, same]
  | commit name owner fresh guard next ih =>
      intro point excluded joint notCommit
      cases point with
      | inl entry => cases notCommit
      | inr later =>
          obtain ⟨legalJoint, legal, same⟩ := ih later excluded joint notCommit
          refine ⟨legalJoint, legal, ?_⟩
          simp only [recoveryStep, Sum.elim_inr, same]
  | reveal published owner name fresh source unresolved next ih =>
      intro point excluded joint notCommit
      cases point with
      | inl entry =>
          let disclose := OwnAction.disclosure ((joint owner).map (·.action))
          by_cases inactive : owner ∈ excluded
          · refine ⟨fun _ => none, ?_, ?_⟩
            · intro who
              change ¬ (some owner = some who ∧ who ∉ excluded)
              rintro ⟨acting, active⟩
              exact active (Option.some.inj acting ▸ inactive)
            · simp only [recoveryStep, Sum.elim_inl, inactive, ↓reduceIte]
          · refine ⟨Function.update (fun _ => none) owner
              (some ⟨.reveal owner name disclose, false⟩), ?_, ?_⟩
            · intro who
              by_cases same : who = owner
              · subst who
                rw [Function.update_self]
                refine ⟨⟨rfl, inactive⟩, ?_⟩
                change (∃ bit, OwnAction.reveal owner name disclose = .reveal owner name bit) ∧
                  false = false
                exact ⟨⟨disclose, rfl⟩, rfl⟩
              · rw [Function.update_of_ne same]
                change ¬ (some owner = some who ∧ who ∉ excluded)
                exact fun active => same (Option.some.inj active.1).symm
            · simp only [recoveryStep, Sum.elim_inl, inactive, ↓reduceIte,
                Function.update_self, Option.map_some, OwnAction.disclosure]
              rfl
      | inr later =>
          obtain ⟨legalJoint, legal, same⟩ := ih later excluded joint notCommit
          refine ⟨legalJoint, legal, ?_⟩
          simp only [recoveryStep, Sum.elim_inr, same]

/-- An actual noncommitment instruction checkpoints its result directly.
No commitment retry can occur while the saved instruction is a sample or reveal. -/
theorem CommitRecoveryState.nonCommit_successor
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (initial : Config Player L Γ)
    (point : ProtocolState program) (excluded : Finset Player) (generation : Nat)
    (notCommit : ProtocolState.atCommit program point = false)
    (running : ¬ ProtocolState.terminal program point)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (target : ProtocolState program × Finset Player)
    (supported : target ∈ (ProtocolState.recoveryStep program point excluded joint).support) :
    (commitRecoveryProtocol program initial).Successor
      (atPoint target.1 target.2 generation) (atPoint point excluded generation) := by
  obtain ⟨legalJoint, legal, same⟩ :=
    ProtocolState.recoveryStep_legalize_nonCommit program point excluded joint notCommit
  let state := atPoint point excluded generation
  have member : target ∈
      (ProtocolState.recoveryStep program state.point state.excluded legalJoint).support := by
    change target ∈ (ProtocolState.recoveryStep program point excluded legalJoint).support
    rw [same]
    exact supported
  have mapped : target ∈ ((pmfToSubtype
      (ProtocolState.recoveryStep program state.point state.excluded legalJoint)
      (fun result support => ProtocolState.recoveryStep_excluded_monotone program state.point
        state.excluded legalJoint result support)).map Subtype.val).support := by
    rw [map_val_pmfToSubtype]
    exact member
  obtain ⟨packed, packedSupport, packedEq⟩ := (PMF.mem_support_map_iff _ _ _).mp mapped
  refine ⟨legalJoint, ⟨running, legal⟩, ?_⟩
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨packed, packedSupport, ?_⟩
  change (state.install packed.val packed.property).close = atPoint target.1 target.2 generation
  have savedEq : state.saved = point := rfl
  have absent : ¬ (state.install packed.val packed.property).Finished := by
    intro completed
    have commits := completed.1
    change ProtocolState.atCommit program point = true at commits
    rw [notCommit] at commits
    cases commits
  unfold close
  rw [ite_eq_right absent]
  change (if ProtocolState.atCommit program state.saved then _ else
    atPoint packed.val.1 packed.val.2 state.generation) = _
  rw [savedEq, notCommit]
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases packedEq
  rfl

/-- A sequence of noncommitment instructions lifts to realized legal source
recovery transitions, with the same permanent exclusions and generation. -/
theorem CommitRecoveryState.reaches_of_nonCommit_path
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (initial : Config Player L Γ)
    (generation : Nat) (first last : ProtocolState program × Finset Player)
    (path : Relation.ReflTransGen
      (fun earlier later : ProtocolState program × Finset Player =>
        ¬ ProtocolState.terminal program earlier.1 ∧
        ProtocolState.atCommit program earlier.1 = false ∧
        ∃ joint, later ∈ (ProtocolState.recoveryStep program earlier.1 earlier.2 joint).support)
      first last) :
    (commitRecoveryProtocol program initial).Reaches
      (atPoint first.1 first.2 generation) (atPoint last.1 last.2 generation) := by
  apply Relation.ReflTransGen.lift
    (fun state : ProtocolState program × Finset Player => atPoint state.1 state.2 generation)
    (fun earlier later step => ?_) first last path
  obtain ⟨running, notCommit, joint, supported⟩ := step
  exact nonCommit_successor program initial earlier.1 earlier.2 generation notCommit running
    joint later supported

end Vegas.SourceProgram
