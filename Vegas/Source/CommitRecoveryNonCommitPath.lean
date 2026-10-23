/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryInstructions
import Mathlib.Data.List.Chain
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
        recoveryStep program point excluded joint ∧
      ∀ who, actor program point = some who → who ∉ excluded →
        OwnAction.disclosure ((legalJoint who).map (·.action)) =
          OwnAction.disclosure ((joint who).map (·.action)) := by
  intro Γ O program
  induction program with
  | ret payoff =>
      intro point excluded joint _notCommit
      refine ⟨fun _ => none, ?_, rfl, ?_⟩
      · intro who
        change ¬ (none = some who ∧ who ∉ excluded)
        simp only [reduceCtorEq, false_and, not_false_eq_true]
      · intro who acting
        cases acting
  | sample name fresh law next ih =>
      intro point excluded joint notCommit
      cases point with
      | inl entry =>
          refine ⟨fun _ => none, ?_, rfl, ?_⟩
          · intro who
            change ¬ (none = some who ∧ who ∉ excluded)
            simp only [reduceCtorEq, false_and, not_false_eq_true]
          · intro who acting
            cases acting
      | inr later =>
          obtain ⟨legalJoint, legal, same, disclosure⟩ := ih later excluded joint notCommit
          refine ⟨legalJoint, legal, ?_, disclosure⟩
          simp only [recoveryStep, Sum.elim_inr, same]
  | commit name owner fresh guard next ih =>
      intro point excluded joint notCommit
      cases point with
      | inl entry => cases notCommit
      | inr later =>
          obtain ⟨legalJoint, legal, same, disclosure⟩ := ih later excluded joint notCommit
          refine ⟨legalJoint, legal, ?_, disclosure⟩
          simp only [recoveryStep, Sum.elim_inr, same]
  | reveal published owner name fresh source unresolved next ih =>
      intro point excluded joint notCommit
      cases point with
      | inl entry =>
          let disclose := OwnAction.disclosure ((joint owner).map (·.action))
          by_cases inactive : owner ∈ excluded
          · refine ⟨fun _ => none, ?_, ?_, ?_⟩
            · intro who
              change ¬ (some owner = some who ∧ who ∉ excluded)
              rintro ⟨acting, active⟩
              exact active (Option.some.inj acting ▸ inactive)
            · simp only [recoveryStep, Sum.elim_inl, inactive, ↓reduceIte]
            · intro who acting survives
              have same : owner = who := Option.some.inj acting
              exact (survives (same ▸ inactive)).elim
          · refine ⟨Function.update (fun _ => none) owner
              (some ⟨.reveal owner name disclose, false⟩), ?_, ?_, ?_⟩
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
            · intro who acting _survives
              have same : owner = who := Option.some.inj acting
              subst who
              simp only [Function.update_self, Option.map_some, OwnAction.disclosure]
              rfl
      | inr later =>
          obtain ⟨legalJoint, legal, same, disclosure⟩ := ih later excluded joint notCommit
          refine ⟨legalJoint, legal, ?_, disclosure⟩
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
    ∃ legalJoint, ∃ legal : (commitRecoveryProtocol program initial).Legal
        (atPoint point excluded generation) legalJoint,
      (atPoint target.1 target.2 generation) ∈
        ((commitRecoveryProtocol program initial).step _ ⟨legalJoint, legal⟩).support ∧
      ∀ who, ProtocolState.actor program point = some who → who ∉ excluded →
        OwnAction.disclosure ((legalJoint who).map (·.action)) =
          OwnAction.disclosure ((joint who).map (·.action)) := by
  obtain ⟨legalJoint, legal, same, disclosure⟩ :=
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
  refine ⟨legalJoint, ⟨running, legal⟩, ?_, disclosure⟩
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

/-- The existing noncommitment path retains its actual intermediate points,
legal instructions and post-step addresses. An annotation on each original
step is retained in the same chronological chain. -/
theorem CommitRecoveryState.instructions_of_nonCommit_path
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (initial : Config Player L Γ)
    (generation : Nat) {relation : (ProtocolState program × Finset Player) →
      (ProtocolState program × Finset Player) → Prop}
    (steps : ∀ first last, relation first last →
      ¬ ProtocolState.terminal program first.1 ∧
      ProtocolState.atCommit program first.1 = false ∧
      ∃ joint, last ∈ (ProtocolState.recoveryStep program first.1 first.2 joint).support)
    (first last : ProtocolState program × Finset Player)
    (path : Relation.ReflTransGen relation first last) :
    ∃ (states : List (ProtocolState program × Finset Player))
      (joints : List (Player → Option (CommitRecoveryMove Player L))),
      (first :: states).IsChain relation ∧
      (first :: states).getLast (List.cons_ne_nil _ _) = last ∧
      InstructionPath program initial joints
        (states.map fun point => (atPoint point.1 point.2 generation).publicAddress)
        (atPoint first.1 first.2 generation) (atPoint last.1 last.2 generation) := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], [], .singleton _, rfl, .refl _⟩
  | @head first middle moved _remaining ih =>
      obtain ⟨states, joints, chain, ending, instructions⟩ := ih
      obtain ⟨running, notCommit, joint, supported⟩ := steps first middle moved
      obtain ⟨legalJoint, legal, realized, _disclosure⟩ :=
        nonCommit_successor program initial first.1 first.2
        generation notCommit running joint middle supported
      exact ⟨middle :: states, legalJoint :: joints, .cons_cons moved chain,
        by simpa only [List.getLast_cons_cons] using ending,
        .step legal realized instructions⟩

end Vegas.SourceProgram
