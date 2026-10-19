/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryVirtualHistory
import Vegas.Source.ProposalRecoveryWordLift

/-! # Actual proposal deltas of surviving virtual-repair steps -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem label_disclosure_true (choice : Option (CommitRecoveryMove Player L))
    (requested : Bool) (truthful : OwnAction.disclosure (choice.map (·.action)) = true) :
    ((choice.map (fun move => ProposalRecoveryMove.label move requested)).map
      (·.discloses)).getD false = true := by
  cases choice with
  | none => cases truthful
  | some move =>
      cases move with
      | mk action missing =>
          cases action with
          | commit => cases truthful
          | reveal owner name disclose =>
              cases disclose with
              | false => cases truthful
              | true => rfl

/-- At a given reveal prestate and joint the raw step is deterministic.
Survival therefore forces a TRUE semantic disclosure and successful stored
binding for that GIVEN joint, without any relation to a supplied target. -/
private theorem surviving_reveal_value
    {Γ : SourceCtx Player L} {O : Finset VarId} {published name : VarId} {owner : Player}
    {payload : L.Ty} (fresh : published ∉ Γ.map Prod.fst)
    (source : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ O)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name))
    (config : Config Player L Γ) (excluded : Finset Player)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (result : ProtocolState (.reveal published owner name fresh source unresolved next) ×
      Finset Player)
    (supported : result ∈ (recoveryStep
      (.reveal published owner name fresh source unresolved next) (.inl config)
        excluded joint).support) (survives : owner ∉ result.2) :
    ∃ value, config.state.get source = .success value ∧
      OwnAction.disclosure ((joint owner).map (·.action)) = true ∧ owner ∉ excluded := by
  have active : owner ∉ excluded := fun member => survives
    (recoveryStep_excluded_monotone _ _ _ _ _ supported member)
  have notFailed (failed : (revealSuccessor published source config
      (OwnAction.disclosure ((joint owner).map (·.action)))).state.get .here = .failure) :
      False := by
    have actual := supported
    simp only [recoveryStep, Sum.elim_inl, active, ↓reduceIte, failed,
      PMF.mem_support_pure_iff] at actual
    subst result
    exact survives (Finset.mem_insert_self _ _)
  have truthful : OwnAction.disclosure ((joint owner).map (·.action)) = true := by
    by_cases truthful : OwnAction.disclosure ((joint owner).map (·.action)) = true
    · exact truthful
    have withheld := Bool.eq_false_iff.mpr truthful
    exfalso
    apply notFailed
    simp only [revealSuccessor, withheld, Bool.false_eq_true, ↓reduceIte, Env.cons_get_here]
    split <;> rfl
  cases stored : config.state.get source with
  | failure =>
      exfalso
      apply notFailed
      simp only [revealSuccessor, truthful, ↓reduceIte, stored, Env.cons_get_here]
      split <;> rfl
  | success value => exact ⟨value, rfl, truthful, active⟩

/-- Copy labels along the actual paired semantic events. For foreign actors
the stored value and joint are literal; for the surviving focal actor the
deterministic reveal fact forces the unchanged successful typed value. -/
theorem recoveryProposal_virtual_eq (preserved : Finset VarId) (focal : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (original repaired : ProtocolState program), VirtualRepair preserved focal program
        original repaired → ∀ (excluded : Finset Player)
      (left right : Player → Option (CommitRecoveryMove Player L)),
      (∀ owner, owner ≠ focal → right owner = left owner) →
      ∀ (leftResult rightResult : ProtocolState program × Finset Player),
      leftResult ∈ (recoveryStep program original excluded left).support →
      rightResult ∈ (recoveryStep program repaired excluded right).support →
      focal ∉ leftResult.2 → focal ∉ rightResult.2 → ∀ labels : Player → Bool,
      recoveryProposal program original (fun owner => if owner ∈ excluded then none else
        (left owner).map (fun move => ProposalRecoveryMove.label move (labels owner))) =
      recoveryProposal program repaired (fun owner => if owner ∈ excluded then none else
        (right owner).map (fun move => ProposalRecoveryMove.label move (labels owner))) := by
  intro Γ O program
  induction program with
  | ret => intros; rfl
  | sample name fresh law next ih =>
      intro original repaired related excluded left right foreign leftResult rightResult
        leftReached rightReached leftSurvives rightSurvives labels
      cases original with
      | inl config => cases repaired <;> first | rfl | exact related.elim
      | inr original =>
          cases repaired with
          | inl config => exact related.elim
          | inr repaired =>
              simp only [recoveryStep, Sum.elim_inr] at leftReached rightReached
              obtain ⟨leftNext, leftMember, leftEq⟩ :=
                (PMF.mem_support_map_iff _ _ _).mp leftReached
              obtain ⟨rightNext, rightMember, rightEq⟩ :=
                (PMF.mem_support_map_iff _ _ _).mp rightReached
              rw [← leftEq] at leftSurvives
              rw [← rightEq] at rightSurvives
              exact congrArg (Option.map fun pair => (pair.1 + 1, pair.2))
                (ih original repaired related excluded left right foreign leftNext rightNext
                  leftMember rightMember leftSurvives rightSurvives labels)
  | commit name owner fresh guard next ih =>
      intro original repaired related excluded left right foreign leftResult rightResult
        leftReached rightReached leftSurvives rightSurvives labels
      cases original with
      | inl config => cases repaired <;> first | rfl | exact related.elim
      | inr original =>
          cases repaired with
          | inl config => exact related.elim
          | inr repaired =>
              simp only [recoveryStep, Sum.elim_inr] at leftReached rightReached
              obtain ⟨leftNext, leftMember, leftEq⟩ :=
                (PMF.mem_support_map_iff _ _ _).mp leftReached
              obtain ⟨rightNext, rightMember, rightEq⟩ :=
                (PMF.mem_support_map_iff _ _ _).mp rightReached
              rw [← leftEq] at leftSurvives
              rw [← rightEq] at rightSurvives
              exact congrArg (Option.map fun pair => (pair.1 + 1, pair.2))
                (ih original repaired related excluded left right foreign leftNext rightNext
                  leftMember rightMember leftSurvives rightSurvives labels)
  | reveal published owner name fresh source unresolved next ih =>
      intro original repaired related excluded left right foreign leftResult rightResult
        leftReached rightReached leftSurvives rightSurvives labels
      cases original with
      | inl original =>
          cases repaired with
          | inr point => exact related.elim
          | inl repaired =>
              by_cases outside : owner ≠ focal
              · have binding : repaired.state.get source = original.state.get source := by
                  rw [related.bindings]
                  split
                  · rfl
                  · simp only [repairBinding, outside, ↓reduceIte]
                simp only [recoveryProposal, Sum.elim_inl, foreign owner outside, binding]
              · have own : owner = focal := not_ne_iff.mp outside
                subst owner
                obtain ⟨value, stored, truthful, active⟩ := surviving_reveal_value
                  fresh source unresolved next original excluded left leftResult leftReached
                    leftSurvives
                obtain ⟨_other, _otherStored, otherTruthful, _otherActive⟩ := surviving_reveal_value
                  fresh source unresolved next repaired excluded right rightResult rightReached
                    rightSurvives
                have binding : repaired.state.get source = .success value := by
                  rw [related.bindings]
                  split
                  · exact stored
                  · simp only [stored, repairBinding, ↓reduceIte]
                have leftDisclosure := label_disclosure_true (left focal) (labels focal) truthful
                have rightDisclosure := label_disclosure_true (right focal) (labels focal)
                  otherTruthful
                simp only [recoveryProposal, Sum.elim_inl, active, ↓reduceIte,
                  leftDisclosure, rightDisclosure, stored, binding]
      | inr original =>
          cases repaired with
          | inl config => exact related.elim
          | inr repaired =>
              simp only [recoveryStep, Sum.elim_inr] at leftReached rightReached
              obtain ⟨leftNext, leftMember, leftEq⟩ :=
                (PMF.mem_support_map_iff _ _ _).mp leftReached
              obtain ⟨rightNext, rightMember, rightEq⟩ :=
                (PMF.mem_support_map_iff _ _ _).mp rightReached
              rw [← leftEq] at leftSurvives
              rw [← rightEq] at rightSurvives
              exact congrArg (Option.map fun pair => (pair.1 + 1, pair.2))
                (ih original repaired related excluded left right foreign leftNext rightNext
                  leftMember rightMember leftSurvives rightSurvives labels)

end ProtocolState
end Vegas.SourceProgram
