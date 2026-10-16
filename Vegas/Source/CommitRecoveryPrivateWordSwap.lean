/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryObservedClosure
import Vegas.Source.CommitRecoveryCommitUnique

/-! # Commitment substitution preserving another owner's full source view

Typed foreign commitments are opaque throughout the original commitment
window. This statement retains the observer's complete remembered word and
allows actual omissions and accepted failed values on both paths.
-/

noncomputable section

namespace Vegas.SourceProgram.ProtocolState

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A source commitment reads an observer's own instruction and prior view;
foreign typed results cannot change that observer's complete next view. -/
theorem recoveryStep_commit_observe_congr (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (first second : ProtocolState program),
      observe who program first = observe who program second →
      atCommit program first = true →
      ∀ (excluded : Finset Player)
        (left right : Player → Option (CommitRecoveryMove Player L)), left who = right who →
      ∀ l ∈ (recoveryStep program first excluded left).support,
      ∀ r ∈ (recoveryStep program second excluded right).support,
        observe who program l.1 = observe who program r.1
  | _, _, .ret _, _, _, _, committing, _, _, _, _, _, _, _, _ => by cases committing
  | _, _, .sample _ _ _ next, first, second, same, committing,
      excluded, left, right, ownChoice, l, lm, r, rm => by
      cases first with
      | inl _ => cases committing
      | inr first =>
          cases second with
          | inl _ => cases same
          | inr second =>
              simp only [recoveryStep, Sum.elim_inr] at lm rm
              obtain ⟨lowerLeft, lowerLeftMember, leftShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next first excluded left) _).mp lm
              obtain ⟨lowerRight, lowerRightMember, rightShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next second excluded right) _).mp rm
              subst l; subst r
              exact congrArg Sum.inr (recoveryStep_commit_observe_congr who next first second
                (Sum.inr.inj same) committing excluded left right ownChoice
                lowerLeft lowerLeftMember lowerRight lowerRightMember)
  | _, _, .commit name owner fresh guard next, first, second, same, committing,
      excluded, left, right, ownChoice, l, lm, r, rm => by
      cases first with
      | inl first =>
          cases second with
          | inr _ => cases same
          | inl second =>
              have old := Sum.inl.inj same
              simp only [recoveryStep, Sum.elim_inl] at lm rm
              by_cases inactive : owner ∈ excluded
              · rw [ite_eq_left inactive, PMF.mem_support_pure_iff] at lm rm
                subst l; subst r
                exact congrArg Sum.inr (observe_entry_congr who next _ _
                  (Config.view_automaticCommit_congr who owner name _ first second old))
              · rw [ite_eq_right inactive, PMF.mem_support_pure_iff] at lm rm
                subst l; subst r
                exact congrArg Sum.inr (observe_entry_congr who next _ _
                  (Config.view_commit_congr name guard first second old _ _ (fun equal => by
                    subst owner
                    rw [ownChoice])))
      | inr first =>
          cases second with
          | inl _ => cases same
          | inr second =>
              simp only [recoveryStep, Sum.elim_inr] at lm rm
              obtain ⟨lowerLeft, lowerLeftMember, leftShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next first excluded left) _).mp lm
              obtain ⟨lowerRight, lowerRightMember, rightShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next second excluded right) _).mp rm
              subst l; subst r
              exact congrArg Sum.inr (recoveryStep_commit_observe_congr who next first second
                (Sum.inr.inj same) committing excluded left right ownChoice
                lowerLeft lowerLeftMember lowerRight lowerRightMember)
  | _, _, .reveal _ _ _ _ _ _ next, first, second, same, committing,
      excluded, left, right, ownChoice, l, lm, r, rm => by
      cases first with
      | inl _ => cases committing
      | inr first =>
          cases second with
          | inl _ => cases same
          | inr second =>
              simp only [recoveryStep, Sum.elim_inr] at lm rm
              obtain ⟨lowerLeft, lowerLeftMember, leftShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next first excluded left) _).mp lm
              obtain ⟨lowerRight, lowerRightMember, rightShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next second excluded right) _).mp rm
              subst l; subst r
              exact congrArg Sum.inr (recoveryStep_commit_observe_congr who next first second
                (Sum.inr.inj same) committing excluded left right ownChoice
                lowerLeft lowerLeftMember lowerRight lowerRightMember)

end Vegas.SourceProgram.ProtocolState
