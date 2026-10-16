/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryPublicSuccessor

/-! # Exclusion control from actual noncommitment public results

Samples keep the exclusion set. A reveal adds exactly its owner when the
public publication failed. Hidden private fields and action recall need
not agree to reconstruct that update from the original public result.
-/

noncomputable section

namespace Vegas.SourceProgram.ProtocolState

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Equal prior and next public observations determine the same noncommitment
exclusion update without requiring equality of private source views. -/
theorem recoveryStep_noncommit_public_excluded_eq (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (first second : ProtocolState program),
      ProtocolView.publicOnly who program (observe who program first) =
        ProtocolView.publicOnly who program (observe who program second) →
      atCommit program first = false →
      ∀ (excluded : Finset Player)
        (left right : Player → Option (CommitRecoveryMove Player L)),
      ∀ l ∈ (recoveryStep program first excluded left).support,
      ∀ r ∈ (recoveryStep program second excluded right).support,
        ProtocolView.publicOnly who program (observe who program l.1) =
          ProtocolView.publicOnly who program (observe who program r.1) →
        l.2 = r.2
  | _, _, .ret _, _, _, _, _, _, _, _, l, lm, r, rm, _ => by
      simp only [recoveryStep, PMF.mem_support_pure_iff] at lm rm
      subst l; subst r
      rfl
  | _, _, .sample _ _ _ next, first, second, before, notCommit,
      excluded, left, right, l, lm, r, rm, after => by
      cases first with
      | inl _ =>
          cases second with
          | inr _ => cases before
          | inl _ =>
              obtain ⟨_, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp lm
              obtain ⟨_, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp rm
              rfl
      | inr first =>
          cases second with
          | inl _ => cases before
          | inr second =>
              simp only [recoveryStep, Sum.elim_inr] at lm rm
              obtain ⟨lowerLeft, lowerLeftMember, leftShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next first excluded left) _).mp lm
              obtain ⟨lowerRight, lowerRightMember, rightShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next second excluded right) _).mp rm
              subst l; subst r
              exact recoveryStep_noncommit_public_excluded_eq who next first second
                (Sum.inr.inj before) notCommit excluded left right
                lowerLeft lowerLeftMember lowerRight lowerRightMember (Sum.inr.inj after)
  | _, _, .commit _ _ _ _ next, first, second, before, notCommit,
      excluded, left, right, l, lm, r, rm, after => by
      cases first with
      | inl _ => cases notCommit
      | inr first =>
          cases second with
          | inl _ => cases before
          | inr second =>
              simp only [recoveryStep, Sum.elim_inr] at lm rm
              obtain ⟨lowerLeft, lowerLeftMember, leftShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next first excluded left) _).mp lm
              obtain ⟨lowerRight, lowerRightMember, rightShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next second excluded right) _).mp rm
              subst l; subst r
              exact recoveryStep_noncommit_public_excluded_eq who next first second
                (Sum.inr.inj before) notCommit excluded left right
                lowerLeft lowerLeftMember lowerRight lowerRightMember (Sum.inr.inj after)
  | _, _, .reveal (payload := payload) published owner _ _ selected _ next,
      first, second, before, notCommit, excluded, left, right, l, lm, r, rm, after => by
      cases first with
      | inl first =>
          cases second with
          | inr _ => cases before
          | inl second =>
              simp only [recoveryStep, Sum.elim_inl, PMF.mem_support_pure_iff] at lm rm
              subst l; subst r
              dsimp only
              by_cases inactive : owner ∈ excluded
              · split <;> split <;> simp only [Finset.insert_eq_of_mem inactive]
              · have publicCells :=
                  ProtocolView.publicOnly_entry_cells who next _ _ (Sum.inr.inj after)
                simp only [ite_eq_right inactive] at publicCells ⊢
                have result := congrArg
                  (fun view => view.cells published (.publication payload) .here) publicCells
                change (revealSuccessor published selected first
                    (OwnAction.disclosure ((left owner).map (·.action)))).state.get .here =
                  (revealSuccessor published selected second
                    (OwnAction.disclosure ((right owner).map (·.action)))).state.get .here at result
                rw [result]
      | inr first =>
          cases second with
          | inl _ => cases before
          | inr second =>
              simp only [recoveryStep, Sum.elim_inr] at lm rm
              obtain ⟨lowerLeft, lowerLeftMember, leftShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next first excluded left) _).mp lm
              obtain ⟨lowerRight, lowerRightMember, rightShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next second excluded right) _).mp rm
              subst l; subst r
              exact recoveryStep_noncommit_public_excluded_eq who next first second
                (Sum.inr.inj before) notCommit excluded left right
                lowerLeft lowerLeftMember lowerRight lowerRightMember (Sum.inr.inj after)

end Vegas.SourceProgram.ProtocolState
