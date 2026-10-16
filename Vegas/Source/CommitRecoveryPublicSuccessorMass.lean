/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryPublicSuccessor

/-! # Original chance atoms under a public noncommitment substitution

Equal prior observer views give the same public sample kernel. Equal next
public observations select the same sample value, preserving its exact atom.
Reveals and terminal instructions are deterministic even if guards differ.
-/

noncomputable section

namespace Vegas.SourceProgram.ProtocolState

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A noncommitment substitution preserves its actual original Nature mass;
it does not refresh or delete any public chance factor. -/
theorem recoveryStep_noncommit_mass_eq (who : Player) :
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
        recoveryStep program first excluded left l =
          recoveryStep program second excluded right r
  | _, _, .ret _, first, second, _, _, excluded, left, right, l, lm, r, rm, _ => by
      simp only [recoveryStep, PMF.mem_support_pure_iff] at lm rm
      subst l; subst r
      exact (PMF.pure_apply_self _).trans (PMF.pure_apply_self _).symm
  | Γ, _, .sample (payload := payload) name _ law next, first, second, before, notCommit,
      excluded, left, right, l, lm, r, rm, after => by
      cases first with
      | inl first =>
          cases second with
          | inr _ => cases before
          | inl second =>
              obtain ⟨lv, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp lm
              obtain ⟨rv, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp rm
              have publicCells :=
                ProtocolView.publicOnly_entry_cells who next _ _ (Sum.inr.inj after)
              have values : lv = rv := congrArg
                (fun view => view.cells name (.publicData payload) .here) publicCells
              subst rv
              have priorCells : (first.view who).1.publicOnly =
                  (second.view who).1.publicOnly := congrArg Prod.fst (Sum.inl.inj before)
              have environment : sourcePublicEnv first.state = sourcePublicEnv second.state := by
                apply sourcePublicEnv_congr
                · intro cellName cellType member
                  exact congrArg (fun view : SourceObservation L who Γ =>
                    view.cells cellName (.publicData cellType) member) priorCells
                · intro cellName cellType member
                  exact congrArg (fun view : SourceObservation L who Γ =>
                    view.cells cellName (.publication cellType) member) priorCells
              have injective (config : Config Player L Γ) : Function.Injective
                  (fun value : L.Val payload =>
                    ((Sum.inr (entry next (sampleSuccessor name config value)) :
                      Config Player L Γ ⊕ ProtocolState next), excluded)) := by
                intro a b same
                have configs := entry_injective next (Sum.inr.inj (congrArg Prod.fst same))
                exact congrArg (fun config => config.state.get .here) configs
              simp only [recoveryStep, Sum.elim_inl]
              rw [pmf_map_apply_of_injective _ (injective first),
                pmf_map_apply_of_injective _ (injective second), environment]
      | inr first =>
          cases second with
          | inl _ => cases before
          | inr second =>
              simp only [recoveryStep, Sum.elim_inr] at lm rm ⊢
              obtain ⟨lowerLeft, lowerLeftMember, leftShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next first excluded left) _).mp lm
              obtain ⟨lowerRight, lowerRightMember, rightShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next second excluded right) _).mp rm
              subst l; subst r
              have injective : Function.Injective
                  (fun result : ProtocolState next × Finset Player =>
                  ((Sum.inr result.1 : Config Player L Γ ⊕ ProtocolState next), result.2)) := by
                intro a b same
                exact Prod.ext (Sum.inr.inj (congrArg Prod.fst same))
                  (congrArg (fun result :
                    (Config Player L Γ ⊕ ProtocolState next) × Finset Player => result.2) same)
              rw [pmf_map_apply_of_injective _ injective,
                pmf_map_apply_of_injective _ injective]
              exact recoveryStep_noncommit_mass_eq who next first second (Sum.inr.inj before)
                notCommit excluded left right lowerLeft lowerLeftMember lowerRight lowerRightMember
                (Sum.inr.inj after)
  | Γ, _, .commit _ _ _ _ next, first, second, before, notCommit,
      excluded, left, right, l, lm, r, rm, after => by
      cases first with
      | inl _ => cases notCommit
      | inr first =>
          cases second with
          | inl _ => cases before
          | inr second =>
              simp only [recoveryStep, Sum.elim_inr] at lm rm ⊢
              obtain ⟨lowerLeft, lowerLeftMember, leftShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next first excluded left) _).mp lm
              obtain ⟨lowerRight, lowerRightMember, rightShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next second excluded right) _).mp rm
              subst l; subst r
              have injective : Function.Injective
                  (fun result : ProtocolState next × Finset Player =>
                  ((Sum.inr result.1 : Config Player L Γ ⊕ ProtocolState next), result.2)) := by
                intro a b same
                exact Prod.ext (Sum.inr.inj (congrArg Prod.fst same))
                  (congrArg (fun result :
                    (Config Player L Γ ⊕ ProtocolState next) × Finset Player => result.2) same)
              rw [pmf_map_apply_of_injective _ injective,
                pmf_map_apply_of_injective _ injective]
              exact recoveryStep_noncommit_mass_eq who next first second (Sum.inr.inj before)
                notCommit excluded left right lowerLeft lowerLeftMember lowerRight lowerRightMember
                (Sum.inr.inj after)
  | Γ, _, .reveal _ _ _ _ _ _ next, first, second, before, notCommit,
      excluded, left, right, l, lm, r, rm, after => by
      cases first with
      | inl first =>
          cases second with
          | inr _ => cases before
          | inl second =>
              simp only [recoveryStep, Sum.elim_inl, PMF.mem_support_pure_iff] at lm rm
              subst l; subst r
              exact (PMF.pure_apply_self _).trans (PMF.pure_apply_self _).symm
      | inr first =>
          cases second with
          | inl _ => cases before
          | inr second =>
              simp only [recoveryStep, Sum.elim_inr] at lm rm ⊢
              obtain ⟨lowerLeft, lowerLeftMember, leftShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next first excluded left) _).mp lm
              obtain ⟨lowerRight, lowerRightMember, rightShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next second excluded right) _).mp rm
              subst l; subst r
              have injective : Function.Injective
                  (fun result : ProtocolState next × Finset Player =>
                  ((Sum.inr result.1 : Config Player L Γ ⊕ ProtocolState next), result.2)) := by
                intro a b same
                exact Prod.ext (Sum.inr.inj (congrArg Prod.fst same))
                  (congrArg (fun result :
                    (Config Player L Γ ⊕ ProtocolState next) × Finset Player => result.2) same)
              rw [pmf_map_apply_of_injective _ injective,
                pmf_map_apply_of_injective _ injective]
              exact recoveryStep_noncommit_mass_eq who next first second (Sum.inr.inj before)
                notCommit excluded left right lowerLeft lowerLeftMember lowerRight lowerRightMember
                (Sum.inr.inj after)

end Vegas.SourceProgram.ProtocolState
