/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryPreparationRepair
import Vegas.Source.ProposalRecoveryWordLift

/-! # Literal source labels and proposal contents under selective repair -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

/-- Removing labels commutes with the actual selective transformation. -/
theorem repairPreparationJoint_semantic (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program)
      (joint : Player → Option (ProposalRecoveryMove Player L)),
      Setup.proposalRecoveryJoint (repairPreparationJoint who program point joint) =
        repairPreparationRawJoint who program point (Setup.proposalRecoveryJoint joint) := by
  intro Γ O program
  induction program with
  | ret => intros; rfl
  | sample _ _ _ next ih =>
      intro point joint
      cases point with
      | inl => rfl
      | inr point => exact ih point joint
  | @commit Γ O name owner payload fresh guard next ih =>
      intro point joint
      cases point with
      | inr point => exact ih point joint
      | inl config =>
          funext observer
          simp only [repairPreparationJoint, repairPreparationRawJoint, Sum.elim_inl]
          split
          · by_cases acts : observer = owner
            · subst observer
              simp only [Setup.proposalRecoveryJoint, Function.update_self]
              cases chosen : joint owner with
              | none => rfl
              | some move =>
                  cases marker : move.semantic.missing <;>
                    cases binding : OwnAction.binding owner name payload (some
                      move.semantic.action) <;>
                      simp [marker, binding]
            · simp only [Setup.proposalRecoveryJoint, Function.update_of_ne acts]
          · rfl
  | reveal published owner name fresh source unresolved next ih =>
      intro point joint
      cases point with
      | inr point => exact ih point joint
      | inl config =>
          funext observer
          simp only [repairPreparationJoint, repairPreparationRawJoint, Sum.elim_inl]
          split
          · cases bound : config.state.get source with
            | failure =>
                by_cases acts : observer = owner
                · subst observer
                  simp only [Setup.proposalRecoveryJoint, Function.update_self]
                  cases joint owner <;> rfl
                · simp only [Setup.proposalRecoveryJoint, Function.update_of_ne acts]
            | success => rfl
          · rfl

/-- The new moves are legal labels, rather than supplied plaintext values. -/
theorem repairPreparationJoint_valid (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program)
      (joint : Player → Option (ProposalRecoveryMove Player L)),
      (∀ owner move, joint owner = some move → move.Valid) →
      ∀ owner move, repairPreparationJoint who program point joint owner = some move →
        move.Valid := by
  intro Γ O program
  induction program with
  | ret =>
      intro point joint valid observer move chosen
      exact valid observer move chosen
  | sample _ _ _ next ih =>
      intro point joint valid observer move chosen
      cases point with
      | inl => exact valid observer move chosen
      | inr point => exact ih point joint valid observer move chosen
  | commit name owner fresh guard next ih =>
      intro point joint valid observer move chosen
      cases point with
      | inr point => exact ih point joint valid observer move chosen
      | inl config =>
          simp only [repairPreparationJoint, Sum.elim_inl] at chosen
          split at chosen
          · by_cases acts : observer = owner
            · subst observer
              rw [Function.update_self] at chosen
              obtain ⟨original, present, selected⟩ := (Option.map_eq_some_iff).mp chosen
              split at selected
              · exact selected ▸ valid owner original present
              · split at selected
                · subst move
                  exact fun impossible => Bool.noConfusion impossible
                · exact selected ▸ valid owner original present
            · rw [Function.update_of_ne acts] at chosen
              exact valid observer move chosen
          · exact valid observer move chosen
  | reveal published owner name fresh source unresolved next ih =>
      intro point joint valid observer move chosen
      cases point with
      | inr point => exact ih point joint valid observer move chosen
      | inl config =>
          simp only [repairPreparationJoint, Sum.elim_inl] at chosen
          split at chosen
          · split at chosen
            · by_cases acts : observer = owner
              · subst observer
                rw [Function.update_self] at chosen
                obtain ⟨original, present, selected⟩ := (Option.map_eq_some_iff).mp chosen
                subst move
                exact fun impossible => Bool.noConfusion impossible
              · rw [Function.update_of_ne acts] at chosen
                exact valid observer move chosen
            · exact valid observer move chosen
          · exact valid observer move chosen

end ProtocolState

namespace Config

omit [IExpr.ResultTypes L] in
/-- Stored successes are unchanged by a selective repair. -/
theorem FocalRepair.binding_success {who owner : Player} {Γ : SourceCtx Player L}
    {name : VarId} {payload : L.Ty} {original repaired : Config Player L Γ}
    (related : Config.FocalRepair who original repaired)
    (cell : HasVar Γ name (.commitment owner payload)) (value : L.Val payload)
    (success : original.state.get cell = .success value) :
    repaired.state.get cell = .success value := by
  obtain ⟨_, patched, invariant, _, _⟩ := related
  by_cases own : owner = who
  · subst owner
    cases marked : patched cell (sourceObserve who repaired.state, repaired.history who) with
    | false => exact (invariant.keptEq cell marked).trans success
    | true =>
        have failure := (invariant.replacedEq cell marked).1
        rw [success] at failure
        cases failure
  · exact (invariant.foreignEq cell own).trans success

end Config

namespace ProtocolState

/-- Each actual proposal delta, including a failed-disclosure value, is
preserved. A patched failed stored binding never invents a proposal. -/
theorem FocalRepair.recoveryProposal_preparation (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (original repaired : ProtocolState program),
      FocalRepair who program original repaired →
      ∀ joint : Player → Option (ProposalRecoveryMove Player L),
      recoveryProposal program repaired (repairPreparationJoint who program original joint) =
        recoveryProposal program original joint := by
  intro Γ O program
  induction program with
  | ret => intros; rfl
  | sample _ _ _ next ih =>
      intro original repaired related joint
      cases original <;> cases repaired
      · rfl
      · exact related.elim
      · exact related.elim
      · exact congrArg (Option.map fun pair => (pair.1 + 1, pair.2)) (ih _ _ related joint)
  | commit name owner fresh guard next ih =>
      intro original repaired related joint
      cases original <;> cases repaired
      · rfl
      · exact related.elim
      · exact related.elim
      · exact congrArg (Option.map fun pair => (pair.1 + 1, pair.2)) (ih _ _ related joint)
  | reveal published owner name fresh source unresolved next ih =>
      intro original repaired related joint
      cases original with
      | inr original =>
          cases repaired with
          | inl => exact related.elim
          | inr repaired =>
              exact congrArg (Option.map fun pair => (pair.1 + 1, pair.2))
                (ih _ _ related joint)
      | inl original =>
          cases repaired with
          | inr => exact related.elim
          | inl repaired =>
              change Config.FocalRepair who original repaired at related
              by_cases own : owner = who
              · subst who
                cases bound : original.state.get source with
                | failure =>
                    simp only [recoveryProposal, repairPreparationJoint, Sum.elim_inl,
                      ↓reduceIte, bound, Function.update_self]
                    cases joint owner <;> simp [ProposalRecoveryMove.discloses,
                      OwnAction.disclosure]
                | success value =>
                    have same := Config.FocalRepair.binding_success related source value bound
                    simp only [recoveryProposal, repairPreparationJoint, Sum.elim_inl,
                      ↓reduceIte, bound, same]
              · obtain ⟨_, _, invariant, _, _⟩ := related
                simp only [recoveryProposal, repairPreparationJoint, Sum.elim_inl, own, ↓reduceIte,
                  invariant.foreignEq source own]

end ProtocolState
end Vegas.SourceProgram
