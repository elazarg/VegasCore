/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryClear

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
end Vegas.SourceProgram
