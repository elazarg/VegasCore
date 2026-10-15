/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.FailedBindingDeviation

/-! # Intended source points have no persistent departure debt -/

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace Config

variable {Γ : SourceCtx Player L} {O : Finset VarId} {config : Config Player L Γ}

omit [IExpr.ResultTypes L] in
theorem Intended.not_indebted (intended : config.Intended O) (who : Player) :
    ¬ config.Indebted who O := by
  intro owed
  obtain ⟨obligation, member, _, _, value, bound, rejected⟩ := owed.pending
  have accepted := intended.predicted obligation member value bound
  rw [accepted] at rejected
  cases rejected

omit [IExpr.ResultTypes L] in
theorem Intended.not_failedBinding (intended : config.Intended O) (who : Player) :
    ¬ config.FailedBinding who O := by
  intro owed
  obtain ⟨_, _, source, _, failed⟩ := owed.pending
  obtain ⟨value, successful⟩ := intended.bound source
  rw [successful] at failed
  cases failed

end Config

namespace ProtocolState

/-- The semantic intended invariant rules out both rejected-value debt and
irrevocable failed-binding debt, including failures at past reveal positions. -/
theorem Intended.not_owesFailure (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (point : ProtocolState program) →
    Intended program point → ¬ OwesFailure who program point
  | _, _, .ret _, _, intended => fun owed =>
      owed.elim (intended.not_indebted who) (intended.not_failedBinding who)
  | _, _, .sample _ _ _ next, point, intended => by
      cases point with
      | inl _ => exact fun owed =>
          owed.elim (intended.1.not_indebted who) (intended.1.not_failedBinding who)
      | inr later => exact Intended.not_owesFailure who next later intended
  | _, _, .commit _ _ _ _ next, point, intended => by
      cases point with
      | inl _ => exact fun owed =>
          owed.elim (intended.1.not_indebted who) (intended.1.not_failedBinding who)
      | inr later => exact Intended.not_owesFailure who next later intended
  | _, _, .reveal _ _ _ _ _ _ next, point, intended => by
      cases point with
      | inl _ => exact fun owed =>
          owed.elim (intended.1.not_indebted who) (intended.1.not_failedBinding who)
      | inr later =>
          intro owed
          rcases owed with (failed | owed) | (failed | owed)
          · obtain ⟨value, successful⟩ := intended.1
            rw [successful] at failed
            cases failed.2
          · exact Intended.not_owesFailure who next later intended.2 (Or.inl owed)
          · obtain ⟨value, successful⟩ := intended.1
            rw [successful] at failed
            cases failed.2
          · exact Intended.not_owesFailure who next later intended.2 (Or.inr owed)

end ProtocolState
end Vegas.SourceProgram
