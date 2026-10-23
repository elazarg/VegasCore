/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ValueBinding
import Vegas.Source.Purification
import Vegas.Source.FiniteSupport
import Vegas.Source.ProtocolBehavioralPolicy

/-! # Value-only binding from an arbitrary source continuation

The replacement of an unusable binding by a value plus later withholding works
from a residual configuration, with its existing registry, revelations and own
action histories intact. One mixture serves every configuration in an arbitrary
finite belief, preserving correlations with any parameter of that configuration.

These are conditional source deviation laws. They do not identify native
opponents' observations, construct consistent native beliefs, or prove a native
sequential-equilibrium extension.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L} {O : Finset VarId} {who : Player}

omit [IExpr.ResultTypes L] in
theorem Patched.refl (state : State L Γ) (history : History Player L) :
    Patched (who := who) id (fun _ _ => false) state state history history where
  publicEq := fun _ => rfl
  inputEq := fun _ => rfl
  publicationEq := fun _ => rfl
  foreignEq := fun _ _ => rfl
  replacedEq := fun _ impossible => by contradiction
  keptEq := fun _ _ => rfl
  historyEq := fun _ _ => rfl
  unpatchEq := rfl

/-- The repaired continuation is legal under every commitment interface. -/
theorem ValueBinding.admitted :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (policy : BehavioralPolicy who program) → ValueBinding program policy →
    (admission : CommitmentInterface program) → policy.Admitted program admission
  | _, _, .ret _, _, _, _ => trivial
  | _, _, .sample _ _ _ next, policy, valid, admission =>
      valid.admitted next policy admission
  | _, _, .commit _ _ _ _ next, policy, valid, admission => by
      refine ⟨?_, valid.2.admitted next policy.2 (fun site => admission (some site))⟩
      intro owned view choice supported
      cases choice with
      | failure => exact (valid.1 owned view supported).elim
      | success value => trivial
  | _, _, .reveal _ _ _ _ _ _ next, policy, valid, admission =>
      valid.admitted next policy.2 admission

end Vegas.SourceProgram
