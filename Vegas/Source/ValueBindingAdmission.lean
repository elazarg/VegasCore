/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ValueBinding
import Vegas.Source.ProtocolBehavioralPolicy

/-! # The value interface admits exactly the value-binding policies

A behavioral policy is admitted by the value interface
(`Vegas.SourceProgram.CommitmentInterface.values`) exactly when it never
chooses a failed binding, which is the value-binding condition
(`Vegas.SourceProgram.ValueBinding`). The policies of the source protocol model
under the value interface are therefore the value-binding policies.
-/

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The value interface admits exactly the value-binding policies. -/
theorem BehavioralPolicy.admitted_values_iff_valueBinding {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (policy : BehavioralPolicy who program) →
    (policy.Admitted program (CommitmentInterface.values program) ↔ ValueBinding program policy)
  | _, _, .ret _, _ => Iff.rfl
  | _, _, .sample _ _ _ next, policy => admitted_values_iff_valueBinding next policy
  | _, _, .commit _ _ _ _ next, policy => by
      refine and_congr ?_ (admitted_values_iff_valueBinding next policy.2)
      constructor
      · intro admits own view failed
        have admitted := admits own view _ failed
        simp only [CommitmentInterface.values, CommitmentAdmission.admits_failure,
          reduceCtorEq] at admitted
      · intro binding own view choice member
        cases choice with
        | success value => trivial
        | failure => exact absurd member (binding own view)
  | _, _, .reveal _ _ _ _ _ _ next, policy => admitted_values_iff_valueBinding next policy.2

/-- Successful value bindings are admitted by every commitment interface. -/
theorem BehavioralPolicy.admitted_of_valueBinding {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (policy : BehavioralPolicy who program) →
    ValueBinding program policy → (admission : CommitmentInterface program) →
    policy.Admitted program admission
  | _, _, .ret _, _, _, _ => trivial
  | _, _, .sample _ _ _ next, policy, binding, admission =>
      admitted_of_valueBinding next policy binding admission
  | _, _, .commit _ _ _ _ next, policy, binding, admission => by
      refine ⟨?_, admitted_of_valueBinding next policy.2 binding.2
        (fun site => admission (some site))⟩
      intro own view choice member
      cases choice with
      | success value => exact CommitmentAdmission.admits_success _ value
      | failure => exact absurd member (binding.1 own view)
  | _, _, .reveal _ _ _ _ _ _ next, policy, binding, admission =>
      admitted_of_valueBinding next policy.2 binding admission

/-- The policies admitted by the value interface are the value-binding
policies. -/
def valueBindingAdmittedEquiv {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (who : Player) :
    {policy : BehavioralPolicy who program //
      policy.Admitted program (CommitmentInterface.values program)} ≃
      ValueBindingPolicy who program :=
  Equiv.subtypeEquivRight fun policy =>
    BehavioralPolicy.admitted_values_iff_valueBinding program policy

end Vegas.SourceProgram
