module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Source.Disclosure

@[expose] public section

/-! # Source binding submission

Submission excludes public omission at an active commitment while allowing an
accepted unusable binding. Repairing omissions preserves all reveal decisions
and every already-submitting policy.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Every active binding callback submits an accepted binding, possibly unusable. -/
def SubmitsBindings {who : Player} : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → BehavioralPolicy who program → Prop
  | _, _, .ret _, _ => True
  | _, _, .sample _ _ _ next, policy => SubmitsBindings next policy
  | _, _, .commit _ owner _ _ next, policy =>
      (∀ (own : owner = who) view active, none ∉ (policy.1 own view active).support) ∧
        SubmitsBindings next policy.2
  | _, _, .reveal _ _ _ _ _ _ next, policy => SubmitsBindings next policy.2

/-- Replace an active binding omission by an accepted unusable binding. -/
def BehavioralPolicy.submitBindings {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    BehavioralPolicy who program → BehavioralPolicy who program
  | _, _, .ret _, _ => PUnit.unit
  | _, _, .sample _ _ _ next, policy => submitBindings next policy
  | _, _, .commit _ _ _ _ next, policy =>
      (fun own view active => (policy.1 own view active).map
        (fun choice => some (choice.getD .failure)), submitBindings next policy.2)
  | _, _, .reveal _ _ _ _ _ _ next, policy => (policy.1, submitBindings next policy.2)

theorem submitsBindings_submitBindings {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (policy : BehavioralPolicy who program) → SubmitsBindings program (policy.submitBindings
      program)
  | _, _, .ret _, _ => trivial
  | _, _, .sample _ _ _ next, policy => submitsBindings_submitBindings next policy
  | _, _, .commit _ _ _ _ next, policy => by
      refine ⟨?_, submitsBindings_submitBindings next policy.2⟩
      intro own view active omitted
      obtain ⟨choice, _, impossible⟩ := (PMF.mem_support_map_iff _ _ _).mp omitted
      cases impossible
  | _, _, .reveal _ _ _ _ _ _ next, policy => submitsBindings_submitBindings next policy.2

theorem Disclosing.submitBindings {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (policy : BehavioralPolicy who program) → Disclosing program policy →
      Disclosing program (policy.submitBindings program)
  | _, _, .ret _, _, _ => trivial
  | _, _, .sample _ _ _ next, policy, opens => submitBindings next policy opens
  | _, _, .commit _ _ _ _ next, policy, opens => submitBindings next policy.2 opens
  | _, _, .reveal _ _ _ _ _ _ next, policy, opens =>
      ⟨opens.1, submitBindings next policy.2 opens.2⟩

theorem BehavioralPolicy.submitBindings_eq_self {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (policy : BehavioralPolicy who program) → SubmitsBindings program policy →
      policy.submitBindings program = policy
  | _, _, .ret _, policy, _ => Subsingleton.elim _ _
  | _, _, .sample _ _ _ next, policy, submits => submitBindings_eq_self next policy submits
  | _, _, .commit _ _ _ _ next, policy, submits => by
      apply Prod.ext
      · funext own view active
        change (policy.1 own view active).map _ = policy.1 own view active
        calc
          _ = (policy.1 own view active).map id := by
            apply map_congr_on_support
            intro choice supported
            cases choice with
            | none => exact (submits.1 own view active supported).elim
            | some value => rfl
          _ = _ := PMF.map_id _
      · exact submitBindings_eq_self next policy.2 submits.2
  | _, _, .reveal _ _ _ _ _ _ next, policy, submits =>
      Prod.ext rfl (submitBindings_eq_self next policy.2 submits)

theorem BehavioralPolicy.submitBindings_idem {who : Player} {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O) (policy : BehavioralPolicy who
      program) :
    (policy.submitBindings program).submitBindings program = policy.submitBindings program :=
  submitBindings_eq_self program _ (submitsBindings_submitBindings program policy)

end Vegas.SourceProgram
