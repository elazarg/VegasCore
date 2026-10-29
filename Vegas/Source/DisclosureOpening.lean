/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.DisclosureBehavioral
import Vegas.Source.Disclosure

/-! # Opening every authentic binding

An authentic opening discloses exactly when the owner's immutable binding
contains a value. Deferred guard rejection does not suppress the attempt.
The opening profile normalizes the profile that always requests disclosure.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- At every active own reveal, open precisely the bindings that contain a value. -/
def BehavioralPolicy.OpensAuthentically {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → BehavioralPolicy who program → Prop
  | _, _, .ret _, _ => True
  | _, _, .sample _ _ _ next, policy => OpensAuthentically next policy
  | _, _, .commit _ _ _ _ next, policy => OpensAuthentically next policy.2
  | _, _, .reveal _ _ _ _ selected _ next, policy =>
      (∀ own view active, policy.1 own view active = PMF.pure
        ((view.observation.cells.get (own ▸ selected)).getD .failure).isSuccess) ∧
      OpensAuthentically next policy.2

/-- Normalizing a policy that always requests disclosure opens every authentic binding. -/
theorem BehavioralPolicy.opensAuthentically_forceDisclose {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (policy : BehavioralPolicy who program) →
    ((policy.forceDisclose program).normalizeDisclosures program).OpensAuthentically program
  | _, _, .ret _, _ => trivial
  | _, _, .sample _ _ _ next, policy => opensAuthentically_forceDisclose next policy
  | _, _, .commit _ _ _ _ next, policy => opensAuthentically_forceDisclose next policy.2
  | _, _, .reveal _ _ _ _ _ _ next, policy => by
      refine ⟨?_, opensAuthentically_forceDisclose next policy.2⟩
      intro own view active
      simp only [normalizeDisclosures, forceDisclose, PMF.pure_map, Bool.true_and]

/-- Retain binding kernels and disclose every authentic own binding. -/
def BehavioralPolicy.authenticOpening {who : Player} {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (policy : BehavioralPolicy who program) : BehavioralPolicy who program :=
  (policy.forceDisclose program).normalizeDisclosures program

/-- Every player opens each authentic binding, retaining the original binding policies. -/
def openingProfile {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program) :
    BehavioralProfile program :=
  fun player => (profile player).authenticOpening program

/-- Every player of the opening profile opens exactly its authentic bindings. -/
theorem openingProfile_opensAuthentically {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program) (who : Player) :
    (openingProfile program profile who).OpensAuthentically program :=
  BehavioralPolicy.opensAuthentically_forceDisclose program (profile who)

/-- A law on decisions that never refuses discloses surely. -/
theorem eq_pure_true_of_false_not_mem {law : PMF Bool} (never : false ∉ law.support) :
    law = PMF.pure true := by
  have refused : law false = 0 := (PMF.apply_eq_zero_iff law false).mpr never
  have total := law.tsum_coe
  rw [tsum_bool, refused, zero_add] at total
  ext decision
  cases decision
  · rw [refused, PMF.pure_apply, ite_eq_right Bool.false_ne_true]
  · rw [total, PMF.pure_apply, ite_eq_left rfl]

/-- Forcing a disclosing policy to disclose changes nothing. -/
theorem BehavioralPolicy.forceDisclose_eq_of_disclosing {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (policy : BehavioralPolicy who program) → Disclosing program policy →
      policy.forceDisclose program = policy
  | _, _, .ret _, _, _ => rfl
  | _, _, .sample _ _ _ next, policy, disclosing =>
      forceDisclose_eq_of_disclosing next policy disclosing
  | _, _, .commit _ _ _ _ next, policy, disclosing => by
      change (policy.1, policy.2.forceDisclose next) = policy
      rw [forceDisclose_eq_of_disclosing next policy.2 disclosing]
  | _, _, .reveal _ _ _ _ _ _ next, policy, disclosing => by
      change ((fun _ _ _ => PMF.pure true), policy.2.forceDisclose next) = policy
      rw [forceDisclose_eq_of_disclosing next policy.2 disclosing.2]
      refine Prod.ext ?_ rfl
      funext own view active
      exact (eq_pure_true_of_false_not_mem (disclosing.1 own view active)).symm

/-- A profile that discloses at every reveal is its own opening profile after
normalization. -/
theorem openingProfile_eq_of_disclosing {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (disclosing : ∀ who, Disclosing program (profile who)) :
    openingProfile program profile =
      normalizeDisclosureProfile program profile := by
  funext who
  change ((profile who).forceDisclose program).normalizeDisclosures program = _
  rw [BehavioralPolicy.forceDisclose_eq_of_disclosing program (profile who) (disclosing who)]
  rfl

end Vegas.SourceProgram
