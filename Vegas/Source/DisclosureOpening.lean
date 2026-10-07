/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.DisclosureBehavioral
import Vegas.Source.Disclosure

/-! # Opening every effective disclosure

A policy opens effectively when at every own reveal it discloses exactly when
the disclosure is effective, that is, when its bound value opens and passes the
guard (`Vegas.SourceProgram.BehavioralPolicy.OpensEffectively`). Its decision
then depends on its view only through the opening's own result, which the
owner's stored commitment determines. Normalizing a policy that always
discloses gives one (`Vegas.SourceProgram.BehavioralPolicy.opensEffectively_forceDisclose`),
and the clients that open whatever else is pending follow such a profile
(`Vegas.SourceProgram.openingProfile`).
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- At every own reveal, the policy discloses exactly when the disclosure is
effective. The registry and publication positions are carried by the source
syntax. -/
def BehavioralPolicy.OpensEffectively {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → Registry Γ → Revelations Γ →
    BehavioralPolicy who program → Prop
  | _, _, .ret _, _, _, _ => True
  | _, _, .sample _ _ _ next, registry, revelations, policy =>
      OpensEffectively next registry.weaken revelations.weaken policy
  | _, _, .commit (payload := payload) name owner _ guard next, registry, revelations, policy =>
      OpensEffectively next
        ({ owner := owner, subject := name, payload := payload, source := .here,
            guard := guard.weaken } :: registry.weaken) revelations.weaken policy.2
  | _, _, .reveal published _ _ _ selected _ next, registry, revelations, policy =>
      (∀ own view, policy.1 own view = PMF.pure
        (effectiveDisclosureView published selected registry revelations
          (own.symm ▸ view.1) true)) ∧
      OpensEffectively next registry.weaken
        (revelations.reveal (published := published) selected) policy.2

/-- Normalizing a policy that always discloses opens effectively. -/
theorem BehavioralPolicy.opensEffectively_forceDisclose {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) →
    (registry : Registry Γ) → (revelations : Revelations Γ) →
    (remember : DecisionView who Γ → PMF (List (OwnAction Player L))) →
    (policy : BehavioralPolicy who program) →
    ((policy.forceDisclose program).normalizeDisclosureFrom program registry revelations
      remember).OpensEffectively program registry revelations
  | _, _, .ret _, _, _, _, _ => trivial
  | _, _, .sample _ _ _ next, registry, revelations, remember, policy =>
      opensEffectively_forceDisclose next _ _ _ policy
  | _, _, .commit _ _ _ _ next, registry, revelations, remember, policy =>
      opensEffectively_forceDisclose next _ _ _ policy.2
  | _, _, .reveal published owner _ _ selected _ next,
      registry, revelations, remember, policy => by
      refine ⟨?_, opensEffectively_forceDisclose next _ _ _ policy.2⟩
      intro own view
      cases own
      simp only [normalizeDisclosureFrom, forceDisclose, disclosureMemoryLaw, PMF.pure_map]
      rw [PMF.map_bind]
      simp only [PMF.pure_map]
      exact PMF.bind_const _ _

/-- The profile whose policies always disclose, normalized: every player opens
exactly its effective disclosures. -/
def openingProfile {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (registry : Registry Γ)
    (revelations : Revelations Γ) (profile : BehavioralProfile program) :
    BehavioralProfile program :=
  normalizeDisclosureProfile program registry revelations fun player =>
    (profile player).forceDisclose program

/-- Every player of the opening profile opens effectively. -/
theorem openingProfile_opensEffectively {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (registry : Registry Γ)
    (revelations : Revelations Γ) (profile : BehavioralProfile program) (who : Player) :
    (openingProfile program registry revelations profile who).OpensEffectively program
      registry revelations :=
  BehavioralPolicy.opensEffectively_forceDisclose program registry revelations _ (profile who)

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
      change ((fun _ _ => PMF.pure true), policy.2.forceDisclose next) = policy
      rw [forceDisclose_eq_of_disclosing next policy.2 disclosing.2]
      refine Prod.ext ?_ rfl
      funext own view
      exact (eq_pure_true_of_false_not_mem (disclosing.1 own view)).symm

/-- A profile that discloses at every reveal is its own opening profile after
normalization. -/
theorem openingProfile_eq_of_disclosing {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (registry : Registry Γ)
    (revelations : Revelations Γ) (profile : BehavioralProfile program)
    (disclosing : ∀ who, Disclosing program (profile who)) :
    openingProfile program registry revelations profile =
      normalizeDisclosureProfile program registry revelations profile := by
  unfold openingProfile
  congr 1
  funext who
  exact BehavioralPolicy.forceDisclose_eq_of_disclosing program (profile who) (disclosing who)

end Vegas.SourceProgram
