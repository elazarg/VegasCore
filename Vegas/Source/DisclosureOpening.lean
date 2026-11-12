module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Source.DisclosureBehavioral
public import Vegas.Source.Disclosure

@[expose] public section

/-! # Opening every effective binding

An opening discloses exactly when its guarded publication would contain a
value. The opening profile normalizes an always-disclosing source profile.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- At every active reveal, disclose exactly when the owner-local guarded
publication succeeds, using the static metadata at the instruction. -/
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
      (∀ own view active, policy.1 own view active = PMF.pure
        (effectiveDisclosureView published (own ▸ selected) registry revelations view true)) ∧
      OpensEffectively next registry.weaken
        (revelations.reveal (published := published) selected) policy.2

/-- Normalizing an always-disclosing policy chooses every effective opening. -/
theorem BehavioralPolicy.opensEffectively_forceDisclose {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (registry : Registry Γ) →
    (revelations : Revelations Γ) → (policy : BehavioralPolicy who program) →
    OpensEffectively program registry revelations
      ((policy.forceDisclose program).normalizeDisclosuresFrom program registry revelations)
  | _, _, .ret _, _, _, _ => trivial
  | _, _, .sample _ _ _ next, _, _, policy => opensEffectively_forceDisclose next _ _ policy
  | _, _, .commit _ _ _ _ next, _, _, policy => opensEffectively_forceDisclose next _ _ policy.2
  | _, _, .reveal _ _ _ _ _ _ next, _, _, policy => by
      refine ⟨?_, opensEffectively_forceDisclose next _ _ policy.2⟩
      intro own view active
      simp only [normalizeDisclosuresFrom, forceDisclose, PMF.pure_map]

/-- Retain binding kernels and attempt every opening that would publish a value. -/
def BehavioralPolicy.authenticOpening {who : Player} {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (policy : BehavioralPolicy who program) : BehavioralPolicy who program :=
  (policy.forceDisclose program).normalizeDisclosures program

/-- Every player attempts every effective opening, retaining its binding kernels. -/
def openingProfile {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program) :
    BehavioralProfile program :=
  fun player => (profile player).authenticOpening program

/-- Every player of the opening profile chooses exactly the effective openings. -/
theorem openingProfile_opensEffectively {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program) (who : Player) :
    BehavioralPolicy.OpensEffectively program [] (Revelations.initial Γ)
      (openingProfile program profile who) :=
  BehavioralPolicy.opensEffectively_forceDisclose program _ _ (profile who)

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
