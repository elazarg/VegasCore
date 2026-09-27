/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.DisclosureBehavioral
import Vegas.Source.ProtocolBehavioralPolicy

/-! # Support of effective source choices

A policy completed at unreachable views can support every admitted source
choice. The existing private-intention normalization then supports exactly
the effective representatives needed by the native service. Failed guarded
intentions may collapse to withholding; no full-support claim in the original
unquotiented disclosure menu is made for the normalized policy.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Every admitted constructor choice occurs at every source decision view,
including views outside the initialized history tree. -/
def BehavioralPolicy.SupportsChoices {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → CommitmentInterface program →
    BehavioralPolicy who program → Prop
  | _, _, .ret _, _, _ => True
  | _, _, .sample _ _ _ next, admission, policy => SupportsChoices next admission policy
  | _, _, .commit _ owner _ _ next, admission, policy =>
      (∀ (own : owner = who) view choice, (admission none).Admits choice →
        choice ∈ (policy.1 own view).support) ∧
      SupportsChoices next (fun site => admission (some site)) policy.2
  | _, _, .reveal _ owner _ _ _ _ next, admission, policy =>
      (∀ (own : owner = who) view choice, choice ∈ (policy.1 own view).support) ∧
      SupportsChoices next admission policy.2

/-- Bindings retain admitted values. A disclosure needs support only for
the Boolean choices fixed by the actual deferred guard normalization. -/
def BehavioralPolicy.SupportsEffectiveChoices {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → CommitmentInterface program →
    Registry Γ → Revelations Γ → BehavioralPolicy who program → Prop
  | _, _, .ret _, _, _, _, _ => True
  | _, _, .sample _ _ _ next, admission, registry, revelations, policy =>
      SupportsEffectiveChoices next admission registry.weaken revelations.weaken policy
  | _, _, .commit (payload := payload) name owner _ guard next,
      admission, registry, revelations, policy =>
      (∀ (own : owner = who) view choice, (admission none).Admits choice →
        choice ∈ (policy.1 own view).support) ∧
      SupportsEffectiveChoices next (fun site => admission (some site))
        (({ owner := owner, subject := name, payload := payload, source := .here,
            guard := guard.weaken } : Obligation _) :: registry.weaken)
        revelations.weaken policy.2
  | _, _, .reveal published owner _ _ selected _ next,
      admission, registry, revelations, policy =>
      (∀ (own : owner = who) view choice,
        effectiveDisclosureView published (own ▸ selected) registry revelations view.1 choice =
            choice → choice ∈ (policy.1 own view).support) ∧
      SupportsEffectiveChoices next admission registry.weaken
        (revelations.reveal selected) policy.2

/-- Full support of the existing information-local protocol laws supplies all
admitted constructor choices, without a source-state reachability premise. -/
theorem BehavioralPolicy.supportsChoices_of_protocolAction {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (policy : BehavioralPolicy who program) →
    (∀ view action, ProtocolView.menu who program admission view action →
      action ∈ (policy.protocolAction program view).support) →
    policy.SupportsChoices program admission
  | _, _, .ret _, _, _, _ => trivial
  | _, _, .sample _ _ _ next, admission, policy, full =>
      policy.supportsChoices_of_protocolAction next admission
        (fun view action legal => full (Sum.inr view) action legal)
  | _, _, .commit (payload := payload) name owner fresh guard next, admission, policy, full => by
      refine ⟨?_, policy.2.supportsChoices_of_protocolAction next
        (fun site => admission (some site))
          (fun view action legal => full (Sum.inr view) action legal)⟩
      intro own view choice admitted
      have supported := full (Sum.inl view) (some (.commit owner name payload choice))
        ⟨congrArg some own, choice, admitted, rfl⟩
      simp only [protocolAction, Sum.elim_inl, dite_eq_left own, FinDist.support_map]
        at supported
      obtain ⟨other, member, same⟩ := supported
      have equal := congrArg (OwnAction.binding owner name payload) same
      simp only [OwnAction.binding_commit] at equal
      exact equal ▸ member
  | _, _, .reveal published owner name fresh binding unresolved next,
      admission, policy, full => by
      refine ⟨?_, policy.2.supportsChoices_of_protocolAction next admission
        (fun view action legal => full (Sum.inr view) action legal)⟩
      intro own view choice
      have supported := full (Sum.inl view) (some (.reveal owner name choice))
        ⟨congrArg some own, choice, rfl⟩
      simp only [protocolAction, Sum.elim_inl, dite_eq_left own, FinDist.support_map]
        at supported
      obtain ⟨other, member, same⟩ := supported
      have equal : other = choice := congrArg OwnAction.disclosure same
      exact equal ▸ member

theorem BehavioralPolicy.fromProtocol_supports {who : Player}
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (policy : (view : ProtocolView who program) → FinDist
      {action : Option (OwnAction Player L) //
        ProtocolView.menu who program admission view action})
    (full : ∀ view, (policy view).FullSupport) :
    (fromProtocol program admission policy).SupportsChoices program admission := by
  apply supportsChoices_of_protocolAction program admission
  intro view action legal
  rw [protocolAction_fromProtocol, FinDist.support_map]
  exact ⟨⟨action, legal⟩, full view ⟨action, legal⟩, rfl⟩

/-- Any supported private-memory value supplies each effective action.
The conditional memory law need not put positive mass on every intention. -/
theorem BehavioralPolicy.normalizeDisclosureFrom_supports {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (registry : Registry Γ) → (revelations : Revelations Γ) →
    (remember : DecisionView who Γ → FinDist (List (OwnAction Player L))) →
    (policy : BehavioralPolicy who program) → policy.SupportsChoices program admission →
    (policy.normalizeDisclosureFrom program registry revelations remember).SupportsEffectiveChoices
      program admission registry revelations
  | _, _, .ret _, _, _, _, _, _, _ => trivial
  | _, _, .sample _ _ _ next, admission, registry, revelations, remember, policy, full =>
      policy.normalizeDisclosureFrom_supports next admission registry.weaken revelations.weaken
        (fun view => remember (view.back false)) full
  | _, _, .commit name owner _ guard next,
      admission, registry, revelations, remember, policy, full => by
      refine ⟨?_, policy.2.normalizeDisclosureFrom_supports next _ _ _ _ full.2⟩
      intro own view choice admitted
      subst who
      obtain ⟨past, remembered⟩ := (remember view).support_nonempty
      change choice ∈ ((bindingMemoryLaw name _ remember (policy.1 rfl) view).map
        Prod.fst).support
      rw [FinDist.support_map]
      refine ⟨(choice, past ++ [.commit owner name _ choice]), ?_, rfl⟩
      rw [bindingMemoryLaw, FinDist.support_bind]
      refine Set.mem_iUnion₂.mpr ⟨past, remembered, ?_⟩
      rw [FinDist.support_map]
      exact ⟨choice, full.1 rfl (view.1, past) choice admitted, rfl⟩
  | _, _, .reveal published owner name _ selected _ next,
      admission, registry, revelations, remember, policy, full => by
      refine ⟨?_, policy.2.normalizeDisclosureFrom_supports next _ _ _ _ full.2⟩
      intro own view choice effective
      subst who
      obtain ⟨past, remembered⟩ := (remember view).support_nonempty
      change choice ∈ ((disclosureMemoryLaw published selected registry revelations
        remember (policy.1 rfl) view).map Prod.fst).support
      rw [FinDist.support_map]
      refine ⟨(choice, past ++ [.reveal owner name choice]), ?_, rfl⟩
      rw [disclosureMemoryLaw, FinDist.support_bind]
      refine Set.mem_iUnion₂.mpr ⟨past, remembered, ?_⟩
      rw [FinDist.support_map]
      exact ⟨choice, full.1 rfl (view.1, past) choice, by simp only [effective]⟩

/-- Simultaneous normalization preserves all effective constructor choices,
without asserting that any intermediate normalized profile is an equilibrium. -/
theorem normalizeDisclosureProfile_supports {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (registry : Registry Γ) (revelations : Revelations Γ)
    (profile : BehavioralProfile program)
    (full : ∀ who, (profile who).SupportsChoices program admission) (who : Player) :
    (normalizeDisclosureProfile program registry revelations profile who).SupportsEffectiveChoices
      program admission registry revelations :=
  (profile who).normalizeDisclosureFrom_supports program admission registry revelations
    (fun view => FinDist.pure view.2) (full who)

end Vegas.SourceProgram
