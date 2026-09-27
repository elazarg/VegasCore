/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.DisclosureContinuation
import Vegas.Game.DisclosureRealization

/-! # Exact conditional comparisons after private disclosure aggregation

Every continuation comparison at a positive normalized source observation is
one finite mixture of comparisons at actual positive original observations.
The same mixture represents the prescribed and deviating terminal laws.
The source policies in that mixture are admitted and chosen uniformly across
their hidden-state fibers. All beliefs are derived from actual prefix laws.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {who : Player}

/-- Private ineffective-disclosure aliases admit exact whole-continuation
simulation at every positive normalized prefix observation. This is an
operational comparison theorem: it does not assert that normalization is
fully mixed in the original, larger source action menu. -/
theorem normalized_disclosure_prefix_comparison {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (profile : BehavioralProfile program) (policy alternative : BehavioralPolicy who program)
    (permitted : alternative.Admitted program admission)
    (registry : Registry Γ) (revelations : Revelations Γ)
    (initial : FinDist (Config Player L Γ))
    (registryEq : ∀ config ∈ initial.support, config.registry = registry)
    (revelationsEq : ∀ config ∈ initial.support, @config.revelations = @revelations)
    (count : Nat) :
    let original := initial.bind fun config =>
      (fun distribution => distribution.bind (ProtocolState.behavioralStateStep program
        (Function.update profile who policy)))^[count]
          (FinDist.pure (ProtocolState.entry program config))
    let normalized := initial.bind fun config =>
      (fun distribution => distribution.bind (ProtocolState.behavioralStateStep program
        (Function.update profile who (policy.normalizeDisclosures program registry revelations))))
          ^[count] (FinDist.pure (ProtocolState.entry program config))
    let observe := ProtocolState.observe who program
    let project := ProtocolView.normalizeDisclosureRecall program (fun view => view.2)
    ∀ view ∈ (normalized.map observe).support,
      ∃ alternatives : FinDist (ProtocolView who program ×
          {lifted : BehavioralPolicy who program // lifted.Admitted program admission}),
        (∀ selected ∈ alternatives.support,
          selected.1 ∈ (original.map observe).support ∧ project selected.1 = view) ∧
        ((normalized.condOnFibre observe view).bind (ProtocolState.continuationLaw program
          (Function.update profile who
            (policy.normalizeDisclosures program registry revelations)))) =
          alternatives.bind (fun selected => (original.condOnFibre observe selected.1).bind
            (ProtocolState.continuationLaw program (Function.update profile who policy))) ∧
        ((normalized.condOnFibre observe view).bind
          (ProtocolState.continuationLaw program (Function.update profile who alternative))) =
          alternatives.bind (fun selected => (original.condOnFibre observe selected.1).bind
            (ProtocolState.continuationLaw program
              (Function.update profile who selected.2.1))) := by
  classical
  dsimp only
  intro view present
  let original := initial.bind fun config =>
    (fun distribution => distribution.bind (ProtocolState.behavioralStateStep program
      (Function.update profile who policy)))^[count]
        (FinDist.pure (ProtocolState.entry program config))
  let normalized := initial.bind fun config =>
    (fun distribution => distribution.bind (ProtocolState.behavioralStateStep program
      (Function.update profile who (policy.normalizeDisclosures program registry revelations))))
        ^[count] (FinDist.pure (ProtocolState.entry program config))
  let observe := ProtocolState.observe who program
  let project := ProtocolView.normalizeDisclosureRecall (who := who) program (fun view => view.2)
  let retract := ProtocolState.normalizeDisclosureRecall (who := who) program (fun view => view.2)
  let kernel := policy.disclosureMemory program registry revelations
    (fun view => FinDist.pure view.2)
  have expanded : original = normalized.bind kernel := by
    rw [FinDist.bind_bind]
    apply FinDist.bind_congr
    intro config supported
    have equation := normalized_disclosure_prefix program profile policy config count
    rw [registryEq config supported, revelationsEq config supported] at equation
    exact equation
  have retracts : ∀ state ∈ normalized.support, ∀ old ∈ (kernel state).support,
      retract old = state := by
    intro state supported old member
    obtain ⟨config, supportedConfig, reached⟩ :=
      Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
    have retained := disclosure_prefix_retracts program profile policy
      (fun view => FinDist.pure view.2) (fun view => view.2) config
      (fun past chosen => FinDist.mem_support_pure.mp chosen) count
    rw [registryEq config supportedConfig, revelationsEq config supportedConfig] at retained
    exact retained state reached old member
  have projects : ∀ state ∈ normalized.support, ∀ old ∈ (kernel state).support,
      (project ∘ observe) old = observe state := by
    intro state supported old member
    exact (ProtocolState.observe_normalizeDisclosureRecall program
      (fun view => view.2) old).symm.trans (congrArg observe (retracts state supported old member))
  let restored := original.condOnFibre (project ∘ observe) view
  let views := restored.map observe
  let lift (oldView : ProtocolView who program) : BehavioralPolicy who program :=
    (exists_disclosure_continuation_lift program admission profile alternative permitted
      (fun view => view.2) oldView).choose
  have legal (oldView : ProtocolView who program) : (lift oldView).Admitted program admission :=
    (exists_disclosure_continuation_lift program admission profile alternative permitted
      (fun view => view.2) oldView).choose_spec.1
  let alternatives : FinDist (ProtocolView who program ×
      {lifted : BehavioralPolicy who program // lifted.Admitted program admission}) :=
    views.map fun oldView => (oldView, ⟨lift oldView, legal oldView⟩)
  have meets : ∃ state ∈ (project ∘ observe) ⁻¹' {view}, state ∈ original.support := by
    obtain ⟨state, supported, observed⟩ := FinDist.support_map .. ▸ present
    obtain ⟨old, member⟩ := (kernel state).support_nonempty
    refine ⟨old, (projects state supported old member).trans observed, ?_⟩
    rw [expanded, FinDist.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨state, supported, member⟩
  have viewSupport (oldView : ProtocolView who program) (supported : oldView ∈ views.support) :
      oldView ∈ (original.map observe).support ∧ project oldView = view := by
    obtain ⟨state, member, same⟩ := FinDist.support_map .. ▸ supported
    change state ∈ (original.condOnFibre (project ∘ observe) view).support at member
    rw [FinDist.condOnFibre, dite_eq_left meets] at member
    have details := FinDist.support_condOn _ _ _ member
    refine ⟨?_, ?_⟩
    · rw [FinDist.support_map]
      exact ⟨state, details.2, same⟩
    · exact (congrArg project same).symm.trans details.1
  have conditional : restored = (normalized.condOnFibre observe view).bind kernel := by
    change (original.condOnFibre (project ∘ observe) view) = _
    rw [expanded]
    exact FinDist.conditional_bind_of_observation normalized kernel observe (project ∘ observe)
      projects view present
  have originalFibers : ∀ oldView ∈ views.support,
      restored.condOnFibre observe oldView = original.condOnFibre observe oldView := by
    intro oldView supported
    exact FinDist.conditional_fiber_after_projection original observe project view oldView supported
  refine ⟨alternatives, ?_, ?_, ?_⟩
  · intro selected supported
    obtain ⟨oldView, member, rfl⟩ := FinDist.support_map .. ▸ supported
    exact viewSupport oldView member
  · change ((normalized.condOnFibre observe view).bind _) = _
    rw [show alternatives = _ from rfl, FinDist.bind_map]
    trans restored.bind (ProtocolState.continuationLaw program
      (Function.update profile who policy))
    · rw [conditional, FinDist.bind_bind]
      apply FinDist.bind_congr
      intro state supported
      obtain ⟨witness, supportedWitness, observed⟩ := FinDist.support_map .. ▸ present
      have targetMeets : ∃ state ∈ observe ⁻¹' {view}, state ∈ normalized.support :=
        ⟨witness, observed, supportedWitness⟩
      rw [FinDist.condOnFibre, dite_eq_left targetMeets] at supported
      obtain ⟨config, supportedConfig, reached⟩ := Set.mem_iUnion₂.mp
        (FinDist.support_bind .. ▸ (FinDist.support_condOn _ _ _ supported).2)
      have realized := disclosure_prefix_continuation_realizes program profile policy
        (fun view => FinDist.pure view.2) config count
      rw [registryEq config supportedConfig, revelationsEq config supportedConfig] at realized
      exact (realized state reached).symm
    · conv_lhs => arg 1; rw [restored.eq_bind_condOnFibre observe]
      rw [FinDist.bind_bind]
      exact FinDist.bind_congr fun oldView supported =>
        congrArg (FinDist.bind · _) (originalFibers oldView supported)
  · change ((normalized.condOnFibre observe view).bind _) = _
    rw [show alternatives = _ from rfl, FinDist.bind_map]
    trans views.bind fun _ => (normalized.condOnFibre observe view).bind
      (ProtocolState.continuationLaw program (Function.update profile who alternative))
    · exact (FinDist.bind_const ..).symm
    · apply FinDist.bind_congr
      intro oldView supported
      have properties := viewSupport oldView supported
      have posterior := normalized_disclosure_prefix_posterior program profile policy registry
        revelations initial registryEq revelationsEq count oldView properties.1
      change (original.condOnFibre observe oldView).map retract =
        normalized.condOnFibre observe (project oldView) at posterior
      rw [properties.2] at posterior
      rw [← posterior, FinDist.bind_map]
      symm
      apply FinDist.bind_congr
      intro state member
      apply (exists_disclosure_continuation_lift program admission profile alternative permitted
        (fun view => view.2) oldView).choose_spec.2 state
      obtain ⟨witness, supportedWitness, observed⟩ := FinDist.support_map .. ▸ properties.1
      have oldMeets : ∃ state ∈ observe ⁻¹' {oldView}, state ∈ original.support :=
        ⟨witness, observed, supportedWitness⟩
      rw [FinDist.condOnFibre, dite_eq_left oldMeets] at member
      exact (FinDist.support_condOn _ _ _ member).1

end Vegas.SourceProgram
