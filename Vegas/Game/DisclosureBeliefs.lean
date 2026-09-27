/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.DisclosureRetraction
import GameTheoryExtensions.Math.Probability.ObservationRetraction

/-! # Actual prefix posteriors after private disclosure aggregation

Conditioning an original private intention and then compressing its history
gives the posterior at the corresponding effective-disclosure observation.
The statement follows from actual source prefix execution, including an
arbitrary correlated initial distribution. No posterior compatibility is
assumed, and no positive limiting reach is required.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {who : Player}

/-- At every positive original observation, private disclosure intentions
provide no additional information about the compressed state. This is an
exact prefix posterior equation, including all hidden cells and opponents'
private histories. It applies separately at each positive perturbation. -/
theorem normalized_disclosure_prefix_posterior {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (policy : BehavioralPolicy who program) (registry : Registry Γ)
    (revelations : Revelations Γ) (initial : FinDist (Config Player L Γ))
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
    ∀ observed ∈ (original.map (ProtocolState.observe who program)).support,
      (original.condOnFibre (ProtocolState.observe who program) observed).map
          (ProtocolState.normalizeDisclosureRecall (who := who) program (fun view => view.2)) =
        normalized.condOnFibre (ProtocolState.observe who program)
          (ProtocolView.normalizeDisclosureRecall program (fun view => view.2) observed) := by
  dsimp only
  intro observed present
  let original := initial.bind fun config =>
    (fun distribution => distribution.bind (ProtocolState.behavioralStateStep program
      (Function.update profile who policy)))^[count]
        (FinDist.pure (ProtocolState.entry program config))
  let normalized := initial.bind fun config =>
    (fun distribution => distribution.bind (ProtocolState.behavioralStateStep program
      (Function.update profile who (policy.normalizeDisclosures program registry revelations))))
        ^[count] (FinDist.pure (ProtocolState.entry program config))
  let kernel := policy.disclosureMemory program registry revelations
    (fun view => FinDist.pure view.2)
  have expanded : original = normalized.bind kernel := by
    rw [FinDist.bind_bind]
    apply FinDist.bind_congr
    intro config supported
    have equation := normalized_disclosure_prefix program profile policy config count
    rw [registryEq config supported, revelationsEq config supported] at equation
    exact equation
  have restores : ∀ state ∈ normalized.support, ∀ original ∈ (kernel state).support,
      ProtocolState.normalizeDisclosureRecall (who := who) program
        (fun view => view.2) original = state := by
    intro state supported original member
    obtain ⟨config, supportedConfig, reached⟩ :=
      Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
    have retained := disclosure_prefix_retracts program profile policy
      (fun view => FinDist.pure view.2) (fun view => view.2) config
      (fun past chosen => FinDist.mem_support_pure.mp chosen) count
    rw [registryEq config supportedConfig, revelationsEq config supportedConfig] at retained
    exact retained state reached original member
  have result := FinDist.conditional_retraction normalized kernel
    (ProtocolState.normalizeDisclosureRecall (who := who) program (fun view => view.2))
    (ProtocolState.observe who program) (ProtocolState.observe who program)
    (ProtocolView.normalizeDisclosureRecall program (fun view => view.2))
    (ProtocolState.observe_normalizeDisclosureRecall program (fun view => view.2))
    restores
    (fun left _ right _ same => policy.disclosureMemory_observation_congr program
      registry revelations (fun view => FinDist.pure view.2) left right same)
    observed (by rwa [← expanded])
  rw [← expanded] at result
  exact result

end Vegas.SourceProgram
