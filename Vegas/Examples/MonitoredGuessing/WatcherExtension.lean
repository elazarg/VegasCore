/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.RestrictedClock
import Interaction.ReactiveFiniteAssessment
import GameTheoryExtensions.Analysis.Protocol.RestrictionExtension

/-! # Restoring every effective watcher response

The watched game already admits every effective ordinary-player response.
If the watcher's utility is identically zero, each of its equilibria extends
to the full effective game. Ordinary-player utilities may be arbitrary fixed
functions of the native state, including publicly collected charges.

The conclusion uses one common consistent assessment and preserves the complete
initialized history/payoff law. It proves neither strict reporting incentives
nor resistance to transfers or coalitions involving the watcher.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

theorem ordinary_choice_surjective (who : Player) (ordinary : who ≠ watcher)
    (info : nativeApp.Info) : Function.Surjective (watcherRestriction.choice who info) := by
  intro action
  have member := action.2
  refine ⟨⟨action.1, ?_⟩, ?_⟩
  · cases info with
    | none => exact member
    | some data =>
        obtain ⟨response, allowed, same⟩ := member
        exact ⟨response, by simpa only [watchedMenu, ordinary, ↓reduceIte] using allowed, same⟩
  · exact Subtype.ext rfl

/-- Zero utility at every history suffices to restore all watcher alternatives.
The utility function and both games are fixed before selecting the watched SE. -/
theorem watcher_equilibrium_extends
    (utility : nativeApp.ProtocolState → Player → ℝ)
    (indifferent : ∀ state, utility state watcher = 0)
    (source : watchedModel.BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor watched_decisionRecall.decisionInformationAntichain
      (fun who site => source.continuationContext site
        (fun history => utility history.state who)
        (2 * nativeHorizon + 1 - watchedDepth who site))) :
    ∃ target : effectiveModel.BehavioralAssessment,
      target.IsSequentialEquilibriumFor effective_decisionRecall.decisionInformationAntichain
        (fun who site => target.continuationContext site
          (fun history => utility history.state who)
          (2 * nativeHorizon + 1 - effectiveDepth who site)) ∧
      watcherRestriction.ExtendsProfile source.strategy target.strategy ∧
      (∀ who site, target.belief who (watcherRestriction.site who site) =
        (source.belief who site).map (watcherRestriction.informationHistory who site)) ∧
      (watchedModel.runBehavioral source.strategy (2 * nativeHorizon + 1)).map
          watcherRestriction.history =
        effectiveModel.runBehavioral target.strategy (2 * nativeHorizon + 1) ∧
      (watchedModel.runBehavioral source.strategy (2 * nativeHorizon + 1)).map
          (fun history => (watcherRestriction.history history, utility history.state)) =
        (effectiveModel.runBehavioral target.strategy (2 * nativeHorizon + 1)).map
          (fun history => (history, utility history.state)) ∧
      ∀ history ∈ (effectiveModel.runBehavioral target.strategy
        (2 * nativeHorizon + 1)).support, effectiveArena.terminal history.state := by
  classical
  apply watcherRestriction.sequential_equilibrium_extends_of_indifference
    watched_decisionRecall.decisionInformationAntichain
    (effectiveMenu.uniformAssessment nativeInitialLaw nativeHorizon nativeScheduler)
    (effectiveMenu.uniform_fullyMixed nativeInitialLaw nativeHorizon nativeScheduler)
    effective_decisionRecall (2 * nativeHorizon + 1)
    (effectiveMenu.bounded nativeInitialLaw nativeHorizon nativeScheduler)
    effectiveDepth effective_common_depth
    (fun history who => utility history.state who)
    (fun history who => utility history.state who) (fun _ _ => rfl)
    _ source equilibrium
  intro who
  by_cases same : who = watcher
  · subst who
    exact Or.inr ⟨0, fun history => indifferent history.state⟩
  · exact Or.inl (ordinary_choice_surjective who same)

end Vegas.Examples.MonitoredGuessing.Restricted
