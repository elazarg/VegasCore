/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.WatcherExtension
import Vegas.Pending.ReactiveAliasEquilibrium
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Restoring watcher choices and every bounded raw response

The watched game extends first to effective responses, then to all raw private
representations. Utilities and observations must ignore only the proved private
normalization. The joint observation/payoff law is retained. This closes the
last two edges of the fixture's strategic stack; it does not supply the source
interpretation or the ordinary-player enforcement comparisons.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

theorem watcher_raw_equilibrium_extends
    {Observation : Type} (observe : nativeApp.ProtocolState → Observation)
    (observationInvariant : ∀ state, observe (normalization.state state) = observe state)
    (utility : nativeApp.ProtocolState → Player → ℝ)
    (utilityInvariant : ∀ state, utility (normalization.state state) = utility state)
    (indifferent : ∀ state, utility state watcher = 0)
    (source : watchedModel.BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor watched_decisionRecall.antichain
      (fun who site => source.continuationContext site
        (fun history => utility history.state who)
        (2 * nativeHorizon + 1 - watchedDepth who site))) :
    ∃ target : nativeModel.BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        (nativeMenu.decisionInformationAntichain nativeInitialLaw nativeHorizon nativeScheduler)
        (fun who site => target.continuationContext site
          (fun history => utility history.state who) (2 * nativeHorizon + 1)) ∧
      (nativeModel.runBehavioral target.strategy (2 * nativeHorizon + 1)).map
          (fun history => (observe history.state, utility history.state)) =
        (watchedModel.runBehavioral source.strategy (2 * nativeHorizon + 1)).map
          (fun history => (observe history.state, utility history.state)) := by
  classical
  obtain ⟨effective, effectiveSE, _, _, executionLaw, _, _⟩ :=
    watcher_equilibrium_extends utility indifferent source equilibrium
  have fullSE := (effective.sequentialEquilibrium_remaining_iff effectiveModel
    effective_decisionRecall.antichain (2 * nativeHorizon + 1)
    (effectiveMenu.bounded nativeInitialLaw nativeHorizon nativeScheduler)
    effectiveDepth effective_common_depth (fun who history => utility history.state who)).mp
      effectiveSE
  obtain ⟨raw, _, rawSE, _, projected⟩ :=
    nativeBounds.exists_canonicalRaw_sequentialEquilibrium nativeRuntime nativeLeaks
      nativeInitialLaw nativeHorizon nativeScheduler effective
        (fun who state => utility state who) fullSE
  refine ⟨raw, ?_, ?_⟩
  · simpa only [utilityInvariant] using rawSE
  · have observationLaw := congrArg (FinDist.map (fun state => (observe state, utility state)))
      projected
    simp only [FinDist.map_comp, Function.comp_def, observationInvariant, utilityInvariant]
      at observationLaw
    rw [observationLaw, ← executionLaw, FinDist.map_comp]
    rfl

end Vegas.Examples.MonitoredGuessing.Restricted
