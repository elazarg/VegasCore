/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.SchedulerPredraw
import Vegas.EventGraph.SchedulerDeviation
import Vegas.EventGraph.CanonicalNormalization
import GameTheoryExtensions.Math.Probability.Support

/-! # Setup-wide asynchronous deviation simulation

Public scheduler randomness is drawn before private setup, then replayed by
the focal policy. Unchanged opponents use their order-normalized policies.
The conclusion preserves the terminal typed-store law, not the visible order.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- An arbitrary unilateral asynchronous deviation has a finite mixture of
canonical deviations against the original opponents. The mixture
is independent of the realized private setup. -/
theorem BarrierOrdered.exists_deviation_mixture
    (ordered : graph.BarrierOrdered) (finite : graph.FiniteActions)
    (inputs : PMF graph.Inputs) (finiteInputs : inputs.support.Finite)
    (scheduler : graph.PublicScheduler) (profile : graph.BehavioralProfile)
    (who : Player) (replacement : graph.BehavioralPolicy who) :
    ∃ mixture : PMF (graph.BehavioralPolicy who), mixture.support.Finite ∧
      (inputs.bind fun initial =>
        graph.runPolicies scheduler
          (Profile.update (sig := graph.gameSignature)
            (graph.normalizeProfile profile) who replacement) initial).map Config.store =
        mixture.bind fun alternative =>
          (inputs.bind fun initial =>
            graph.runPolicies graph.canonicalScheduler
              (Profile.update (sig := graph.gameSignature)
                profile who alternative) initial).map Config.store := by
  obtain ⟨schedulers, finiteSchedulers, law⟩ := graph.exists_scheduler_mixture
    (Profile.update (sig := graph.gameSignature)
      (graph.normalizeProfile profile) who replacement) inputs scheduler finiteInputs
    (finite.profileFiniteSupport _)
  refine ⟨schedulers.map (fun fixed => graph.replayPolicy fixed who replacement), ?_, ?_⟩
  · rw [PMF.support_map]
    exact finiteSchedulers.image _
  rw [← law, PMF.map_bind, PMF.bind_map, Function.comp_def]
  apply bind_congr_on_support _
  intro fixed _
  rw [PMF.map_bind, PMF.map_bind]
  apply bind_congr_on_support _
  intro initial _
  rw [ordered.runPolicies_update_store_eq_canonical fixed profile who replacement initial,
    graph.runPolicies_canonical_normalize_eq
      (Profile.update (sig := graph.gameSignature) profile who
        (graph.replayPolicy fixed who replacement)) initial,
    normalizeProfile_update, normalizePolicy_replayPolicy]

end Vegas.EventGraph
