/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.SchedulerPredraw
import Vegas.EventGraph.SchedulerDeviation
import Vegas.EventGraph.CanonicalNormalization

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
    (ordered : graph.BarrierOrdered) (inputs : FinDist graph.Inputs)
    (scheduler : graph.PublicScheduler) (profile : graph.BehavioralProfile)
    (who : Player) (replacement : graph.BehavioralPolicy who) :
    ∃ mixture : FinDist (graph.BehavioralPolicy who),
      (inputs.bind fun initial =>
        graph.runPolicies scheduler
          (Profile.update (sig := graph.gameSignature)
            (graph.normalizeProfile profile) who replacement) initial).map Config.store =
        mixture.bind fun alternative =>
          (inputs.bind fun initial =>
            graph.runPolicies graph.canonicalScheduler
              (Profile.update (sig := graph.gameSignature)
                profile who alternative) initial).map Config.store := by
  obtain ⟨schedulers, law⟩ := graph.exists_scheduler_mixture
    (Profile.update (sig := graph.gameSignature)
      (graph.normalizeProfile profile) who replacement) inputs scheduler
  refine ⟨schedulers.map (fun fixed => graph.replayPolicy fixed who replacement), ?_⟩
  rw [← law, FinDist.map_bind, FinDist.bind_map]
  apply FinDist.bind_congr
  intro fixed _
  rw [FinDist.map_bind, FinDist.map_bind]
  apply FinDist.bind_congr
  intro initial _
  rw [ordered.runPolicies_update_store_eq_canonical fixed profile who replacement initial,
    graph.runPolicies_canonical_normalize_eq
      (Profile.update (sig := graph.gameSignature) profile who
        (graph.replayPolicy fixed who replacement)) initial,
    normalizeProfile_update, normalizePolicy_replayPolicy]

end Vegas.EventGraph
