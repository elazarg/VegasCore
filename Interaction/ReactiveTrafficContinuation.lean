/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveTrafficState

/-! # Traffic evidence through actual runtime continuations

The physical round evaluator and the canonical history evaluator preserve the
same traffic records. These results allow arbitrary responses and schedulers;
neither conformance nor eventual acceptance of an envelope is required.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

theorem stateTraffic_reaches (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler)
    {first last : (app.protocol initial horizon scheduler).History} {fuel : Nat}
    (path : (app.protocol initial horizon scheduler).ReachesWithin fuel first last) :
    app.stateTraffic first.state <+: app.stateTraffic last.state := by
  rw [← app.trafficAudit_eq_stateTraffic initial horizon scheduler first.trace,
    ← app.trafficAudit_eq_stateTraffic initial horizon scheduler last.trace]
  exact app.trafficAudit_reaches initial horizon scheduler path

end Interaction.ReactiveApplication
