/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ServiceTimingCoupling

/-! # Product retention improves actual turn-timing error -/

noncomputable section

namespace VegasTests.ServiceTiming

open Vegas SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}

/-- Two event deferrals of one fifth cost nine twenty-fifths instead of two fifths. -/
example {turns : Nat} (timing : TurnTiming setup turns mode)
    (events : (serviceGraph setup mode).EventId ≃ Fin 2)
    (deferred : ∀ event, timing.deferral event = (1 : ℝ) / 5) :
    timing.deferralError = (9 : ℝ) / 25 ∧
      timing.deferralError < ∑ event, timing.deferral event := by
  have retained := Fintype.prod_equiv events (fun event => 1 - timing.deferral event)
    (fun _ : Fin 2 => 1 - (1 : ℝ) / 5) (fun event => by rw [deferred event])
  have summed := Fintype.sum_equiv events timing.deferral
    (fun _ : Fin 2 => (1 : ℝ) / 5) deferred
  rw [TurnTiming.deferralError, retained, summed]
  norm_num [Fin.prod_univ_two, Fin.sum_univ_two]

end VegasTests.ServiceTiming
