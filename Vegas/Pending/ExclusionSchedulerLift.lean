/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionPrefix

/-! # Recovery schedulers from native environment histories

The lifted scheduler reads projected actual histories and views. Its native
projection is the original scheduler for every native input.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- Run a native scheduler on the projected recovery environment transcript. -/
def liftScheduler (scheduler : (runtime.reactiveApplication leaks).Scheduler) :
    (runtime.recoveryApplication leaks).Scheduler := fun past view =>
  (scheduler (past.map (environmentEntry runtime leaks))
    (environmentView runtime leaks view)).map (liftCommand runtime leaks)

/-- Lifting a scheduler and then projecting its clear inputs is exact. -/
theorem nativeScheduler_liftScheduler
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) :
    nativeScheduler runtime leaks (liftScheduler runtime leaks scheduler) = scheduler := by
  funext past view
  simp only [nativeScheduler, liftScheduler, List.map_map, Function.comp_def,
    environmentEntry_liftEnvironmentEntry, environmentView_liftEnvironmentView,
    List.map_id_fun', id_eq, PMF.map_comp, command_liftCommand]
  exact PMF.map_id _

end Vegas.EventGraphRuntime.RecoveryProjection
