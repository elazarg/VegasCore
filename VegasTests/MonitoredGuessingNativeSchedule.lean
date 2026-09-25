/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingNativePrelude
import Vegas.Pending.ReactiveServiceCompletion

/-! # Exact calendar evaluation for the monitored native game -/

noncomputable section

namespace VegasTests.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

theorem native_segment_rounds (players : Player → nativeApp.Policy)
    (before rest after : List (ServiceInstruction nativeGraph))
    (split : nativePlan = before ++ rest ++ after) (execution : nativeApp.Execution)
    (position : execution.environmentRecall.length = before.length) :
    nativeApp.runRounds nativeScheduler players rest.length execution =
      nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork rest execution := by
  induction rest generalizing before execution with
  | nil => rfl
  | cons instruction rest ih =>
      have selected : nativePlan[before.length]? = some instruction := by
        rw [split, List.append_assoc, List.getElem?_append_right (by omega), Nat.sub_self]
        rfl
      have step : nativeApp.round nativeScheduler players execution =
          nativeRuntime.interactionStep nativeLeaks players nativeNetwork instruction
            execution := by
        simp only [ReactiveApplication.round, nativeScheduler, position, selected,
          interactionStep]
      rw [List.length_cons, ReactiveApplication.runRounds, step, runInteractionPlan]
      apply FinDist.bind_congr
      intro next supported
      apply ih (before ++ [instruction])
      · simpa only [List.append_assoc, List.singleton_append] using split
      · have advanced := nativeRuntime.interactionStep_recall nativeLeaks players
          nativeNetwork instruction execution next supported
        simp only [List.length_append, List.length_singleton]
        omega

theorem native_finish_response (players : Player → nativeApp.Policy)
    (before rest : List (ServiceInstruction nativeGraph)) (who : Player)
    (split : nativePlan = before ++ .player who :: rest) (execution : nativeApp.Execution)
    (position : execution.environmentRecall.length = before.length + 1) :
    nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler players
        (some ⟨rest.length, some who, execution⟩) =
      (players who (execution.recall who) (execution.observe nativeApp who)).bind
        (fun response =>
          (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork rest
            (execution.respond nativeApp who response)).map nativeApp.finished) := by
  simp only [ReactiveApplication.finish, ReactiveApplication.resume,
    ReactiveApplication.invoke, FinDist.bind_map, FinDist.map_bind]
  apply FinDist.bind_congr
  intro response _
  congr 1
  apply native_segment_rounds players (before ++ [.player who]) rest []
  · simpa only [List.append_assoc, List.singleton_append, List.append_nil] using split
  · simpa only [ReactiveApplication.respond_environmentRecall,
      List.length_append, List.length_singleton] using position

theorem native_finish_initial (players : Player → nativeApp.Policy) :
    nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler players none =
      (FinDist.uniformOfFintype (α := Bool)).bind (fun bit =>
        (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork nativePlan
          (nativeStart bit)).map nativeApp.finished) := by
  simp only [ReactiveApplication.finish, nativeInitialLaw, FinDist.bind_map]
  apply FinDist.bind_congr
  intro bit _
  congr 1
  exact native_segment_rounds players [] nativePlan [] (List.append_nil _).symm
    (nativeStart bit) rfl

end VegasTests.MonitoredGuessing
