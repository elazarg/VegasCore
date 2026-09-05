/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Scheduled.Replay

noncomputable section

namespace VegasTests.ScheduledReplay

open Vegas GameTheory.Protocol

/-- The running total is visible to the scheduler, just as it is to players. -/
@[reducible] def publicCounter : ScheduledSystem (Fin 2) :=
  { Vegas.counterSystem with
    SchedulerView := Nat
    schedulerView := id
    schedules := fun _ => {[0, 1], [1, 0]}
    schedules_nonempty := fun _ => ⟨[0, 1], Set.mem_insert _ _⟩ }

/-- An executing policy whose order changes with observed public data. -/
def dataDependentScheduler : publicCounter.revealingInformation.Policy .scheduler :=
  fun info =>
    if info.current = 0 then
      ⟨some [0, 1], [0, 1], Set.mem_insert _ _, rfl⟩
    else
      ⟨some [1, 0], [1, 0], Set.mem_insert_of_mem _ rfl, rfl⟩

/-- The two orders are computed at their respective historical public
observations; neither is supplied to the replay as input. -/
example : publicCounter.replayOrderPast dataDependentScheduler (i := 0) id [1, 0] =
    [([1, 0], 1), ([0, 1], 0)] := by
  rfl

example : publicCounter.replayOrderPast dataDependentScheduler (i := 0) id [0, 1] =
    [([0, 1], 0), ([1, 0], 1)] := by
  rfl

/-- Replay is an actual law theorem for this data-dependent scheduler and
arbitrary randomized, order-aware players, for any number of rounds. -/
example
    (profile : (who : Participant (Fin 2)) →
      publicCounter.revealingInformation.BehavioralPolicy who) (fuel : Nat) :
    publicCounter.revealingInformation.runBehavioral
        (publicCounter.fixScheduler dataDependentScheduler profile) fuel =
      publicCounter.revealingInformation.runBehavioral
        (publicCounter.replayBehavioralProfile dataDependentScheduler (fun _ => id) profile)
          fuel :=
  publicCounter.runBehavioral_replay dataDependentScheduler (fun _ => id)
    (fun _ _ => rfl) (publicCounter.fixScheduler dataDependentScheduler profile) rfl fuel

/-- Honest order-blind opponents remain the same policies, not policies
chosen in response to a particular deviator or hidden state. -/
example (who : Fin 2)
    (policy : publicCounter.blindInformation.BehavioralPolicy (.player who)) :
    publicCounter.backtranslatePlayerBehavioralPolicy dataDependentScheduler id
        (publicCounter.liftBehavioralPolicy policy) = policy :=
  publicCounter.backtranslatePlayerBehavioralPolicy_lift dataDependentScheduler id policy

end VegasTests.ScheduledReplay
