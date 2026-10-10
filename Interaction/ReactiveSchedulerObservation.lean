/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRounds

/-! # Scheduler laws implemented through restricted observations

The runtime exposes a complete public network view to a scheduler. A backend
with less visibility can implement a particular scheduler when its command law
factors through the backend's observation. This is a law equality, so the
adapter preserves execution probabilities for arbitrary player policies.
Restricting scheduler support alone does not supply this certificate.
-/

namespace Interaction.ReactiveApplication

variable {Principal : Type} (app : ReactiveApplication Principal)

/-- Implement a scheduler using only the observation supplied by a backend. -/
def Scheduler.ofObservation {Observation : Type}
    (observe : List app.EnvironmentEntry → app.EnvironmentView → Observation)
    (choose : Observation → PMF app.Command) : app.Scheduler :=
  fun past view => choose (observe past view)

/-- Equal backend observations give equal command laws, even when the full
network views and command recalls differ. -/
theorem Scheduler.ofObservation_eq_of_observation_eq {Observation : Type}
    (observe : List app.EnvironmentEntry → app.EnvironmentView → Observation)
    (choose : Observation → PMF app.Command)
    {firstPast secondPast : List app.EnvironmentEntry}
    {firstView secondView : app.EnvironmentView}
    (same : observe firstPast firstView = observe secondPast secondView) :
    Scheduler.ofObservation app observe choose firstPast firstView =
      Scheduler.ofObservation app observe choose secondPast secondView :=
  congrArg choose same

/-- A backend observation factorization implements the original scheduler
exactly, rather than merely preserving its possible commands. -/
theorem Scheduler.eq_of_factorization {Observation : Type}
    (scheduler : app.Scheduler)
    (observe : List app.EnvironmentEntry → app.EnvironmentView → Observation)
    (choose : Observation → PMF app.Command)
    (factors : ∀ past view, scheduler past view = choose (observe past view)) :
    scheduler = Scheduler.ofObservation app observe choose := by
  funext past view
  exact factors past view

/-- Observation-based implementation preserves the complete execution law
at every finite horizon and against every raw player policy profile. -/
theorem runRounds_eq_of_scheduler_factorization [DecidableEq Principal]
    {Observation : Type} (scheduler : app.Scheduler)
    (observe : List app.EnvironmentEntry → app.EnvironmentView → Observation)
    (choose : Observation → PMF app.Command)
    (factors : ∀ past view, scheduler past view = choose (observe past view))
    (players : Principal → app.Policy) (count : Nat) (execution : app.Execution) :
    app.runRounds scheduler players count execution =
      app.runRounds (Scheduler.ofObservation app observe choose) players count execution := by
  rw [Scheduler.eq_of_factorization app scheduler observe choose factors]

end Interaction.ReactiveApplication
