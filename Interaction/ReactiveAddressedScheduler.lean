/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveSchedulerImplementation
import GameTheory.Math.Probability.Product

/-! # Immutable independent seeds addressed by actual scheduler history

The request planner sees the remainder seed and actual environment history. A
local reply reads precisely the requested coordinate. Retiring an address or
allocating a fresh one does not resample or modify the original seed vector.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal Address LocalSeed RestSeed Query : Type}
  {app : ReactiveApplication Principal}

/-- A scheduler separates history-dependent address selection from the local
seed reply. The planner cannot inspect any local seed coordinate. -/
structure AddressedScheduler (app : ReactiveApplication Principal)
    (Address LocalSeed RestSeed Query : Type) where
  request : RestSeed → List app.EnvironmentEntry → app.EnvironmentView →
    Option (Address × Query)
  fallback : RestSeed → List app.EnvironmentEntry → app.EnvironmentView → app.Command
  reply : Address → LocalSeed → Query → app.Command

namespace AddressedScheduler

variable (controller : AddressedScheduler app Address LocalSeed RestSeed Query)

/-- All local seeds are sampled once, independently of the remainder. -/
def prior [Fintype Address] (laws : Address → PMF LocalSeed) (restLaw : PMF RestSeed) :
    PMF (RestSeed × (Address → LocalSeed)) :=
  restLaw.bind fun rest => (independentProduct laws).map (Prod.mk rest)

/-- Exactly one addressed seed is read when the planner requests a local reply. -/
def choose (seeds : RestSeed × (Address → LocalSeed))
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) : app.Command :=
  match controller.request seeds.1 past view with
  | none => controller.fallback seeds.1 past view
  | some (address, query) => controller.reply address (seeds.2 address) query

def family (seeds : RestSeed × (Address → LocalSeed)) : app.Scheduler :=
  fun past view => PMF.pure (controller.choose seeds past view)

def implementation [Fintype Address] (laws : Address → PMF LocalSeed)
    (restLaw : PMF RestSeed) : app.SchedulerImplementation
      (RestSeed × (Address → LocalSeed)) :=
  app.schedulerMixture (prior laws restLaw) controller.family

/-- Changing a seed that is not requested leaves the actual next command equal. -/
theorem choose_update_of_not_requested [DecidableEq Address]
    (seeds : RestSeed × (Address → LocalSeed)) (selected : Address) (value : LocalSeed)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (unread : (controller.request seeds.1 past view).map Prod.fst ≠ some selected) :
    controller.choose (seeds.1, Function.update seeds.2 selected value) past view =
      controller.choose seeds past view := by
  cases requested : controller.request seeds.1 past view with
  | none => simp only [choose, requested]
  | some request =>
      have different : request.1 ≠ selected := by
        intro same
        apply unread
        simpa only [requested, Option.map_some] using congrArg some same
      simp only [choose, requested, Function.update_of_ne different]

@[simp]
theorem prior_map_seeds [Fintype Address]
    (laws : Address → PMF LocalSeed) (restLaw : PMF RestSeed) :
    (prior laws restLaw).map Prod.snd = independentProduct laws := by
  simp only [prior, PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_const]
  exact PMF.map_id _

@[simp]
theorem prior_map_coordinate [Fintype Address]
    (laws : Address → PMF LocalSeed) (restLaw : PMF RestSeed) (selected : Address) :
    (prior laws restLaw).map (fun seeds => seeds.2 selected) = laws selected := by
  rw [← independentProduct_map_eval laws selected, ← prior_map_seeds laws restLaw,
    PMF.map_comp]
  rfl

variable [DecidableEq Principal]

/-- Behavioralizing the actual immutable-seed implementation preserves the
joint law of the complete execution and original seed vector. -/
theorem realize_joint [Fintype Address] (laws : Address → PMF LocalSeed)
    (restLaw : PMF RestSeed) (players : Principal → app.Policy)
    (count : Nat) (state : app.State) :
    ((prior laws restLaw).bind fun seeds =>
      (app.runRounds (controller.family seeds) players count
        (Execution.initial app state)).map fun execution => (execution, seeds)) =
      (app.runRounds (controller.implementation laws restLaw).scheduler players count
        (Execution.initial app state)).bind fun execution =>
          ((controller.implementation laws restLaw).posterior
            execution.environmentRecall).map (Prod.mk execution) :=
  app.schedulerMixture_joint (prior laws restLaw) controller.family players count state

/-- This realization keeps the original all-event randomization, including
coordinates of attempts that never become ready. -/
theorem realize [Fintype Address] (laws : Address → PMF LocalSeed)
    (restLaw : PMF RestSeed) (players : Principal → app.Policy)
    (count : Nat) (state : app.State) :
    ((prior laws restLaw).bind fun seeds =>
      app.runRounds (controller.family seeds) players count (Execution.initial app state)) =
      app.runRounds (controller.implementation laws restLaw).scheduler players count
        (Execution.initial app state) :=
  app.schedulerMixture_realize (prior laws restLaw) controller.family players count state

end AddressedScheduler
end Interaction.ReactiveApplication
