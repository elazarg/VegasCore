/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

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

variable [DecidableEq Principal]

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
