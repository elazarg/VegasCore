/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAddressedScheduler
import Interaction.ReactiveSchedulerFreshSeed

/-! # A fresh addressed seed retains its original conditional law

Any selected address splits the original all-event randomization into its local
seed and an independent remainder. The concrete request planner discharges the
unread-coordinate premise of the existing private-scheduler theorem.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal Address LocalSeed RestSeed Query : Type}
  {app : ReactiveApplication Principal} [Fintype Address]

namespace AddressedScheduler

variable (controller : AddressedScheduler app Address LocalSeed RestSeed Query)

/-- The remainder retains all other original event seeds and remainder randomness. -/
def SplitSeed (selected : Address) : Bool → Type
  | false => LocalSeed
  | true => RestSeed × ({address : Address // address ≠ selected} → LocalSeed)

local notation "SeedAt" =>
  SplitSeed (LocalSeed := LocalSeed) (RestSeed := RestSeed)

open Classical in
def splitLaws (laws : Address → PMF LocalSeed) (restLaw : PMF RestSeed)
    (selected : Address) : (side : Bool) → PMF (SeedAt selected side)
  | false => laws selected
  | true => restLaw.bind fun rest =>
      (independentProduct (fun address : {address : Address // address ≠ selected} =>
        laws address)).map (Prod.mk rest)

open Classical in
def reassemble (selected : Address)
    (values : (side : Bool) → SeedAt selected side) :
    RestSeed × (Address → LocalSeed) :=
  ((values true).1, (Equiv.piSplitAt selected (fun _ => LocalSeed)).symm
    (values false, (values true).2))

private theorem bool_product_pair {A : Bool → Type} (laws : (side : Bool) → PMF (A side)) :
    (independentProduct laws).map (fun values => (values false, values true)) =
      (laws false).bind fun first => (laws true).map (Prod.mk first) := by
  rw [independentProduct_splitAt laws false, PMF.map_bind]
  apply congrArg ((laws false).bind)
  funext first
  have marginal := independentProduct_map_eval
    (fun side : {side : Bool // side ≠ false} => laws side) ⟨true, by decide⟩
  have mapped := congrArg (fun law => law.map (Prod.mk first)) marginal
  simpa [PMF.map_comp, Function.comp_def] using mapped

/-- Splitting at any potential attempt/event address preserves the complete
original prior, including every unused or retired address. -/
theorem reassemble_prior (laws : Address → PMF LocalSeed) (restLaw : PMF RestSeed)
    (selected : Address) :
    (independentProduct (splitLaws laws restLaw selected)).map (reassemble selected) =
      prior laws restLaw := by
  classical
  let finish := fun pair : LocalSeed ×
      (RestSeed × ({address : Address // address ≠ selected} → LocalSeed)) =>
    (pair.2.1, (Equiv.piSplitAt selected (fun _ => LocalSeed)).symm (pair.1, pair.2.2))
  have split := congrArg (fun law => law.map finish)
    (bool_product_pair (splitLaws laws restLaw selected))
  simp only [PMF.map_comp, Function.comp_def] at split
  change _ = _ at split
  rw [show (fun values => finish (values false, values true)) = reassemble selected from rfl]
    at split
  rw [split]
  simp only [splitLaws, PMF.map_bind, PMF.map_comp, Function.comp_def]
  rw [PMF.bind_comm]
  apply congrArg restLaw.bind
  funext rest
  have original := congrArg (fun law => law.map (Prod.mk rest))
    (independentProduct_splitAt laws selected)
  dsimp only [finish]
  convert original.symm using 1
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  rfl

omit [Fintype Address] in
open Classical in
theorem reassemble_update (selected : Address)
    (values : (side : Bool) → SeedAt selected side)
    (value : LocalSeed) :
    reassemble selected (Function.update values false value) =
      ((reassemble selected values).1,
        Function.update (reassemble selected values).2 selected value) := by
  classical
  apply Prod.ext
  · simp [reassemble]
  · funext address
    by_cases same : address = selected
    · subst address
      simp [reassemble]
    · simp [reassemble, same]

def splitChoose (selected : Address)
    (values : (side : Bool) → SeedAt selected side)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) : app.Command :=
  controller.choose (reassemble selected values) past view

/-- Before the first request for an address, the actual scheduler posterior is
an independent local original law times the updated complete remainder. -/
theorem posterior_before_request (laws : Address → PMF LocalSeed)
    (restLaw : PMF RestSeed) (selected : Address) (past : List app.EnvironmentEntry)
    (notRequested : ∀ (before : List app.EnvironmentEntry) (entry : app.EnvironmentEntry),
      before ++ [entry] <+: past → ∀ rest,
        (controller.request rest before entry.beforeView).map Prod.fst ≠ some selected) :
    ∃ updated : (side : Bool) → PMF (SeedAt selected side),
      (app.schedulerMixture (independentProduct (splitLaws laws restLaw selected))
        (fun values before view => PMF.pure
          (controller.splitChoose selected values before view))).posterior past =
            independentProduct updated ∧ updated false = laws selected := by
  classical
  apply app.schedulerMixture_posterior_unread
  intro before entry recordedPrefix values value
  dsimp only [splitChoose]
  rw [reassemble_update]
  exact controller.choose_update_of_not_requested _ selected value before entry.beforeView
    (notRequested before entry recordedPrefix _)

variable [DecidableEq Principal]

/-- The split implementation and the original all-event implementation induce
exactly the same law on full executions. -/
theorem split_realize (laws : Address → PMF LocalSeed) (restLaw : PMF RestSeed)
    (selected : Address) (players : Principal → app.Policy) (count : Nat) (state : app.State) :
    app.runRounds (app.schedulerMixture (independentProduct (splitLaws laws restLaw selected))
      (fun values => controller.family (reassemble selected values))).scheduler players count
        (Execution.initial app state) =
      app.runRounds (controller.implementation laws restLaw).scheduler players count
        (Execution.initial app state) := by
  rw [← app.schedulerMixture_realize, ← controller.realize]
  rw [← reassemble_prior laws restLaw selected, PMF.bind_map]
  rfl

/-- With no request yet, the actual full-execution law remains independent of
the selected original seed. This includes newly allocated retry addresses. -/
theorem unread_execution (laws : Address → PMF LocalSeed) (restLaw : PMF RestSeed)
    (selected : Address) (players : Principal → app.Policy) (count : Nat) (state : app.State)
    (notRequested : ∀ next ∈ (app.runRounds
      (controller.implementation laws restLaw).scheduler players count
        (Execution.initial app state)).support,
      ∀ (before : List app.EnvironmentEntry) (entry : app.EnvironmentEntry),
        before ++ [entry] <+: next.environmentRecall → ∀ rest,
          (controller.request rest before entry.beforeView).map Prod.fst ≠ some selected) :
    ((prior laws restLaw).bind fun seeds =>
      (app.runRounds (controller.family seeds) players count (Execution.initial app state)).map
        fun next => (next, seeds.2 selected)) =
      (app.runRounds (controller.implementation laws restLaw).scheduler players count
        (Execution.initial app state)).bind fun next => (laws selected).map (Prod.mk next) := by
  classical
  have unread := app.schedulerMixture_unread_execution (splitLaws laws restLaw selected)
    (controller.splitChoose selected) players count state (by
      intro next supported before entry recordedPrefix values value
      have genuine : next ∈ (app.runRounds
          (controller.implementation laws restLaw).scheduler players count
            (Execution.initial app state)).support := by
        change next ∈ (app.runRounds (app.schedulerMixture
          (independentProduct (splitLaws laws restLaw selected))
            (fun values => controller.family (reassemble selected values))).scheduler
              players count (Execution.initial app state)).support at supported
        rwa [controller.split_realize laws restLaw selected] at supported
      dsimp only [splitChoose]
      rw [reassemble_update]
      exact controller.choose_update_of_not_requested _ selected value before entry.beforeView
        (notRequested next genuine before entry recordedPrefix _))
  have coordinate (values : (side : Bool) → SeedAt selected side) :
      (reassemble selected values).2 selected = values false := by simp [reassemble]
  change ((independentProduct (splitLaws laws restLaw selected)).bind fun values =>
    (app.runRounds (controller.family (reassemble selected values)) players count
      (Execution.initial app state)).map fun next => (next, values false)) =
      (app.runRounds (app.schedulerMixture (independentProduct (splitLaws laws restLaw selected))
        (fun values => controller.family (reassemble selected values))).scheduler players count
          (Execution.initial app state)).bind fun next => (laws selected).map (Prod.mk next)
    at unread
  rw [controller.split_realize laws restLaw selected] at unread
  rw [← reassemble_prior laws restLaw selected, PMF.bind_map]
  simpa only [Function.comp_def, coordinate] using unread

end AddressedScheduler
end Interaction.ReactiveApplication
