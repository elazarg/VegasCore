/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAddressedPosterior
import GameTheoryExtensions.Math.Probability.ProductMixture

/-! # A recovered coordinate constraint in the original addressed posterior -/

noncomputable section

namespace Interaction.ReactiveApplication.AddressedScheduler

open GameTheory.Math.Probability

variable {Principal Address LocalSeed RestSeed Query : Type}
  [Fintype Address] [DecidableEq Address] {app : ReactiveApplication Principal}
  (controller : AddressedScheduler app Address LocalSeed RestSeed Query)

local notation "AllSeed" =>
  CoordinateSeed (LocalSeed := LocalSeed) (RestSeed := RestSeed) (Address := Address)

omit [DecidableEq Address] in
/-- If the actual deterministic constraint for one coordinate is recovered for
all candidate seeds and compatible remainder values, its ORIGINAL filtered law
factors from all remaining coordinates. No independence inside the remainder
posterior is asserted or required. -/
theorem posterior_splitAt_of_coordinate_constraint
    (laws : Address → PMF LocalSeed) (restLaw : PMF RestSeed) (selected : Address)
    (past : List app.EnvironmentEntry) (event : Set LocalSeed)
    (positive : ∃ values ∈ {values : (index : Option Address) → AllSeed index |
      app.commandConsistentFrom (fun values => controller.choose (unpack values)) values [] past},
        values ∈ (independentProduct (coordinateLaws laws restLaw)).support)
    (recovered : ∀ rest, (∃ values ∈
      {values : (index : Option Address) → AllSeed index |
        app.commandConsistentFrom (fun values => controller.choose (unpack values)) values [] past ∧
          values none = rest},
        values ∈ (independentProduct (coordinateLaws laws restLaw)).support) →
      ∀ candidate, controller.coordinateConsistentFrom rest selected candidate [] past ↔
        candidate ∈ event) :
    ∃ (localPositive : ∃ seed ∈ event, seed ∈ (laws selected).support)
      (residual : PMF ((index : {index : Option Address // index ≠ some selected}) →
        AllSeed index)),
      (((controller.coordinateImplementation laws restLaw).posterior past).map fun values =>
        (values (some selected),
          fun index : {index : Option Address // index ≠ some selected} => values index)) =
        ((laws selected).filter event localPositive).bind fun value =>
          residual.map (Prod.mk value) := by
  classical
  let prior := independentProduct (coordinateLaws laws restLaw)
  let current := (controller.coordinateImplementation laws restLaw).posterior past
  let restriction := controller.coordinateRestriction
  have currentEq : current = prior.filter
      {values | app.commandConsistentFrom (fun values => controller.choose (unpack values))
        values [] past} positive := by
    exact app.schedulerMixture_posterior_eq_filter prior
      (fun values => controller.choose (unpack values)) past positive
  let restPosterior := current.map fun values => values none
  have compatibleRest : ∀ rest ∈ restPosterior.support, ∃ values ∈
      {values : (index : Option Address) → AllSeed index |
        app.commandConsistentFrom (fun values => controller.choose (unpack values)) values [] past ∧
          values none = rest}, values ∈ prior.support := by
    intro rest supported
    obtain ⟨values, present, restEq⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    rw [currentEq] at present
    obtain ⟨compatible, initial⟩ := (PMF.mem_support_filter_iff positive).mp present
    exact ⟨values, ⟨compatible, restEq⟩, initial⟩
  obtain ⟨witness, compatible, supported⟩ := positive
  have positiveRest : ∃ values ∈
      {values : (index : Option Address) → AllSeed index |
        app.commandConsistentFrom (fun values => controller.choose (unpack values)) values [] past ∧
          values none = witness none}, values ∈ prior.support :=
    ⟨witness, ⟨compatible, rfl⟩, supported⟩
  have commands : app.commandConsistentFrom controller.choose (unpack witness) [] past := by
    simpa only [Set.mem_ofPred_eq, app.commandConsistentFrom_comp] using compatible
  have coordinate := ((controller.command_rectangle (witness none)
    (fun address => witness (some address)) [] past).mp commands).2 selected
  have localPositive : ∃ seed ∈ event, seed ∈ (laws selected).support := by
    refine ⟨witness (some selected), (recovered (witness none) positiveRest _).mp coordinate, ?_⟩
    exact (independentProduct_support_iff (coordinateLaws laws restLaw) witness).mp supported
      (some selected)
  let factors := fun rest (index : Option Address) =>
    if present : ∃ seed ∈ restriction rest past index,
        seed ∈ (coordinateLaws laws restLaw index).support then
      (coordinateLaws laws restLaw index).filter (restriction rest past index) present
    else coordinateLaws laws restLaw index
  have products : ∀ rest ∈ restPosterior.support,
      fiberPosterior current (fun values => values none) rest =
        independentProduct (factors rest) := by
    intro rest supported
    obtain ⟨coordinates, product⟩ := controller.posterior_given_remainder laws restLaw past rest
      (compatibleRest rest supported)
    rw [product]
    congr 1
    funext index
    exact (dite_eq_left (coordinates index)).symm
  have common : ∀ rest ∈ restPosterior.support,
      factors rest (some selected) = (laws selected).filter event localPositive := by
    intro rest supported
    obtain ⟨coordinates, _⟩ := controller.posterior_given_remainder laws restLaw past rest
      (compatibleRest rest supported)
    have same : restriction rest past (some selected) = event :=
      Set.ext fun seed => recovered rest (compatibleRest rest supported) seed
    dsimp only [factors]
    rw [dite_eq_left (coordinates (some selected))]
    change (laws selected).filter (restriction rest past (some selected)) _ = _
    congr 1
  let residual := restPosterior.bind fun rest =>
    independentProduct (fun index : {index : Option Address // index ≠ some selected} =>
      factors rest index)
  have tagged := tagged_product_mixture_splitAt restPosterior factors (some selected)
    ((laws selected).filter event localPositive) common
  have projected := congrArg (PMF.map fun result :
      LocalSeed × (RestSeed × ((index : {index : Option Address // index ≠ some selected}) →
        AllSeed index)) => (result.1, result.2.2)) tagged
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at projected
  refine ⟨localPositive, residual, ?_⟩
  calc
    _ = restPosterior.bind (fun rest =>
        (fiberPosterior current (fun values => values none) rest).map fun values =>
          (values (some selected),
            fun index : {index : Option Address // index ≠ some selected} => values index)) := by
      rw [← PMF.map_bind, fiberPosterior_reconstruct]
    _ = restPosterior.bind (fun rest => (independentProduct (factors rest)).map fun values =>
        (values (some selected),
          fun index : {index : Option Address // index ≠ some selected} => values index)) := by
      apply bind_congr_on_support _
      intro rest supported
      rw [products rest supported]
    _ = _ := by
      dsimp only [CoordinateSeed] at projected ⊢
      simp only [residual, PMF.map_bind]
      convert projected using 1
      rfl

end Interaction.ReactiveApplication.AddressedScheduler
