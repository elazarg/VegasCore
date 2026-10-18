/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastRuntime
import Vegas.Examples.CommitSeedBroadcastSeedIndependence
import Interaction.ReactiveSchedulerRelabel
import GameTheory.Math.Probability.Product

/-! # The same original scheduler as a full independently addressed seed law -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

/-- The original binding's location in the full service seed vector. -/
def originalAddress (owner : Player) : PhaseSeedAddress graph :=
  ⟨originalCoordinate owner, by
    constructor
    · change 0 < 6
      decide
    · change 0 ≤ 3
      decide⟩

theorem originalAddress_injective : Function.Injective originalAddress := by
  intro first second same
  have events := congrArg (fun address : PhaseSeedAddress graph => address.1.event.val) same
  exact Fin.ext events

open Classical in
/-- Each original binding has its original biased coin; every other service
coordinate has the fixed protected-service seed. -/
def addressedSeedLaws (address : PhaseSeedAddress graph) : PMF Bool :=
  if ∃ owner, address = originalAddress owner then timingCoin else PMF.pure false

theorem addressedSeedLaws_original (owner : Player) :
    addressedSeedLaws (originalAddress owner) = timingCoin := by
  unfold addressedSeedLaws
  exact ite_eq_left ⟨owner, rfl⟩

theorem addressedSeedLaws_other (address : PhaseSeedAddress graph)
    (other : ∀ owner, address ≠ originalAddress owner) :
    addressedSeedLaws address = PMF.pure false := by
  unfold addressedSeedLaws
  exact ite_eq_right (not_exists.mpr other)

abbrev AddressedSeeds := (Equiv.Perm Player) × (PhaseSeedAddress graph → Bool)

/-- The full vector and the remainder permutation are initialized independently. -/
def addressedSeedLaw : PMF AddressedSeeds :=
  bindPairLaw remainderOrderLaw fun _ => independentProduct addressedSeedLaws

def addressedSeedCore (seed : AddressedSeeds) : Seeds :=
  (seed.1, fun owner => seed.2 (originalAddress owner))

theorem addressed_original_vector :
    (independentProduct addressedSeedLaws).map
      (fun draws owner => draws (originalAddress owner)) =
        independentProduct (fun _ : Player => timingCoin) := by
  let embedding : Player ↪ PhaseSeedAddress graph :=
    ⟨originalAddress, originalAddress_injective⟩
  have projected := independentProduct_map_embedding embedding addressedSeedLaws
  change (independentProduct addressedSeedLaws).map
    (fun draws owner => draws (originalAddress owner)) =
      independentProduct (fun owner => addressedSeedLaws (originalAddress owner)) at projected
  simpa only [addressedSeedLaws_original] using projected

/-- This is equality with the already installed original chance kernel. -/
theorem addressedSeedLaw_map_core : addressedSeedLaw.map addressedSeedCore = nativeSeedLaw := by
  rw [nativeSeedLaw_independent]
  unfold addressedSeedLaw bindPairLaw
  rw [PMF.map_bind]
  apply congrArg (fun kernel => remainderOrderLaw.bind kernel)
  funext order
  rw [PMF.map_comp]
  change (independentProduct addressedSeedLaws).map
    (fun draws => (order, fun owner => draws (originalAddress owner))) = _
  rw [← addressed_original_vector, PMF.map_comp]
  rfl

def addressedFamily (seed : AddressedSeeds) : app.Scheduler := family (addressedSeedCore seed)

def addressedImplementation := app.schedulerMixture addressedSeedLaw addressedFamily

/-- Full addressed memory realizes precisely the existing native scheduler,
including its behavior after every impossible transcript. -/
theorem addressed_scheduler_eq : addressedImplementation.scheduler = scheduler := by
  change (app.schedulerMixture addressedSeedLaw
    (fun seed => family (addressedSeedCore seed))).scheduler = _
  rw [app.schedulerMixture_scheduler_map, addressedSeedLaw_map_core]
  rfl

/-- The complete updated address vector projects to the original core
posterior; all unused protected-service coordinates remain represented. -/
theorem addressed_posterior_core (past : List app.EnvironmentEntry) :
    (addressedImplementation.posterior past).map addressedSeedCore =
      implementation.posterior past := by
  have projected := app.schedulerMixture_posterior_map addressedSeedLaw addressedSeedCore
    family past
  rw [addressedSeedLaw_map_core] at projected
  exact projected

end Vegas.Examples.CommitSeedBroadcast
