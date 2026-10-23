/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.CommitTimingInformationService
import GameTheory.Math.Probability.Joint
import GameTheory.Math.Probability.Product
import GameTheoryExtensions.Math.Probability.Uniform
import Interaction.ReactiveSchedulerRelabel

/-! # Independent service randomness for private timing information

Only Alice's original coordinate has random service. The two-bit native
service is exactly the projection of a full independently addressed seed law,
including its posterior at every recorded environment history.
-/

noncomputable section

namespace Vegas.Examples.CommitTimingInformation

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability

/-- The initial service poll is good with probability nine tenths. -/
def goodPollLaw : PMF Bool :=
  mix (9 / 10) (by norm_num) (by norm_num) (PMF.pure true) (PMF.pure false)

/-- The final opportunity fails with the declared positive probability. -/
def finalPollLaw (failure : Set.Ioo (0 : ℝ) 1) : PMF Bool :=
  mix failure.1 failure.2.1.le failure.2.2.le (PMF.pure false) (PMF.pure true)

/-- The final admission coin is independent of the early poll placement. -/
def seedLaw (failure : Set.Ioo (0 : ℝ) 1) : PMF Seeds :=
  bindPairLaw goodPollLaw fun _ => finalPollLaw failure

theorem seedLaw_good_marginal (failure : Set.Ioo (0 : ℝ) 1) :
    (seedLaw failure).map Prod.fst = goodPollLaw :=
  bindPairLaw_map_fst goodPollLaw fun _ => finalPollLaw failure

theorem seedLaw_final_marginal (failure : Set.Ioo (0 : ℝ) 1) :
    (seedLaw failure).map Prod.snd = finalPollLaw failure := by
  rw [seedLaw, bindPairLaw_map_snd, PMF.bind_const]

theorem seedLaw_apply (failure : Set.Ioo (0 : ℝ) 1) (good final : Bool) :
    seedLaw failure (good, final) = goodPollLaw good * finalPollLaw failure final :=
  bindPairLaw_apply goodPollLaw (fun _ => finalPollLaw failure) good final

/-- The actual native scheduler retains its original two-bit prior. -/
def implementation (failure : Set.Ioo (0 : ℝ) 1) :=
  app.schedulerMixture (seedLaw failure) family

def scheduler (failure : Set.Ioo (0 : ℝ) 1) : app.Scheduler :=
  (implementation failure).scheduler

abbrev AddressedSeeds := Unit × (PhaseSeedAddress graph → Seeds)

open Classical in
/-- All other physical coordinates use the deterministic protected service. -/
def addressedSeedLaws (failure : Set.Ioo (0 : ℝ) 1)
    (address : PhaseSeedAddress graph) : PMF Seeds :=
  if address = originalAddress alice then seedLaw failure else PMF.pure (false, false)

def addressedSeedLaw (failure : Set.Ioo (0 : ℝ) 1) : PMF AddressedSeeds :=
  (independentProduct (addressedSeedLaws failure)).map fun draws => ((), draws)

def addressedSeedCore (seed : AddressedSeeds) : Seeds :=
  seed.2 (originalAddress alice)

theorem addressedSeedLaw_map_core (failure : Set.Ioo (0 : ℝ) 1) :
    (addressedSeedLaw failure).map addressedSeedCore = seedLaw failure := by
  classical
  rw [addressedSeedLaw, PMF.map_comp]
  change (independentProduct (addressedSeedLaws failure)).map
    (fun draws => draws (originalAddress alice)) = _
  rw [independentProduct_map_eval]
  exact ite_eq_left rfl

def addressedFamily (seed : AddressedSeeds) : app.Scheduler :=
  family (addressedSeedCore seed)

def addressedImplementation (failure : Set.Ioo (0 : ℝ) 1) :=
  app.schedulerMixture (addressedSeedLaw failure) addressedFamily

/-- Full addressed randomness realizes the same scheduler at every history. -/
theorem addressed_scheduler_eq (failure : Set.Ioo (0 : ℝ) 1) :
    (addressedImplementation failure).scheduler = scheduler failure := by
  change (app.schedulerMixture (addressedSeedLaw failure)
    (fun seed => family (addressedSeedCore seed))).scheduler = _
  rw [app.schedulerMixture_scheduler_map, addressedSeedLaw_map_core]
  rfl

/-- Bayes updating keeps that same original seed projection, including at
histories to which the scheduler assigns zero likelihood. -/
theorem addressed_posterior_core (failure : Set.Ioo (0 : ℝ) 1)
    (past : List app.EnvironmentEntry) :
    ((addressedImplementation failure).posterior past).map addressedSeedCore =
      (implementation failure).posterior past := by
  have projected := app.schedulerMixture_posterior_map
    (addressedSeedLaw failure) addressedSeedCore family past
  rw [addressedSeedLaw_map_core] at projected
  exact projected

end Vegas.Examples.CommitTimingInformation
