/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastCallbackReplay
import Vegas.Examples.CommitSeedBroadcastSeedIndependence

/-! # Original-seed bounds at the actual initialized quiet first-late input

The behavioral likelihood below is derived from the native callback replay.
It retains the full input, rather than conditioning on the hidden split or
on an environment command index. Assessment occupation transport is separate.
-/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

abbrev FirstLateInformation := Option (List app.PlayerEntry × app.PlayerView)

def firstLateLikelihood (players : Player → app.Policy) (owner : Player)
    (input : FirstLateInformation) (order : List Player) : ℝ :=
  (((physicalCallbacks players order quietStart).map (firstLateInput owner)) input).toReal

theorem firstLateLikelihood_nonnegative (players : Player → app.Policy) (owner : Player)
    (input : FirstLateInformation) (order : List Player) :
    0 ≤ firstLateLikelihood players owner input order := ENNReal.toReal_nonneg

def quietFirstLateMass (players : Player → app.Policy) (owner : Player)
    (input : FirstLateInformation) (seed : Seeds) : ℝ :=
  (((app.runRounds (family seed) players 14 initialExecution).map
    (firstLateInput owner)) input).toReal

/-- Every likelihood is the literal initialized native input mass under the
same original seed. The partition is a conclusion of callback replay. -/
theorem quietFirstLateMass_eq (players : Player → app.Policy)
    (waited : ∀ owner, players owner ((initialCallback owner).recall owner)
      ((initialCallback owner).observe app owner) = PMF.pure ⟨none⟩)
    (owner : Player) (input : FirstLateInformation) (seed : Seeds) :
    quietFirstLateMass players owner input seed =
      firstLateLikelihood players owner input (nativePartitionedOrder seed) := by
  unfold quietFirstLateMass firstLateLikelihood
  rw [initialized_quiet_first_late_input_kernel seed players waited owner]

/-- The bad-seed bound applies to every complete initialized quiet input,
including arbitrarily small positive input masses. -/
theorem quiet_firstLate_bad_mass_le (players : Player → app.Policy)
    (waited : ∀ owner, players owner ((initialCallback owner).recall owner)
      ((initialCallback owner).observe app owner) = PMF.pure ⟨none⟩)
    (owner : Player) (input : FirstLateInformation) :
    expect nativeSeedLaw (fun seed => if seed.2 owner = false then
      quietFirstLateMass players owner input seed else 0) ≤
      (271 / 1000 : ℝ) * expect nativeSeedLaw (quietFirstLateMass players owner input) := by
  have mass := funext (quietFirstLateMass_eq players waited owner input)
  rw [mass]
  exact nativeSeedLaw_bad_likelihood_le owner (firstLateLikelihood players owner input)
    (firstLateLikelihood_nonnegative players owner input)

/-- The same actual input retains the positive all-good chance needed for a
strict usable-preparation comparison. It is not a newly chosen posterior. -/
theorem quiet_firstLate_all_good_mass (players : Player → app.Policy)
    (waited : ∀ owner, players owner ((initialCallback owner).recall owner)
      ((initialCallback owner).observe app owner) = PMF.pure ⟨none⟩)
    (owner : Player) (input : FirstLateInformation) :
    expect nativeSeedLaw (fun seed => if nativeGoodCount seed = 3 then
      quietFirstLateMass players owner input seed else 0) =
      (729 / 1000 : ℝ) * expect nativeSeedLaw (quietFirstLateMass players owner input) := by
  have mass := funext (quietFirstLateMass_eq players waited owner input)
  rw [mass]
  exact nativeSeedLaw_all_good_likelihood (firstLateLikelihood players owner input)

theorem quiet_firstLate_bad_conditional_le (players : Player → app.Policy)
    (waited : ∀ owner, players owner ((initialCallback owner).recall owner)
      ((initialCallback owner).observe app owner) = PMF.pure ⟨none⟩)
    (owner : Player) (input : FirstLateInformation)
    (positive : 0 < expect nativeSeedLaw (quietFirstLateMass players owner input)) :
    expect nativeSeedLaw (fun seed => if seed.2 owner = false then
      quietFirstLateMass players owner input seed else 0) /
      expect nativeSeedLaw (quietFirstLateMass players owner input) ≤ (271 / 1000 : ℝ) :=
  (div_le_iff₀ positive).mpr (quiet_firstLate_bad_mass_le players waited owner input)

end Vegas.Examples.CommitSeedBroadcast
