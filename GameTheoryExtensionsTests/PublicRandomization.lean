/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.PublicRandomization
import GameTheoryExtensions.Math.Probability.Uniform
import GameTheory.Math.Probability.Conditioning
import GameTheoryExtensions.Math.Probability.Expectation

/-! # Public information can be ignored without a conditional product factorization

Both players observe the same fair coin. Compressing each view to a constant
fails the own/opponent-information conditional independence required by USI.
Nevertheless ignoring the coin implements a source mixed Nash equilibrium and
its entire outcome law, against every contingent randomized unilateral choice.
This is a static boundary, not an SE compression theorem.
-/

noncomputable section

namespace GameTheoryExtensionsTests.PublicRandomization

open GameTheory GameTheory.Math.Probability

private def fair : PMF Bool := PMF.uniformOfFintype Bool

private def sharedInformation : PMF (Bool × Bool) := fair.map (fun bit => (bit, bit))

private theorem first_marginal : sharedInformation.map Prod.fst = fair := by
  simp only [sharedInformation, PMF.map_comp]
  exact PMF.map_id fair

private theorem second_marginal : sharedInformation.map Prod.snd = fair := by
  simp only [sharedInformation, PMF.map_comp]
  exact PMF.map_id fair

/-- Conditioning the two full views on their constant compression changes nothing. -/
theorem conditional_information :
    fiberPosterior sharedInformation (fun _ => ()) () = sharedInformation := by
  have reconstructed := fiberPosterior_reconstruct sharedInformation (fun _ => ())
  change (sharedInformation.map (Function.const (Bool × Bool) ())).bind _ = _ at reconstructed
  rw [PMF.map_const, PMF.pure_bind] at reconstructed
  exact reconstructed

/-- The two full views cannot have independent conditional laws given constant
compressed information. This necessary independence component of USI fails. -/
theorem no_conditional_product : ¬ ∃ own other : PMF Bool,
    fiberPosterior sharedInformation (fun _ => ()) () = bindPairLaw own (fun _ => other) := by
  rw [conditional_information]
  rintro ⟨own, other, factor⟩
  have ownLaw := congrArg (PMF.map Prod.fst) factor
  rw [first_marginal, bindPairLaw_map_fst] at ownLaw
  have otherLaw := congrArg (PMF.map Prod.snd) factor
  rw [second_marginal, bindPairLaw_map_snd, PMF.bind_const] at otherLaw
  rw [← ownLaw, ← otherLaw] at factor
  have atom := congrArg (fun law : PMF (Bool × Bool) => (law (false, true)).toReal) factor
  have impossible : sharedInformation (false, true) = 0 := by
    rw [sharedInformation, PMF.map_apply]
    apply ENNReal.tsum_eq_zero.mpr
    intro bit
    cases bit <;> simp
  rw [impossible, ENNReal.toReal_zero, bindPairLaw_apply, ENNReal.toReal_mul] at atom
  norm_num [fair, toReal_uniformOfFintype_apply] at atom

private def source : GameForm Bool where
  sig := ⟨(fun _ => Bool), Bool × Bool⟩
  play profile := PMF.pure (profile false, profile true)

private def value (outcome : Bool × Bool) (who : Bool) : ℝ :=
  if (if who then outcome.2 else outcome.1) then 0 else 1

private def prescribed : Profile source.sig := fun _ => false

private theorem source_nash : IsNash source (euPreference value) prescribed := by
  apply (isNash_iff (F := source) (weaklyPrefers := euPreference value) prescribed).mpr
  intro who alternative
  change euPreference value who (PMF.pure (false, false))
    (PMF.pure (Profile.update prescribed who alternative false,
      Profile.update prescribed who alternative true))
  rw [euPreference_pure_iff]
  cases who <;> cases alternative <;> norm_num [Profile.update, prescribed, value]

/-- A genuine two-player mixed Nash equilibrium is preserved with its whole
outcome law; target strategies range over every public-coin behavioral kernel. -/
theorem ignored_public_coin_nash_and_law :
    IsNash (source.publicRandomization fair) (euPreference value)
      (source.ignorePublicSignal fair (source.purify prescribed)) ∧
    (source.publicRandomization fair).play
        (source.ignorePublicSignal fair (source.purify prescribed)) = PMF.pure (false, false) := by
  let : ∀ who, Finite (source.sig.Strategy who) := fun _ => inferInstanceAs (Finite Bool)
  have mixed : IsNash source.mixed (euPreference value) (source.purify prescribed) :=
    source_nash.purify_of_finite (fun _ _ => payoffIntegrable_pure _ _)
  constructor
  · exact (source.isNash_ignorePublicSignal_iff fair (euPreference value)
      (source.purify prescribed)).mpr mixed
  · rw [source.play_ignorePublicSignal, GameForm.mixed_play_purify]
    rfl

end GameTheoryExtensionsTests.PublicRandomization

/-- info: 'GameTheoryExtensionsTests.PublicRandomization.conditional_information' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheoryExtensionsTests.PublicRandomization in
#print axioms conditional_information

/-- info: 'GameTheoryExtensionsTests.PublicRandomization.no_conditional_product' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheoryExtensionsTests.PublicRandomization in
#print axioms no_conditional_product

/-- info: 'GameTheoryExtensionsTests.PublicRandomization.ignored_public_coin_nash_and_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheoryExtensionsTests.PublicRandomization in
#print axioms ignored_public_coin_nash_and_law
