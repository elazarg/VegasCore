/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.Product

/-! # Disintegration under a restricted observation

A positive restricted mass can identify a posterior directly from its atoms.
When an event and a label have a factored joint law, refining the event by a
selection of labels conditions the label law without changing its posterior
kernel. Positive conditioning is explicit; no identity of arbitrary fallback
posteriors is inferred at a zero-mass observation.
-/

noncomputable section

namespace GameTheory.Math.Probability

open scoped ENNReal

/-- A positive finite restricted mass identifies the actual posterior without
ever choosing a value on a zero conditioning fiber. -/
theorem fiberPosterior_eq_of_scaled_restriction
    {Point : Type*} (law conditional : PMF Point) (observed : Point → Bool)
    (mass : ℝ≥0∞) (positive : mass ≠ 0) (finite : mass ≠ ⊤)
    (restriction : ∀ point, (if observed point then law point else 0) =
      mass * conditional point) :
    true ∈ (law.map observed).support ∧
      fiberPosterior law observed true = conditional := by
  classical
  have normalizer : (law.map observed) true = mass := by
    rw [PMF.map_apply]
    calc
      _ =
          ∑' point, mass * conditional point := by
        apply tsum_congr
        intro point
        convert restriction point using 1
        cases observed point <;> simp
      _ = mass := by rw [ENNReal.tsum_mul_left, conditional.tsum_coe, mul_one]
  have present : true ∈ (law.map observed).support := by
    apply (PMF.mem_support_iff _ _).mpr
    rwa [normalizer]
  refine ⟨present, ?_⟩
  ext point
  rw [fiberPosterior_apply law observed true present, normalizer]
  have indicator : {point | observed point = true}.indicator law point =
      if observed point then law point else 0 := by
    cases selected : observed point <;> simp [Set.indicator, selected]
  rw [indicator, restriction, mul_right_comm mass (conditional point),
    ENNReal.mul_inv_cancel positive finite, one_mul]

open Classical in
/-- A factored restriction identifies both the posterior of the retained event
and its refinement by an observed label. Refinement conditions the original
label law, retaining the same conditional kernel. -/
theorem fiberPosteriors_of_factored_restriction
    {Point Word : Type*} (law : PMF Point) (words : PMF Word)
    (read : Point → Word) (own : Point → Bool) (admitted : Word → Bool)
    (forced : Word → PMF Point) (ownMass : ℝ≥0∞)
    (ownPositive : ownMass ≠ 0) (ownFinite : ownMass ≠ ⊤)
    (foreignPositive : true ∈ (words.map admitted).support)
    (atoms : ∀ word point,
      ownMass * words word * forced word point =
        if own point = true ∧ read point = word then law point else 0) :
    let foreign := words.map (fun word => (word, admitted word))
    true ∈ (law.map (fun point => own point && admitted (read point))).support ∧
      true ∈ (foreign.map Prod.snd).support ∧
      fiberPosterior law (fun point => own point && admitted (read point)) true =
        (fiberPosterior foreign Prod.snd true).bind (fun word => forced word.1) ∧
      true ∈ (law.map own).support ∧
      fiberPosterior law own true = words.bind forced ∧
      (law.map (fun point => own point && admitted (read point))) true =
        ownMass * (words.map admitted) true ∧
      ∀ word point, admitted word = true →
        (ownMass * (words.map admitted) true) *
          (fiberPosterior words admitted true word * forced word point) =
            if own point = true ∧ read point = word then law point else 0 := by
  classical
  intro foreign
  let foreignMass := (words.map admitted) true
  have foreignNonzero : foreignMass ≠ 0 :=
    (PMF.mem_support_iff _ _).mp foreignPositive
  have foreignFinite : foreignMass ≠ ⊤ := PMF.apply_ne_top _ _
  have ownRestriction (point : Point) :
      (if own point then law point else 0) = ownMass * (words.bind forced) point := by
    rw [PMF.bind_apply, ← ENNReal.tsum_mul_left]
    symm
    calc
      (∑' word, ownMass * (words word * forced word point)) =
          ∑' word, if own point = true ∧ read point = word then law point else 0 := by
        apply tsum_congr
        intro word
        exact (mul_assoc ownMass (words word) (forced word point)).symm.trans (atoms word point)
      _ = if own point then law point else 0 := by
        rw [tsum_eq_single (read point)]
        · cases own point <;> simp
        · intro word different
          have distinct : read point ≠ word := Ne.symm different
          simp [distinct]
  have ownPosterior := fiberPosterior_eq_of_scaled_restriction law (words.bind forced) own ownMass
    ownPositive ownFinite ownRestriction
  have conditionalForeign : (fiberPosterior foreign Prod.snd true).bind
      (fun word => forced word.1) = (fiberPosterior words admitted true).bind forced := by
    have mapped := map_fiberPosterior_readout words (fun word => (word, admitted word))
      Prod.snd true foreignPositive
    change (fiberPosterior words admitted true).map (fun word => (word, admitted word)) =
      fiberPosterior foreign Prod.snd true at mapped
    rw [← mapped, PMF.bind_map]
    simp only [Function.comp_def]
  have foreignRestriction (point : Point) :
      foreignMass * ((fiberPosterior words admitted true).bind forced) point =
        ∑' word, if admitted word then words word * forced word point else 0 := by
    rw [PMF.bind_apply, ← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro word
    rw [← mul_assoc]
    change (words.map admitted) true * fiberPosterior words admitted true word *
      forced word point = _
    rw [fiberPosterior_disintegrate words admitted true foreignPositive]
    cases selected : admitted word <;> simp [Set.indicator, selected]
  have ledgerRestriction (point : Point) :
      (if own point && admitted (read point) then law point else 0) =
        (ownMass * foreignMass) *
          ((fiberPosterior words admitted true).bind forced) point := by
    rw [mul_assoc, foreignRestriction, ← ENNReal.tsum_mul_left]
    symm
    calc
      (∑' word, ownMass * (if admitted word then words word * forced word point else 0)) =
          ∑' word, if admitted word then
            if own point = true ∧ read point = word then law point else 0 else 0 := by
        apply tsum_congr
        intro word
        cases selected : admitted word with
        | false => exact mul_zero ownMass
        | true =>
          exact (mul_assoc ownMass (words word) (forced word point)).symm.trans (atoms word point)
      _ = if own point && admitted (read point) then law point else 0 := by
        rw [tsum_eq_single (read point)]
        · cases own point <;> cases admitted (read point) <;> simp
        · intro word different
          have distinct : read point ≠ word := Ne.symm different
          simp [distinct]
  have ledgerPosterior := fiberPosterior_eq_of_scaled_restriction law
    ((fiberPosterior words admitted true).bind forced)
    (fun point => own point && admitted (read point)) (ownMass * foreignMass)
    (mul_ne_zero ownPositive foreignNonzero) (ENNReal.mul_ne_top ownFinite foreignFinite)
    ledgerRestriction
  have ledgerMass : (law.map (fun point => own point && admitted (read point))) true =
      ownMass * foreignMass := by
    rw [PMF.map_apply]
    calc
      _ = ∑' point, (ownMass * foreignMass) *
          ((fiberPosterior words admitted true).bind forced) point := by
        apply tsum_congr
        intro point
        convert ledgerRestriction point using 1
        cases own point <;> cases admitted (read point) <;> simp
      _ = _ := by
        rw [ENNReal.tsum_mul_left,
          ((fiberPosterior words admitted true).bind forced).tsum_coe, mul_one]
  have issuedAtom (word : Word) (point : Point) (issued : admitted word = true) :
      (ownMass * foreignMass) *
        (fiberPosterior words admitted true word * forced word point) =
          if own point = true ∧ read point = word then law point else 0 := by
    calc
      _ = ownMass * (foreignMass * fiberPosterior words admitted true word) *
          forced word point := by ac_rfl
      _ = ownMass * words word * forced word point := by
        rw [show foreignMass = (words.map admitted) true from rfl,
          fiberPosterior_disintegrate words admitted true foreignPositive]
        simp only [Set.indicator, Set.mem_ofPred_eq, issued, ↓reduceIte]
      _ = _ := atoms word point
  refine ⟨ledgerPosterior.1, ?_, ledgerPosterior.2.trans conditionalForeign.symm,
    ownPosterior.1, ownPosterior.2, ledgerMass, issuedAtom⟩
  simpa only [foreign, PMF.map_comp, Function.comp_def] using foreignPositive

/-- Independent coordinates remain independent after observing one coordinate
and replacing it by a fixed value in the complementary readout. -/
theorem independent_observation_complement
    {Player : Type*} [DecidableEq Player] [Fintype Player]
    {Point Owned : Type*} (law : PMF Point) (read : Point → Player → Owned)
    (who : Player) (empty : Owned) (own : Owned → Bool)
    (product : law.map read = independentProduct
      (fun owner => law.map (fun point => read point owner))) :
    let foreign := fun point : Point => fun owner =>
      if owner = who then empty else read point owner
    law.map (fun point => (own (read point who), foreign point)) =
      bindPairLaw (law.map (fun point => own (read point who)))
        (fun _ => law.map foreign) := by
  classical
  intro foreign
  let factors := fun owner => law.map (fun point => read point owner)
  let others := independentProduct (fun owner : {owner : Player // owner ≠ who} =>
    factors owner.val)
  let restore := fun word : (∀ owner : {owner : Player // owner ≠ who}, Owned) =>
    fun owner => if different : owner = who then empty else word ⟨owner, different⟩
  have split : law.map (fun point =>
      (read point who, fun owner : {owner : Player // owner ≠ who} => read point owner.val)) =
        bindPairLaw (factors who) (fun _ => others) := by
    have mapped := congrArg (fun measure => measure.map
      (Equiv.piSplitAt who (fun _ : Player => Owned))) product
    rw [independentProduct_splitAt _ who] at mapped
    simpa only [PMF.map_comp, PMF.map_bind, Function.comp_def, Equiv.apply_symm_apply,
      Equiv.piSplitAt_apply, factors, others, bindPairLaw] using mapped
  have foreignLaw : law.map foreign = others.map restore := by
    have marginal := congrArg (fun measure => measure.map (fun pair => restore pair.2)) split
    simpa [PMF.map_comp, bindPairLaw, PMF.map_bind, PMF.bind_const,
      Function.comp_def, restore, foreign] using marginal
  have mapped := congrArg (fun measure => measure.map
    (fun pair => (own pair.1, restore pair.2))) split
  simp only [bindPairLaw, PMF.map_bind, PMF.map_comp, Function.comp_def] at mapped
  rw [foreignLaw]
  simpa [PMF.bind_map, PMF.map_comp, PMF.map_bind, bindPairLaw,
    Function.comp_def, factors, foreign, restore] using mapped

open Classical in
/-- If an event and a label are independent, conditioning on the event and a
selection of labels mixes the event-and-label posteriors against the selected
label law. The common event mass is retained in the joint atom identities. -/
theorem fiberPosteriors_of_independent_restriction
    {Point Word : Type*} (law : PMF Point) (words : PMF Word) (ownLaw : PMF Bool)
    (read : Point → Word) (own : Point → Bool) (admitted : Word → Bool)
    (forced : Word → PMF Point)
    (ownPositive : true ∈ ownLaw.support)
    (foreignPositive : true ∈ (words.map admitted).support)
    (joint : law.map (fun point => (own point, read point)) =
      bindPairLaw ownLaw (fun _ => words))
    (conditional : ∀ word ∈ words.support,
      forced word = fiberPosterior law (fun point => (own point, read point)) (true, word)) :
    let foreign := words.map (fun word => (word, admitted word))
    true ∈ (law.map (fun point => own point && admitted (read point))).support ∧
      true ∈ (foreign.map Prod.snd).support ∧
      fiberPosterior law (fun point => own point && admitted (read point)) true =
        (fiberPosterior foreign Prod.snd true).bind (fun word => forced word.1) ∧
      true ∈ (law.map own).support ∧
      fiberPosterior law own true = words.bind forced ∧
      (law.map (fun point => own point && admitted (read point))) true =
        ownLaw true * (words.map admitted) true ∧
      ∀ word point, admitted word = true →
        (ownLaw true * (words.map admitted) true) *
          (fiberPosterior words admitted true word * forced word point) =
            if own point = true ∧ read point = word then law point else 0 := by
  classical
  apply fiberPosteriors_of_factored_restriction law words read own admitted forced (ownLaw true)
    ((PMF.mem_support_iff _ _).mp ownPositive) (PMF.apply_ne_top _ _) foreignPositive
  intro word point
  by_cases supported : word ∈ words.support
  · have present : (true, word) ∈
        (law.map (fun point => (own point, read point))).support := by
      rw [joint, PMF.mem_support_iff, bindPairLaw_apply]
      exact mul_ne_zero ((PMF.mem_support_iff _ _).mp ownPositive)
        ((PMF.mem_support_iff _ _).mp supported)
    have mass : (law.map (fun point => (own point, read point))) (true, word) =
        ownLaw true * words word := by rw [joint, bindPairLaw_apply]
    rw [conditional word supported, ← mass]
    have disintegrated := fiberPosterior_disintegrate law
      (fun point => (own point, read point)) (true, word) present point
    simpa only [Set.indicator, Set.mem_ofPred_eq, Prod.mk.injEq] using disintegrated
  · have zero := (PMF.apply_eq_zero_iff _ _).mpr supported
    rw [zero, mul_zero, zero_mul]
    by_cases selected : own point = true ∧ read point = word
    · have lawZero : law point = 0 := by
        apply (PMF.apply_eq_zero_iff _ _).mpr
        intro member
        have mapped : (true, word) ∈
            (law.map (fun point => (own point, read point))).support :=
          (PMF.mem_support_map_iff ..).mpr ⟨point, member, Prod.ext selected.1 selected.2⟩
        rw [joint, PMF.mem_support_iff, bindPairLaw_apply, zero, mul_zero] at mapped
        exact mapped rfl
      simp [selected, lawZero]
    · simp only [selected, ite_false]

end GameTheory.Math.Probability
