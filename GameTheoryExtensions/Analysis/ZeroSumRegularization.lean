/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Minimax

/-! # Finite zero-sum saddle points with feature penalties

The objective penalizes the distance of expected row features from a reference
and rewards the corresponding column distance. An auxiliary finite matrix game
chooses signs to represent the two L1 norms. Its saddle point projects to the
original mixed strategy carriers; auxiliary signs are not part of the result.
-/

noncomputable section

namespace GameTheory.ZeroSumRegularization

open Math.Probability

variable {Row Col RowCoord ColCoord : Type}

/-- Distance of the expected feature vector from its supplied reference. -/
def featureDistance {Plan Coord : Type} [Fintype Coord]
    (feature : Plan → Coord → ℝ) (reference : Coord → ℝ) (law : PMF Plan) : ℝ :=
  ∑ coordinate, |expect law (fun plan => feature plan coordinate) - reference coordinate|

/-- Independent mixed play of a finite matrix payoff. -/
def expectedPayoff (payoff : Row → Col → ℝ) (row : PMF Row) (col : PMF Col) : ℝ :=
  expect row (fun first => expect col (payoff first))

/-- A zero-sum objective with separate L1 penalties on expected features. -/
def objective [Fintype RowCoord] [Fintype ColCoord]
    (payoff : Row → Col → ℝ)
    (rowFeature : Row → RowCoord → ℝ) (rowReference : RowCoord → ℝ)
    (colFeature : Col → ColCoord → ℝ) (colReference : ColCoord → ℝ)
    (weight : ℝ) (row : PMF Row) (col : PMF Col) : ℝ :=
  expectedPayoff payoff row col -
    weight * featureDistance rowFeature rowReference row +
    weight * featureDistance colFeature colReference col

private def sign (positive : Bool) : ℝ := if positive then 1 else -1

private def signed {Coord : Type} [Fintype Coord]
    (signs : Coord → Bool) (vector : Coord → ℝ) : ℝ :=
  ∑ coordinate, sign (signs coordinate) * vector coordinate

private theorem signed_le {Coord : Type} [Fintype Coord]
    (signs : Coord → Bool) (vector : Coord → ℝ) :
    signed signs vector ≤ ∑ coordinate, |vector coordinate| := by
  apply Finset.sum_le_sum
  intro coordinate _
  cases signs coordinate <;> simp only [sign, Bool.false_eq_true, ↓reduceIte,
    one_mul, neg_one_mul]
  · exact neg_le_abs _
  · exact le_abs_self _

private def bestSigns {Coord : Type} (vector : Coord → ℝ) : Coord → Bool :=
  fun coordinate => decide (0 ≤ vector coordinate)

private theorem signed_best {Coord : Type} [Fintype Coord] (vector : Coord → ℝ) :
    signed (bestSigns vector) vector = ∑ coordinate, |vector coordinate| := by
  apply Finset.sum_congr rfl
  intro coordinate _
  by_cases positive : 0 ≤ vector coordinate
  · simp [bestSigns, sign, positive, abs_of_nonneg positive]
  · simp [bestSigns, sign, positive, abs_of_neg (lt_of_not_ge positive)]

private theorem expect_signed {Plan Coord : Type} [Fintype Coord]
    (law : PMF Plan) (feature : Plan → Coord → ℝ) (reference : Coord → ℝ)
    (signs : Coord → Bool) :
    expect law (fun plan => signed signs (fun coordinate =>
      feature plan coordinate - reference coordinate)) =
      signed signs (fun coordinate =>
        expect law (fun plan => feature plan coordinate) - reference coordinate) := by
  simp only [signed, ← FinDist.expect_sum_comm, FinDist.expect_smul,
    FinDist.expect_sub, expect_constant]

private def matrix {First Second : Type} (payoff : First → Second → ℝ) :
    GameForm (Fin 2) where
  sig := { Strategy := fun _ => First × Second, Outcome := ℝ }
  play profile := PMF.pure (payoff (profile 0).1 (profile 1).2)

private def matrixUtility (outcome : ℝ) (who : Fin 2) : ℝ :=
  if who = 0 then outcome else -outcome

private theorem matrix_expected {First Second : Type} (payoff : First → Second → ℝ)
    (profile : Profile (matrix payoff).sig.mixed) :
    expectedUtility matrixUtility 0 ((matrix payoff).mixed.play profile) =
      expect (profile 0) (fun first => expect (profile 1) (fun second =>
        payoff first.1 second.2)) := by
  change expect ((independentProduct profile).bind fun pure =>
    PMF.pure (payoff (pure 0).1 (pure 1).2)) _ = _
  rw [← FinDist.piFin_eq_pi]
  simp [FinDist.piFin, FinDist.expect_bind, expect_map,
    FinDist.expect_product, matrixUtility]
  rfl

private theorem matrix_saddle {First Second : Type}
    [Finite First] [Nonempty First] [Finite Second] [Nonempty Second]
    (payoff : First → Second → ℝ) :
    ∃ first : PMF First, ∃ second : PMF Second,
      (∀ other : PMF First, expect other (fun row => expect second (payoff row)) ≤
        expect first (fun row => expect second (payoff row))) ∧
      (∀ other : PMF Second, expect first (fun row => expect second (payoff row)) ≤
        expect first (fun row => expect other (payoff row))) := by
  let := Fintype.ofFinite First
  let := Fintype.ofFinite Second
  let : (who : Fin 2) → Fintype ((matrix payoff).sig.Strategy who) :=
    fun _ => show Fintype (First × Second) from inferInstance
  let : (who : Fin 2) → Nonempty ((matrix payoff).sig.Strategy who) :=
    fun _ => show Nonempty (First × Second) from inferInstance
  obtain ⟨profile, saddle⟩ := exists_isSaddlePoint (F := matrix payoff) matrixUtility
    (by intro outcome; simp [matrixUtility, Fin.sum_univ_two])
  refine ⟨(profile 0).map Prod.fst, (profile 1).map Prod.snd, ?_, ?_⟩
  · intro other
    let deviation := other.map fun first => (first, Classical.ofNonempty (α := Second))
    have bound := saddle.1 deviation
    change expectedUtility matrixUtility 0
      ((matrix payoff).mixed.play (Profile.update profile 0 deviation)) ≤
        expectedUtility matrixUtility 0 ((matrix payoff).mixed.play profile) at bound
    rw [matrix_expected, matrix_expected] at bound
    simp only [deviation, expect_map, Profile.update_same,
      Profile.update_of_ne _ _ (by decide : (1 : Fin 2) ≠ 0)] at bound ⊢
    convert bound using 1 <;> rfl
  · intro other
    let deviation := other.map fun second => (Classical.ofNonempty (α := First), second)
    have bound := saddle.2 deviation
    change expectedUtility matrixUtility 0 ((matrix payoff).mixed.play profile) ≤
      expectedUtility matrixUtility 0
        ((matrix payoff).mixed.play (Profile.update profile 1 deviation)) at bound
    rw [matrix_expected, matrix_expected] at bound
    simp only [deviation, expect_map, Profile.update_same,
      Profile.update_of_ne _ _ (by decide : (0 : Fin 2) ≠ 1)] at bound ⊢
    convert bound using 1 <;> rfl

section Signs

variable [Fintype RowCoord] [Fintype ColCoord]
  (payoff : Row → Col → ℝ)
  (rowFeature : Row → RowCoord → ℝ) (rowReference : RowCoord → ℝ)
  (colFeature : Col → ColCoord → ℝ) (colReference : ColCoord → ℝ) (weight : ℝ)

private def signedPayoff (row : Row × (ColCoord → Bool))
    (col : Col × (RowCoord → Bool)) : ℝ :=
  payoff row.1 col.1 -
    weight * signed col.2 (fun coordinate => rowFeature row.1 coordinate -
      rowReference coordinate) +
    weight * signed row.2 (fun coordinate => colFeature col.1 coordinate -
      colReference coordinate)

private theorem signedPayoff_expect
    (row : PMF (Row × (ColCoord → Bool))) (col : PMF (Col × (RowCoord → Bool))) :
    expect row (fun first => expect col
      (signedPayoff payoff rowFeature rowReference colFeature colReference weight first)) =
      expect (row.map Prod.fst) (fun first => expect (col.map Prod.fst) (payoff first)) -
        weight * expect col (fun second => signed second.2 (fun coordinate =>
          expect (row.map Prod.fst) (fun first => rowFeature first coordinate) -
            rowReference coordinate)) +
        weight * expect row (fun first => signed first.2 (fun coordinate =>
          expect (col.map Prod.fst) (fun second => colFeature second coordinate) -
            colReference coordinate)) := by
  unfold signedPayoff
  simp only [FinDist.expect_add, FinDist.expect_sub,
    FinDist.expect_smul, expect_map]
  congr 2
  · rw [FinDist.expect_comm]
    apply congrArg (weight * ·)
    apply expect_congr_on_support
    intro second _
    exact expect_signed row (fun first => rowFeature first.1) rowReference second.2
  · apply expect_congr_on_support
    intro first _
    exact expect_signed col (fun second => colFeature second.1) colReference first.2

private def rowLift (row : PMF Row) (col : PMF Col) :
    PMF (Row × (ColCoord → Bool)) :=
  row.map fun first => (first, bestSigns (fun coordinate =>
    expect col (fun second => colFeature second coordinate) - colReference coordinate))

private def colLift (col : PMF Col) (row : PMF Row) :
    PMF (Col × (RowCoord → Bool)) :=
  col.map fun second => (second, bestSigns (fun coordinate =>
    expect row (fun first => rowFeature first coordinate) - rowReference coordinate))

private theorem row_deviation_bound (nonnegative : 0 ≤ weight)
    (row : PMF Row) (col : PMF (Col × (RowCoord → Bool))) :
    objective payoff rowFeature rowReference colFeature colReference weight row
        (col.map Prod.fst) ≤
      expect (rowLift colFeature colReference row (col.map Prod.fst)) (fun first =>
        expect col (signedPayoff payoff rowFeature rowReference colFeature colReference
          weight first)) := by
  rw [signedPayoff_expect]
  simp only [rowLift, PMF.map_comp, Function.comp_def,
    expect_map, signed_best, expect_constant]
  have bound : expect col (fun second => signed second.2 (fun coordinate =>
      expect row (fun first => rowFeature first coordinate) - rowReference coordinate)) ≤
      featureDistance rowFeature rowReference row :=
    FinDist.expect_le_of_forall _ _ _ fun second _ => signed_le second.2 _
  simp only [objective, expectedPayoff, featureDistance, expect_map] at bound ⊢
  nlinarith

private theorem col_deviation_bound (nonnegative : 0 ≤ weight)
    (row : PMF (Row × (ColCoord → Bool))) (col : PMF Col) :
    expect row (fun first =>
        expect (colLift rowFeature rowReference col (row.map Prod.fst))
          (signedPayoff payoff rowFeature rowReference colFeature colReference weight first)) ≤
      objective payoff rowFeature rowReference colFeature colReference weight
        (row.map Prod.fst) col := by
  rw [signedPayoff_expect]
  simp only [colLift, PMF.map_comp, Function.comp_def,
    expect_map, signed_best, expect_constant]
  have bound : expect row (fun first => signed first.2 (fun coordinate =>
      expect col (fun second => colFeature second coordinate) - colReference coordinate)) ≤
      featureDistance colFeature colReference col :=
    FinDist.expect_le_of_forall _ _ _ fun first _ => signed_le first.2 _
  simp only [objective, expectedPayoff, featureDistance, expect_map] at bound ⊢
  nlinarith

/-- Finite mixed strategies admit an exact saddle for the L1-regularized
objective. Only expected feature vectors are penalized; the result does not
require a positive lower bound on the weight or an interior reference vector. -/
theorem exists_saddle [Finite Row] [Nonempty Row] [Finite Col] [Nonempty Col]
    (nonnegative : 0 ≤ weight) :
    ∃ row : PMF Row, ∃ col : PMF Col,
      (∀ other, objective payoff rowFeature rowReference colFeature colReference
        weight other col ≤
          objective payoff rowFeature rowReference colFeature colReference weight row col) ∧
      (∀ other, objective payoff rowFeature rowReference colFeature colReference
        weight row col ≤
          objective payoff rowFeature rowReference colFeature colReference weight row other) := by
  classical
  let := Fintype.ofFinite Row
  let := Fintype.ofFinite Col
  obtain ⟨row, col, rowOptimal, colOptimal⟩ := matrix_saddle
    (signedPayoff payoff rowFeature rowReference colFeature colReference weight)
  let value := expect row (fun first => expect col
    (signedPayoff payoff rowFeature rowReference colFeature colReference weight first))
  have lower (other : PMF Row) :
      objective payoff rowFeature rowReference colFeature colReference weight other
        (col.map Prod.fst) ≤ value :=
    (row_deviation_bound payoff rowFeature rowReference colFeature colReference weight
      nonnegative other col).trans (rowOptimal _)
  have upper (other : PMF Col) : value ≤
      objective payoff rowFeature rowReference colFeature colReference weight
        (row.map Prod.fst) other :=
    (colOptimal _).trans
      (col_deviation_bound payoff rowFeature rowReference colFeature colReference weight
        nonnegative row other)
  exact ⟨row.map Prod.fst, col.map Prod.fst,
    fun other => (lower other).trans (upper (col.map Prod.fst)),
    fun other => (lower (row.map Prod.fst)).trans (upper other)⟩

/-- Approximate security at reference candidates controls the total feature
penalty of a regularized saddle. Only its two displayed comparisons are needed;
the candidates need not have exactly the reference features. -/
theorem penalty_bound (row referenceRow : PMF Row) (col referenceCol : PMF Col)
    (value rowError colError : ℝ)
    (rowOptimal : objective payoff rowFeature rowReference colFeature colReference
      weight referenceRow col ≤
        objective payoff rowFeature rowReference colFeature colReference weight row col)
    (colOptimal : objective payoff rowFeature rowReference colFeature colReference
      weight row col ≤
        objective payoff rowFeature rowReference colFeature colReference weight row referenceCol)
    (lowerSecurity : value - rowError ≤ expectedPayoff payoff referenceRow col)
    (upperSecurity : expectedPayoff payoff row referenceCol ≤ value + colError) :
    weight * (featureDistance rowFeature rowReference row +
      featureDistance colFeature colReference col) ≤
        rowError + colError + weight * (featureDistance rowFeature rowReference referenceRow +
          featureDistance colFeature colReference referenceCol) := by
  unfold objective at rowOptimal colOptimal
  nlinarith

end Signs

end GameTheory.ZeroSumRegularization
