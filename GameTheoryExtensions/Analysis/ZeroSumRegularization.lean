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
    (feature : Plan → Coord → ℝ) (reference : Coord → ℝ) (law : FinDist Plan) : ℝ :=
  ∑ coordinate, |law.expect (fun plan => feature plan coordinate) - reference coordinate|

/-- Independent mixed play of a finite matrix payoff. -/
def expectedPayoff (payoff : Row → Col → ℝ) (row : FinDist Row) (col : FinDist Col) : ℝ :=
  row.expect (fun first => col.expect (payoff first))

/-- A zero-sum objective with separate L1 penalties on expected features. -/
def objective [Fintype RowCoord] [Fintype ColCoord]
    (payoff : Row → Col → ℝ)
    (rowFeature : Row → RowCoord → ℝ) (rowReference : RowCoord → ℝ)
    (colFeature : Col → ColCoord → ℝ) (colReference : ColCoord → ℝ)
    (weight : ℝ) (row : FinDist Row) (col : FinDist Col) : ℝ :=
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
    (law : FinDist Plan) (feature : Plan → Coord → ℝ) (reference : Coord → ℝ)
    (signs : Coord → Bool) :
    law.expect (fun plan => signed signs (fun coordinate =>
      feature plan coordinate - reference coordinate)) =
      signed signs (fun coordinate =>
        law.expect (fun plan => feature plan coordinate) - reference coordinate) := by
  simp only [signed, ← FinDist.expect_sum_comm, FinDist.expect_smul,
    FinDist.expect_sub, FinDist.expect_const]

private def matrix {First Second : Type} (payoff : First → Second → ℝ) :
    GameForm (Fin 2) where
  sig := { Strategy := fun _ => First × Second, Outcome := ℝ }
  play profile := FinDist.pure (payoff (profile 0).1 (profile 1).2)

private def matrixUtility (outcome : ℝ) (who : Fin 2) : ℝ :=
  if who = 0 then outcome else -outcome

private theorem matrix_expected {First Second : Type} (payoff : First → Second → ℝ)
    (profile : Profile (matrix payoff).sig.mixed) :
    expectedUtility matrixUtility 0 ((matrix payoff).mixed.play profile) =
      (profile 0).expect (fun first => (profile 1).expect (fun second =>
        payoff first.1 second.2)) := by
  change ((FinDist.pi profile).bind fun pure =>
    FinDist.pure (payoff (pure 0).1 (pure 1).2)).expect _ = _
  rw [← FinDist.piFin_eq_pi]
  simp [FinDist.piFin, FinDist.expect_bind, FinDist.expect_map,
    FinDist.expect_product, matrixUtility]
  rfl

private theorem matrix_saddle {First Second : Type}
    [Finite First] [Nonempty First] [Finite Second] [Nonempty Second]
    (payoff : First → Second → ℝ) :
    ∃ first : FinDist First, ∃ second : FinDist Second,
      (∀ other : FinDist First, other.expect (fun row => second.expect (payoff row)) ≤
        first.expect (fun row => second.expect (payoff row))) ∧
      (∀ other : FinDist Second, first.expect (fun row => second.expect (payoff row)) ≤
        first.expect (fun row => other.expect (payoff row))) := by
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
    simp only [deviation, FinDist.expect_map, Profile.update_same,
      Profile.update_of_ne _ _ (by decide : (1 : Fin 2) ≠ 0)] at bound ⊢
    convert bound using 1 <;> rfl
  · intro other
    let deviation := other.map fun second => (Classical.ofNonempty (α := First), second)
    have bound := saddle.2 deviation
    change expectedUtility matrixUtility 0 ((matrix payoff).mixed.play profile) ≤
      expectedUtility matrixUtility 0
        ((matrix payoff).mixed.play (Profile.update profile 1 deviation)) at bound
    rw [matrix_expected, matrix_expected] at bound
    simp only [deviation, FinDist.expect_map, Profile.update_same,
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
    (row : FinDist (Row × (ColCoord → Bool))) (col : FinDist (Col × (RowCoord → Bool))) :
    row.expect (fun first => col.expect
      (signedPayoff payoff rowFeature rowReference colFeature colReference weight first)) =
      (row.map Prod.fst).expect (fun first => (col.map Prod.fst).expect (payoff first)) -
        weight * col.expect (fun second => signed second.2 (fun coordinate =>
          (row.map Prod.fst).expect (fun first => rowFeature first coordinate) -
            rowReference coordinate)) +
        weight * row.expect (fun first => signed first.2 (fun coordinate =>
          (col.map Prod.fst).expect (fun second => colFeature second coordinate) -
            colReference coordinate)) := by
  unfold signedPayoff
  simp only [FinDist.expect_add, FinDist.expect_sub,
    FinDist.expect_smul, FinDist.expect_map]
  congr 2
  · rw [FinDist.expect_comm]
    apply congrArg (weight * ·)
    apply FinDist.expect_congr
    intro second _
    exact expect_signed row (fun first => rowFeature first.1) rowReference second.2
  · apply FinDist.expect_congr
    intro first _
    exact expect_signed col (fun second => colFeature second.1) colReference first.2

private def rowLift (row : FinDist Row) (col : FinDist Col) :
    FinDist (Row × (ColCoord → Bool)) :=
  row.map fun first => (first, bestSigns (fun coordinate =>
    col.expect (fun second => colFeature second coordinate) - colReference coordinate))

private def colLift (col : FinDist Col) (row : FinDist Row) :
    FinDist (Col × (RowCoord → Bool)) :=
  col.map fun second => (second, bestSigns (fun coordinate =>
    row.expect (fun first => rowFeature first coordinate) - rowReference coordinate))

private theorem row_deviation_bound (nonnegative : 0 ≤ weight)
    (row : FinDist Row) (col : FinDist (Col × (RowCoord → Bool))) :
    objective payoff rowFeature rowReference colFeature colReference weight row
        (col.map Prod.fst) ≤
      (rowLift colFeature colReference row (col.map Prod.fst)).expect (fun first =>
        col.expect (signedPayoff payoff rowFeature rowReference colFeature colReference
          weight first)) := by
  rw [signedPayoff_expect]
  simp only [rowLift, FinDist.map_comp, Function.comp_def,
    FinDist.expect_map, signed_best, FinDist.expect_const]
  have bound : col.expect (fun second => signed second.2 (fun coordinate =>
      row.expect (fun first => rowFeature first coordinate) - rowReference coordinate)) ≤
      featureDistance rowFeature rowReference row :=
    FinDist.expect_le_of_forall _ _ _ fun second _ => signed_le second.2 _
  simp only [objective, expectedPayoff, featureDistance, FinDist.expect_map] at bound ⊢
  nlinarith

private theorem col_deviation_bound (nonnegative : 0 ≤ weight)
    (row : FinDist (Row × (ColCoord → Bool))) (col : FinDist Col) :
    row.expect (fun first =>
        (colLift rowFeature rowReference col (row.map Prod.fst)).expect
          (signedPayoff payoff rowFeature rowReference colFeature colReference weight first)) ≤
      objective payoff rowFeature rowReference colFeature colReference weight
        (row.map Prod.fst) col := by
  rw [signedPayoff_expect]
  simp only [colLift, FinDist.map_comp, Function.comp_def,
    FinDist.expect_map, signed_best, FinDist.expect_const]
  have bound : row.expect (fun first => signed first.2 (fun coordinate =>
      col.expect (fun second => colFeature second coordinate) - colReference coordinate)) ≤
      featureDistance colFeature colReference col :=
    FinDist.expect_le_of_forall _ _ _ fun first _ => signed_le first.2 _
  simp only [objective, expectedPayoff, featureDistance, FinDist.expect_map] at bound ⊢
  nlinarith

/-- Finite mixed strategies admit an exact saddle for the L1-regularized
objective. Only expected feature vectors are penalized; the result does not
require a positive lower bound on the weight or an interior reference vector. -/
theorem exists_saddle [Finite Row] [Nonempty Row] [Finite Col] [Nonempty Col]
    (nonnegative : 0 ≤ weight) :
    ∃ row : FinDist Row, ∃ col : FinDist Col,
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
  let value := row.expect (fun first => col.expect
    (signedPayoff payoff rowFeature rowReference colFeature colReference weight first))
  have lower (other : FinDist Row) :
      objective payoff rowFeature rowReference colFeature colReference weight other
        (col.map Prod.fst) ≤ value :=
    (row_deviation_bound payoff rowFeature rowReference colFeature colReference weight
      nonnegative other col).trans (rowOptimal _)
  have upper (other : FinDist Col) : value ≤
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
theorem penalty_bound (row referenceRow : FinDist Row) (col referenceCol : FinDist Col)
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
