/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.ConsistentLikelihood

/-! # Posterior exclusion from asymptotic execution likelihoods

Unreached observations cannot be treated by absolute execution errors alone:
their common prefix probability may tend to zero faster than those errors.
This interface factors actual reach weights along the same fully mixed Bayes
sequence that witnesses consistency. The factors may include errors, provided
those errors vanish after dividing by the common type and observation factors.

The result allows histories involving additional raw calls to contribute to the
finite groups. Excluding those histories is not a premise. Their likelihood
contribution instead belongs in the operational factor estimate.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability Filter

variable {ι : Type} [Fintype ι] {E : ExecutionProtocol ι} {M : InformationModel E}

/-- Actual history-group likelihoods factored along an assessment sequence.
The common type-prefix factor is shared between observation families. -/
structure AsymptoticHistoryLikelihood (who : ι) (Index Label : Type)
    (sequence : ℕ → M.BehavioralAssessment) (prefixLikelihood : ℕ → Label → ℝ) where
  site : Index → M.InformationSite who
  histories : (index : Index) → Label → Finset (M.InformationHistory who (site index).1)
  observationFactor : ℕ → Index → ℝ
  timingFactor : ℕ → Index → Label → ℝ
  limitTimingFactor : Index → Label → ℝ
  reach_factored : ∀ n index label,
    finiteHistoryReach (sequence n).strategy who (site index) (histories index label) =
      prefixLikelihood n label * observationFactor n index * timingFactor n index label
  timing_tendsto : ∀ index label,
    Tendsto (fun n => timingFactor n index label) atTop (nhds (limitTimingFactor index label))

namespace AsymptoticHistoryLikelihood

variable {who : ι} {X Y Label : Type} {sequence : ℕ → M.BehavioralAssessment}
    {prefixLikelihood : ℕ → Label → ℝ}
    (left : AsymptoticHistoryLikelihood who X Label sequence prefixLikelihood)
    (right : AsymptoticHistoryLikelihood who Y Label sequence prefixLikelihood)

/-- The cross product of timing likelihood factors in one approximation. -/
def crossAt (n : ℕ) (first second : Label) (x : X) (y : Y) : ℝ :=
  left.timingFactor n x first * right.timingFactor n y second

/-- The cross product of the limiting timing likelihood factors. -/
def crossLimit (first second : Label) (x : X) (y : Y) : ℝ :=
  left.limitTimingFactor x first * right.limitTimingFactor y second

/-- The exact Bayes cancellation still holds for the error-inclusive factors. -/
theorem bayes_cross_identity (antichain : M.DecisionInformationAntichain)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent M (sequence n) antichain)
    (n : ℕ) (first second : Label) (x : X) (y : Y) :
    finiteHistoryBelief (sequence n) who (left.site x) (left.histories x second) *
        finiteHistoryBelief (sequence n) who (right.site y) (right.histories y first) *
        left.crossAt right n first second x y =
      finiteHistoryBelief (sequence n) who (left.site x) (left.histories x first) *
        finiteHistoryBelief (sequence n) who (right.site y) (right.histories y second) *
        left.crossAt right n second first x y := by
  have leftPositive := M.informationMass_pos_of_fullSupport (sequence n).strategy
    (mixed n) who (left.site x)
  have rightPositive := M.informationMass_pos_of_fullSupport (sequence n).strategy
    (mixed n) who (right.site y)
  rw [finiteHistoryBelief_eq_div_reach antichain (bayes n) who _ leftPositive,
    finiteHistoryBelief_eq_div_reach antichain (bayes n) who _ rightPositive,
    finiteHistoryBelief_eq_div_reach antichain (bayes n) who _ leftPositive,
    finiteHistoryBelief_eq_div_reach antichain (bayes n) who _ rightPositive]
  rw [left.reach_factored, left.reach_factored, right.reach_factored, right.reach_factored]
  unfold crossAt
  ring

/-- Bayes cross identities pass to the limiting beliefs and timing factors. -/
theorem belief_cross_identity {A : M.BehavioralAssessment}
    (antichain : M.DecisionInformationAntichain)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent M (sequence n) antichain)
    (converges : BehavioralAssessmentConvergesPointwise sequence A)
    (first second : Label) (x : X) (y : Y) :
    finiteHistoryBelief A who (left.site x) (left.histories x second) *
        finiteHistoryBelief A who (right.site y) (right.histories y first) *
        left.crossLimit right first second x y =
      finiteHistoryBelief A who (left.site x) (left.histories x first) *
        finiteHistoryBelief A who (right.site y) (right.histories y second) *
        left.crossLimit right second first x y := by
  have factorLimit (a b : Label) :
      Tendsto (fun n => left.crossAt right n a b x y) atTop
        (nhds (left.crossLimit right a b x y)) :=
    (left.timing_tendsto x a).mul (right.timing_tendsto y b)
  have leftLimit := ((finiteHistoryBelief_tendsto converges who (left.site x)
      (left.histories x second)).mul
      (finiteHistoryBelief_tendsto converges who (right.site y)
        (right.histories y first))).mul (factorLimit first second)
  have rightLimit := ((finiteHistoryBelief_tendsto converges who (left.site x)
      (left.histories x first)).mul
      (finiteHistoryBelief_tendsto converges who (right.site y)
        (right.histories y second))).mul (factorLimit second first)
  have same : (fun n => finiteHistoryBelief (sequence n) who (left.site x)
        (left.histories x second) * finiteHistoryBelief (sequence n) who (right.site y)
        (right.histories y first) * left.crossAt right n first second x y) =
      fun n => finiteHistoryBelief (sequence n) who (left.site x)
        (left.histories x first) * finiteHistoryBelief (sequence n) who (right.site y)
        (right.histories y second) * left.crossAt right n second first x y := by
    funext n
    exact left.bayes_cross_identity right antichain mixed bayes n first second x y
  rw [same] at leftLimit
  exact tendsto_nhds_unique leftLimit rightLimit

/-- Relative likelihood estimates, unlike absolute execution errors, constrain
the beliefs at observations whose probability vanishes along the sequence. -/
theorem belief_product_eq_zero {A : M.BehavioralAssessment}
    (antichain : M.DecisionInformationAntichain)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent M (sequence n) antichain)
    (converges : BehavioralAssessmentConvergesPointwise sequence A)
    (first second : Label) (x : X) (y : Y)
    (nonzero : left.crossLimit right first second x y ≠ 0)
    (zero : left.crossLimit right second first x y = 0) :
    finiteHistoryBelief A who (left.site x) (left.histories x second) *
      finiteHistoryBelief A who (right.site y) (right.histories y first) = 0 := by
  have limits := left.belief_cross_identity right antichain mixed bayes converges
    first second x y
  rw [zero, mul_zero] at limits
  exact (mul_eq_zero.mp limits).resolve_right nonzero

/-- One whole observation family excludes one type under asymptotic likelihood
factorization, uniformly over every observation in the other family. -/
theorem belief_face {A : M.BehavioralAssessment}
    (antichain : M.DecisionInformationAntichain)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent M (sequence n) antichain)
    (converges : BehavioralAssessmentConvergesPointwise sequence A)
    (first second : Label)
    (nonzero : ∀ x y, left.crossLimit right first second x y ≠ 0)
    (zero : ∀ x y, left.crossLimit right second first x y = 0) :
    (∀ x history, history ∈ left.histories x second →
      A.belief who (left.site x) history = 0) ∨
    (∀ y history, history ∈ right.histories y first →
      A.belief who (right.site y) history = 0) := by
  classical
  by_cases allZero : ∀ x, finiteHistoryBelief A who (left.site x)
      (left.histories x second) = 0
  · left
    intro x history member
    exact belief_eq_zero_of_finiteHistoryBelief_eq_zero A who _ _ (allZero x) history member
  · right
    obtain ⟨x, notZero⟩ := not_forall.mp allZero
    intro y history member
    have product := left.belief_product_eq_zero right antichain mixed bayes converges
      first second x y (nonzero x y) (zero x y)
    have rightZero := (mul_eq_zero.mp product).resolve_left notZero
    exact belief_eq_zero_of_finiteHistoryBelief_eq_zero A who _ _ rightZero history member

/-- Construct the adapter from operational likelihood estimates whose errors
vanish relative to the common prefix and observation factors. -/
def ofRelativeError
    (site : X → M.InformationSite who)
    (histories : (index : X) → Label → Finset (M.InformationHistory who (site index).1))
    (observationFactor : ℕ → X → ℝ) (leadingFactor : X → Label → ℝ)
    (error : ℕ → X → Label → ℝ)
    (reach : ∀ n index label,
      finiteHistoryReach (sequence n).strategy who (site index) (histories index label) =
        prefixLikelihood n label * observationFactor n index *
          (leadingFactor index label + error n index label))
    (vanishes : ∀ index label,
      Tendsto (fun n => error n index label) atTop (nhds 0)) :
    AsymptoticHistoryLikelihood who X Label sequence prefixLikelihood where
  site := site
  histories := histories
  observationFactor := observationFactor
  timingFactor n index label := leadingFactor index label + error n index label
  limitTimingFactor := leadingFactor
  reach_factored := reach
  timing_tendsto index label := by
    simpa only [add_zero] using tendsto_const_nhds.add (vanishes index label)

end AsymptoticHistoryLikelihood

namespace FactoredHistoryLikelihood

variable {who : ι} {Index Label : Type}
    {prefixLikelihood : (∀ who, M.BehavioralPolicy who) → Label → ℝ}
    (family : FactoredHistoryLikelihood (M := M) who Index Label prefixLikelihood)

/-- An exact continuous execution factorization supplies the more general
sequence-relative interface without introducing any approximation error. -/
def alongSequence {sequence : ℕ → M.BehavioralAssessment} {A : M.BehavioralAssessment}
    (converges : BehavioralAssessmentConvergesPointwise sequence A) :
    AsymptoticHistoryLikelihood who Index Label sequence
      (fun n => prefixLikelihood (sequence n).strategy) where
  site := family.site
  histories := family.histories
  observationFactor n := family.observationFactor (sequence n).strategy
  timingFactor n := family.timingFactor (sequence n).strategy
  limitTimingFactor := family.timingFactor A.strategy
  reach_factored n := family.reach_factored (sequence n).strategy
  timing_tendsto := family.timing_tendsto sequence A converges

end FactoredHistoryLikelihood

end GameTheory.Protocol.InformationModel
