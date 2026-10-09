/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.Bayes
import GameTheory.Analysis.Protocol.Sequential

/-! # Consistent beliefs from factored execution likelihoods

Finite groups of actual decision histories have Bayes probabilities equal to
their reach-weight sums divided by the site's mass. When two observation
families share the same type-dependent prefix likelihood, that prefix cancels
from a cross identity. A nonzero limiting timing factor on one side and a zero
factor on the other force one whole observation family to exclude a type.

The hypotheses concern sums of actual execution weights and convergence of
timing factors. They do not prescribe beliefs at unreached information sets.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability Filter

variable {ι : Type} [Fintype ι] {E : ExecutionProtocol ι} {M : InformationModel E}

/-- The belief of a finite group of complete histories at a decision site. -/
def finiteHistoryBelief (A : M.BehavioralAssessment) (who : ι)
    (site : M.InformationSite who)
    (histories : Finset (M.InformationHistory who site.1)) : ℝ :=
  ∑ history ∈ histories, (A.belief who site history).toReal

/-- The execution likelihood of the same finite group of complete histories. -/
def finiteHistoryReach (profile : ∀ who, M.BehavioralPolicy who) (who : ι)
    (site : M.InformationSite who)
    (histories : Finset (M.InformationHistory who site.1)) : ℝ :=
  ∑ history ∈ histories, (M.historyReachWeight profile history.1).toReal

/-- Bayes' rule for a finite history group; no common trace depth is needed. -/
theorem finiteHistoryBelief_eq_div_reach {A : M.BehavioralAssessment}
    (antichain : M.DecisionInformationAntichain)
    (bayes : BehavioralAssessment.IsBayesConsistent M A antichain)
    (who : ι) (site : M.InformationSite who)
    (positive : 0 < M.informationMass A.strategy who site)
    (histories : Finset (M.InformationHistory who site.1)) :
    finiteHistoryBelief A who site histories =
      finiteHistoryReach A.strategy who site histories /
        (M.informationMass A.strategy who site).toReal := by
  unfold finiteHistoryBelief finiteHistoryReach
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro history _
  rw [bayes who site positive history, ENNReal.toReal_div]

omit [Fintype ι] in
/-- Finite history-group beliefs converge with the assessment. -/
theorem finiteHistoryBelief_tendsto
    {sequence : ℕ → M.BehavioralAssessment} {A : M.BehavioralAssessment}
    (converges : BehavioralAssessmentConvergesPointwise sequence A)
    (who : ι) (site : M.InformationSite who)
    (histories : Finset (M.InformationHistory who site.1)) :
    Tendsto (fun n => finiteHistoryBelief (sequence n) who site histories) atTop
      (nhds (finiteHistoryBelief A who site histories)) := by
  unfold finiteHistoryBelief
  exact tendsto_finsetSum histories fun history _ =>
    (converges.belief who site).toReal history

omit [Fintype ι] in
/-- A zero finite group belief excludes every member of that group. -/
theorem belief_eq_zero_of_finiteHistoryBelief_eq_zero
    (A : M.BehavioralAssessment) (who : ι) (site : M.InformationSite who)
    (histories : Finset (M.InformationHistory who site.1))
    (zero : finiteHistoryBelief A who site histories = 0)
    (history : M.InformationHistory who site.1) (member : history ∈ histories) :
    A.belief who site history = 0 := by
  have each : (A.belief who site history).toReal = 0 := by
    have nonnegative (entry : M.InformationHistory who site.1) (_ : entry ∈ histories) :
        0 ≤ (A.belief who site entry).toReal := ENNReal.toReal_nonneg
    exact (Finset.sum_eq_zero_iff_of_nonneg nonnegative).mp zero history member
  exact ((ENNReal.toReal_eq_zero_iff _).mp each).resolve_right (PMF.apply_ne_top _ _)

/-- An observation family with execution likelihoods factored into a shared
type prefix, a public-observation factor, and a type-dependent timing factor.
The finite groups may include multiple raw representations and retry paths. -/
structure FactoredHistoryLikelihood (who : ι) (Index Label : Type)
    (prefixLikelihood : (∀ who, M.BehavioralPolicy who) → Label → ℝ) where
  site : Index → M.InformationSite who
  histories : (index : Index) → Label → Finset (M.InformationHistory who (site index).1)
  observationFactor : (∀ who, M.BehavioralPolicy who) → Index → ℝ
  timingFactor : (∀ who, M.BehavioralPolicy who) → Index → Label → ℝ
  reach_factored : ∀ profile index label,
    finiteHistoryReach profile who (site index) (histories index label) =
      prefixLikelihood profile label * observationFactor profile index *
        timingFactor profile index label
  timing_tendsto : ∀ (sequence : ℕ → M.BehavioralAssessment) (A : M.BehavioralAssessment),
    BehavioralAssessmentConvergesPointwise sequence A → ∀ index label,
      Tendsto (fun n => timingFactor (sequence n).strategy index label) atTop
        (nhds (timingFactor A.strategy index label))

namespace FactoredHistoryLikelihood

variable {who : ι} {X Y Label : Type}
    {prefixLikelihood : (∀ who, M.BehavioralPolicy who) → Label → ℝ}
    (left : FactoredHistoryLikelihood (M := M) who X Label prefixLikelihood)
    (right : FactoredHistoryLikelihood (M := M) who Y Label prefixLikelihood)

/-- The type-dependent timing product left after cancelling shared prefixes. -/
def cross (profile : ∀ who, M.BehavioralPolicy who)
    (first second : Label) (x : X) (y : Y) : ℝ :=
  left.timingFactor profile x first * right.timingFactor profile y second

/-- Bayes cross identity derived from actual factored reach weights. -/
theorem bayes_cross_identity {A : M.BehavioralAssessment}
    (antichain : M.DecisionInformationAntichain) (mixed : A.IsFullyMixed)
    (bayes : BehavioralAssessment.IsBayesConsistent M A antichain)
    (first second : Label) (x : X) (y : Y) :
    finiteHistoryBelief A who (left.site x) (left.histories x second) *
        finiteHistoryBelief A who (right.site y) (right.histories y first) *
        left.cross right A.strategy first second x y =
      finiteHistoryBelief A who (left.site x) (left.histories x first) *
        finiteHistoryBelief A who (right.site y) (right.histories y second) *
        left.cross right A.strategy second first x y := by
  have leftPositive := M.informationMass_pos_of_fullSupport A.strategy mixed who (left.site x)
  have rightPositive := M.informationMass_pos_of_fullSupport A.strategy mixed who (right.site y)
  rw [finiteHistoryBelief_eq_div_reach antichain bayes who _ leftPositive,
    finiteHistoryBelief_eq_div_reach antichain bayes who _ rightPositive,
    finiteHistoryBelief_eq_div_reach antichain bayes who _ leftPositive,
    finiteHistoryBelief_eq_div_reach antichain bayes who _ rightPositive]
  rw [left.reach_factored, left.reach_factored, right.reach_factored, right.reach_factored]
  unfold cross
  ring

/-- A consistent assessment cannot give both opposing types positive belief
in the corresponding observation groups when the timing cross degenerates. -/
theorem consistent_belief_product_eq_zero {A : M.BehavioralAssessment}
    (antichain : M.DecisionInformationAntichain)
    (consistent : A.IsSequentiallyConsistent antichain)
    (first second : Label) (x : X) (y : Y)
    (nonzero : left.cross right A.strategy first second x y ≠ 0)
    (zero : left.cross right A.strategy second first x y = 0) :
    finiteHistoryBelief A who (left.site x) (left.histories x second) *
      finiteHistoryBelief A who (right.site y) (right.histories y first) = 0 := by
  obtain ⟨sequence, approximate, converges⟩ := consistent
  have factorLimit (a b : Label) :
      Tendsto (fun n => left.cross right (sequence n).strategy a b x y) atTop
        (nhds (left.cross right A.strategy a b x y)) :=
    (left.timing_tendsto sequence A converges x a).mul
      (right.timing_tendsto sequence A converges y b)
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
        (right.histories y first) * left.cross right (sequence n).strategy first second x y) =
      fun n => finiteHistoryBelief (sequence n) who (left.site x)
        (left.histories x first) * finiteHistoryBelief (sequence n) who (right.site y)
        (right.histories y second) * left.cross right (sequence n).strategy second first x y := by
    funext n
    exact left.bayes_cross_identity right antichain (approximate n).1 (approximate n).2
      first second x y
  rw [same] at leftLimit
  have limits := tendsto_nhds_unique leftLimit rightLimit
  rw [zero, mul_zero] at limits
  exact (mul_eq_zero.mp limits).resolve_right nonzero

/-- One whole observation family excludes one of the two types. The conclusion
is uniform across observations, not a separate arbitrary choice at each pair. -/
theorem consistent_belief_face {A : M.BehavioralAssessment}
    (antichain : M.DecisionInformationAntichain)
    (consistent : A.IsSequentiallyConsistent antichain)
    (first second : Label)
    (nonzero : ∀ x y, left.cross right A.strategy first second x y ≠ 0)
    (zero : ∀ x y, left.cross right A.strategy second first x y = 0) :
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
    have product := left.consistent_belief_product_eq_zero right antichain consistent
      first second x y (nonzero x y) (zero x y)
    have rightZero := (mul_eq_zero.mp product).resolve_left notZero
    exact belief_eq_zero_of_finiteHistoryBelief_eq_zero A who _ _ rightZero history member

end FactoredHistoryLikelihood

end GameTheory.Protocol.InformationModel
