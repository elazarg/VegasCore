/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.ConsistentLikelihood
import GameTheoryExtensions.Math.Probability.ProductTransport

/-! # Projected Bayes beliefs through approximate reach factorizations

Fix an information site of a *native* model with finitely many histories, a
site of a *source* model, and a map `project` from the native site's histories
to the source site's. Bayes beliefs are reach weights divided by the site's
mass, so they inherit estimates on reach weights.

**Negligible histories.** Suppose every history of a set `bad` has a
counterpart outside `bad`, at the same site, whose reach is at least `1 / ratio`
times its own. A counterpart may serve several histories, at most as many as
the site has. The bad histories then carry at most the number of the site's
histories times `ratio` times the reach of the others
(`GameTheory.Protocol.InformationModel.sum_reach_le_of_counterpart`), and Bayes
belief at most that number times `ratio`
(`GameTheory.Protocol.InformationModel.sum_belief_le_of_counterpart`).

**Projected beliefs.** Split the site into regular and irregular histories.
Suppose that the reach of a regular history is the source reach of its
projection times a nonnegative operational weight, within a relative error;
that the operational weights of the regular histories projecting to any one
source history sum to a common mass, within a relative error; and that the
irregular reach is at most a ratio times the regular reach. Then the native
Bayes belief, pushed forward along `project`, is within an explicit bound of
the source Bayes belief in `ℓ¹`
(`GameTheory.Protocol.InformationModel.sum_abs_projectedBelief_sub_le`). This
is `GameTheory.Math.Probability.NearProductWeights` with a trivial excluded
coordinate. Along sequences whose three errors vanish the distance vanishes
(`GameTheory.Protocol.InformationModel.tendsto_sum_abs_projectedBelief_sub`),
so the projected native beliefs converge to the limit of the source beliefs
(`GameTheory.Protocol.InformationModel.tendsto_projectedBelief_of_converges`),
and expectations of bounded functions of the projected history follow
(`GameTheory.Protocol.InformationModel.abs_expect_projectedBelief_sub_le`).
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability Filter Finset

variable {ι : Type} [Fintype ι] {E F : ExecutionProtocol ι} {M : InformationModel E}
  {S : InformationModel F}

section Weights

variable {who : ι} {site : M.InformationSite who}

/-- The mass of a site with finitely many histories, as a real number, is the
sum of its reach weights. -/
theorem informationMass_toReal_eq_sum [Fintype (M.InformationHistory who site.1)]
    (strategy : ∀ player, M.BehavioralPolicy player) :
    (M.informationMass strategy who site).toReal =
      ∑ history : M.InformationHistory who site.1,
        (M.historyReachWeight strategy history.1).toReal := by
  unfold informationMass
  rw [tsum_fintype]
  exact ENNReal.toReal_sum fun history _ => by
    unfold historyReachWeight
    exact PMF.apply_ne_top _ _

/-- Under Bayes consistency, a history's real belief is its real reach divided
by the site's real mass. -/
theorem belief_toReal_eq_div {A : M.BehavioralAssessment}
    {antichain : M.DecisionInformationAntichain}
    (bayes : BehavioralAssessment.IsBayesConsistent M A antichain)
    (positive : 0 < M.informationMass A.strategy who site)
    (history : M.InformationHistory who site.1) :
    (A.belief who site history).toReal =
      (M.historyReachWeight A.strategy history.1).toReal /
        (M.informationMass A.strategy who site).toReal := by
  rw [bayes who site positive history, ENNReal.toReal_div]

/-- The real mass a pushforward of a law on a finite type gives a point is
the sum of the masses of its preimage. -/
theorem map_apply_toReal_eq_sum {α β : Type*} [Fintype α] [DecidableEq β] (law : PMF α)
    (project : α → β) (point : β) :
    ((law.map project) point).toReal = ∑ a with project a = point, (law a).toReal := by
  rw [PMF.map_apply, tsum_fintype,
    ENNReal.toReal_sum fun a _ => by split_ifs <;> simp [PMF.apply_ne_top], sum_filter]
  refine sum_congr rfl fun a _ => ?_
  by_cases same : project a = point
  · simp [same]
  · simp [same, Ne.symm same]

end Weights

section Counterpart

variable {who : ι} {site : M.InformationSite who} [Fintype (M.InformationHistory who site.1)]
  (strategy : ∀ player, M.BehavioralPolicy player)
  (bad : M.InformationHistory who site.1 → Prop) [DecidablePred bad]
  (counterpart : M.InformationHistory who site.1 → M.InformationHistory who site.1)
  {ratio : ℝ}

/-- **Negligible reach through counterparts.** If every history of `bad` has a
counterpart outside `bad` whose reach is at least `1 / ratio` times its own, the
bad histories carry at most the number of histories times `ratio` times the
reach of the others. -/
theorem sum_reach_le_of_counterpart (ratio_nonneg : 0 ≤ ratio)
    (counterpart_good : ∀ history, bad history → ¬ bad (counterpart history))
    (dominated : ∀ history, bad history →
      (M.historyReachWeight strategy history.1).toReal ≤
        ratio * (M.historyReachWeight strategy (counterpart history).1).toReal) :
    ∑ history with bad history, (M.historyReachWeight strategy history.1).toReal ≤
      (Fintype.card (M.InformationHistory who site.1) * ratio) *
        ∑ history with ¬ bad history, (M.historyReachWeight strategy history.1).toReal := by
  set reach := fun history : M.InformationHistory who site.1 =>
    (M.historyReachWeight strategy history.1).toReal
  classical
  have reachNonneg : ∀ history, 0 ≤ reach history := fun _ => ENNReal.toReal_nonneg
  have fibers : ∑ history with bad history, reach (counterpart history) =
      ∑ good with ¬ bad good,
        ((univ.filter bad).filter fun history => counterpart history = good).card * reach good := by
    rw [← sum_fiberwise_of_maps_to (g := counterpart) (t := univ.filter fun good => ¬ bad good)
      fun history member => mem_filter.mpr ⟨mem_univ _,
        counterpart_good history (mem_filter.mp member).2⟩]
    refine sum_congr rfl fun good _ => ?_
    rw [sum_congr rfl fun history member => by rw [(mem_filter.mp member).2], sum_const,
      nsmul_eq_mul]
  calc ∑ history with bad history, reach history
      ≤ ∑ history with bad history, ratio * reach (counterpart history) :=
        sum_le_sum fun history member => dominated history (mem_filter.mp member).2
    _ = ratio * ∑ good with ¬ bad good,
          ((univ.filter bad).filter fun history => counterpart history = good).card *
            reach good := by rw [← mul_sum, fibers]
    _ ≤ ratio * ∑ good with ¬ bad good,
          (Fintype.card (M.InformationHistory who site.1) : ℝ) * reach good := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun good _ => ?_) ratio_nonneg
        refine mul_le_mul_of_nonneg_right ?_ (reachNonneg good)
        exact_mod_cast card_le_univ _
    _ = (Fintype.card (M.InformationHistory who site.1) * ratio) *
          ∑ good with ¬ bad good, reach good := by
        rw [← mul_sum]
        ring

/-- **Negligible belief through counterparts.** Under Bayes consistency at a
site of positive mass, histories whose counterparts dominate them as in
`sum_reach_le_of_counterpart` carry belief at most the number of histories
times `ratio`. -/
theorem sum_belief_le_of_counterpart {A : M.BehavioralAssessment}
    {antichain : M.DecisionInformationAntichain}
    (bayes : BehavioralAssessment.IsBayesConsistent M A antichain)
    (positive : 0 < M.informationMass A.strategy who site) (ratio_nonneg : 0 ≤ ratio)
    (counterpart_good : ∀ history, bad history → ¬ bad (counterpart history))
    (dominated : ∀ history, bad history →
      (M.historyReachWeight A.strategy history.1).toReal ≤
        ratio * (M.historyReachWeight A.strategy (counterpart history).1).toReal) :
    ∑ history with bad history, (A.belief who site history).toReal ≤
      Fintype.card (M.InformationHistory who site.1) * ratio := by
  set reach := fun history : M.InformationHistory who site.1 =>
    (M.historyReachWeight A.strategy history.1).toReal
  set mass := (M.informationMass A.strategy who site).toReal
  have massEq : mass = ∑ history, reach history := informationMass_toReal_eq_sum _
  have massPos : 0 < mass := ENNReal.toReal_pos positive.ne'
    (ne_top_of_le_ne_top ENNReal.one_ne_top
      (M.informationMass_le_one A.strategy who site (antichain who site)))
  have bound := sum_reach_le_of_counterpart A.strategy bad counterpart ratio_nonneg
    counterpart_good dominated
  have goodLe : ∑ history with ¬ bad history, reach history ≤ mass := by
    rw [massEq]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      fun _ _ _ => ENNReal.toReal_nonneg
  have scaleNonneg : 0 ≤ (Fintype.card (M.InformationHistory who site.1) : ℝ) * ratio :=
    mul_nonneg (Nat.cast_nonneg _) ratio_nonneg
  rw [sum_congr rfl fun history _ => belief_toReal_eq_div bayes positive history, ← sum_div,
    div_le_iff₀ massPos]
  exact bound.trans (mul_le_mul_of_nonneg_left goodLe scaleNonneg)

end Counterpart

section Projection

/-- The `ℓ¹` bound of the projected-belief transport, in terms of the factor,
fiber and remainder errors. -/
def projectionErrorBound (factorError fiberError remainderRatio : ℝ) : ℝ :=
  2 * (factorError + fiberError + factorError * fiberError) /
      ((1 - factorError) * (1 - fiberError)) + 2 * remainderRatio

/-- The projection error bound vanishes with its three errors. -/
theorem tendsto_projectionErrorBound {factorError fiberError remainderRatio : ℕ → ℝ}
    (factor : Tendsto factorError atTop (nhds 0)) (fiber : Tendsto fiberError atTop (nhds 0))
    (remainder : Tendsto remainderRatio atTop (nhds 0)) :
    Tendsto (fun n => projectionErrorBound (factorError n) (fiberError n) (remainderRatio n))
      atTop (nhds 0) := by
  have numerator := ((factor.add fiber).add (factor.mul fiber)).const_mul 2
  have denominator := ((tendsto_const_nhds (x := (1 : ℝ))).sub factor).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).sub fiber)
  have limit := (numerator.div denominator (by norm_num)).add (remainder.const_mul 2)
  norm_num at limit
  exact limit

private theorem sum_subtype_filter {α : Type*} [Fintype α] (p q : α → Prop) [DecidablePred p]
    [DecidablePred q] (f : α → ℝ) :
    ∑ a : {a // p a} with q a.1, f a.1 = ∑ a with p a ∧ q a, f a := by
  rw [sum_filter, sum_filter, ← sum_subtype (univ.filter p) (by simp)
    (fun a => if q a then f a else 0), sum_filter]
  exact sum_congr rfl fun a _ => by by_cases first : p a <;> by_cases second : q a <;>
    simp [first, second]

private theorem sum_subtype_univ {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p]
    (f : α → ℝ) : ∑ a : {a // p a}, f a.1 = ∑ a with p a, f a := by
  rw [← sum_subtype (univ.filter p) (by simp) f]

private theorem sum_filter_and_add_not_and {α : Type*} [Fintype α] (p q : α → Prop)
    [DecidablePred p] [DecidablePred q] (f : α → ℝ) :
    ∑ a with p a ∧ q a, f a + ∑ a with ¬ p a ∧ q a, f a = ∑ a with q a, f a := by
  rw [sum_filter, sum_filter, sum_filter, ← sum_add_distrib]
  exact sum_congr rfl fun a _ => by by_cases first : p a <;> by_cases second : q a <;>
    simp [first, second]

variable {who : ι} {site : M.InformationSite who} {sourceSite : S.InformationSite who}
  [Fintype (M.InformationHistory who site.1)] [Fintype (S.InformationHistory who sourceSite.1)]
  [DecidableEq (S.InformationHistory who sourceSite.1)]

/-- **Projected-belief transport at one stage.** Let the native assessment `A`
and the source assessment `B` be Bayes consistent at sites of positive mass,
and `project` map the native site's histories to the source site's. Suppose
that

* every regular history has reach within relative error `factorError` of the
  source reach of its projection times its operational weight;
* the operational weights of the regular histories projecting to each source
  history sum to a common mass within relative error `fiberError`;
* the irregular reach is at most `remainderRatio` times the regular reach.

Then the native belief pushed forward along `project` is within
`projectionErrorBound factorError fiberError remainderRatio` of the source
belief in `ℓ¹`. -/
theorem sum_abs_projectedBelief_sub_le {A : M.BehavioralAssessment} {B : S.BehavioralAssessment}
    {antichain : M.DecisionInformationAntichain} {sourceAntichain : S.DecisionInformationAntichain}
    (bayes : BehavioralAssessment.IsBayesConsistent M A antichain)
    (sourceBayes : BehavioralAssessment.IsBayesConsistent S B sourceAntichain)
    (positive : 0 < M.informationMass A.strategy who site)
    (sourcePositive : 0 < S.informationMass B.strategy who sourceSite)
    (project : M.InformationHistory who site.1 → S.InformationHistory who sourceSite.1)
    (regular : M.InformationHistory who site.1 → Prop) [DecidablePred regular]
    (operational : M.InformationHistory who site.1 → ℝ) (fiberMass : ℝ)
    {factorError fiberError remainderRatio : ℝ}
    (operational_nonneg : ∀ history, 0 ≤ operational history) (fiberMass_nonneg : 0 ≤ fiberMass)
    (factorError_nonneg : 0 ≤ factorError) (factorError_lt_one : factorError < 1)
    (fiberError_nonneg : 0 ≤ fiberError) (fiberError_lt_one : fiberError < 1)
    (factor_close : ∀ history, regular history →
      |(M.historyReachWeight A.strategy history.1).toReal -
          (S.historyReachWeight B.strategy (project history).1).toReal * operational history| ≤
        factorError * ((S.historyReachWeight B.strategy (project history).1).toReal *
          operational history))
    (fiber_close : ∀ point,
      |(∑ history with regular history ∧ project history = point, operational history) -
          fiberMass| ≤ fiberError * fiberMass)
    (remainder_le : ∑ history with ¬ regular history,
        (M.historyReachWeight A.strategy history.1).toReal ≤
      remainderRatio * ∑ history with regular history,
        (M.historyReachWeight A.strategy history.1).toReal) :
    ∑ point, |(((A.belief who site).map project) point).toReal -
        (B.belief who sourceSite point).toReal| ≤
      projectionErrorBound factorError fiberError remainderRatio := by
  set reach := fun history : M.InformationHistory who site.1 =>
    (M.historyReachWeight A.strategy history.1).toReal
  set sourceReach := fun point : S.InformationHistory who sourceSite.1 =>
    (S.historyReachWeight B.strategy point.1).toReal
  have reachNonneg : ∀ history, 0 ≤ reach history := fun _ => ENNReal.toReal_nonneg
  have massEq : (M.informationMass A.strategy who site).toReal = ∑ history, reach history :=
    informationMass_toReal_eq_sum _
  have sourceMassEq : (S.informationMass B.strategy who sourceSite).toReal =
      ∑ point, sourceReach point := informationMass_toReal_eq_sum _
  have massPos : 0 < ∑ history, reach history := by
    rw [← massEq]
    exact ENNReal.toReal_pos positive.ne' (ne_top_of_le_ne_top ENNReal.one_ne_top
      (M.informationMass_le_one A.strategy who site (antichain who site)))
  have split : ∑ history, reach history =
      ∑ history with regular history, reach history +
        ∑ history with ¬ regular history, reach history :=
    (sum_filter_add_sum_filter_not univ regular reach).symm
  have regularPos : 0 < ∑ history with regular history, reach history := by
    by_contra notPos
    have zero : ∑ history with regular history, reach history = 0 :=
      le_antisymm (not_lt.mp notPos) (sum_nonneg fun history _ => reachNonneg history)
    have rest : ∑ history with ¬ regular history, reach history ≤ 0 := by
      have := remainder_le
      rw [zero, mul_zero] at this
      exact this
    linarith
  let weights : NearProductWeights (Ω := {history // regular history})
      (Ψ := {history // ¬ regular history}) (E := Unit)
      (fun history => (project history.1, ())) (fun history => project history.1) :=
    { regular := fun history => reach history.1
      remainder := fun history => reach history.1
      source := fun pair => sourceReach pair.1
      left := sourceReach
      right := fun _ => 1
      operational := fun history => operational history.1
      fiberMass := fun _ => fiberMass
      factorError := factorError
      fiberError := fiberError
      remainderRatio := remainderRatio
      left_nonneg := fun _ => ENNReal.toReal_nonneg
      right_nonneg := fun _ => zero_le_one
      operational_nonneg := fun history => operational_nonneg history.1
      fiberMass_nonneg := fun _ => fiberMass_nonneg
      remainder_nonneg := fun history => reachNonneg history.1
      source_eq_mul := fun _ _ => (mul_one _).symm
      regular_close := fun history => factor_close history.1 history.2
      fiber_close := fun point tag => by
        have same : ∑ history : {history // regular history} with
            (project history.1, ()) = (point, tag), operational history.1 =
            ∑ history with regular history ∧ project history = point, operational history := by
          rw [← sum_subtype_filter regular (fun history => project history = point)]
          refine sum_congr (filter_congr fun history _ => ?_) fun _ _ => rfl
          simp [Prod.ext_iff]
        rw [same]
        exact fiber_close point
      factorError_nonneg := factorError_nonneg
      factorError_lt_one := factorError_lt_one
      fiberError_nonneg := fiberError_nonneg
      fiberError_lt_one := fiberError_lt_one
      remainder_le := by
        rw [sum_subtype_univ regular reach, sum_subtype_univ (fun history => ¬ regular history)
          reach]
        exact remainder_le
      regular_pos := by
        rw [sum_subtype_univ regular reach]
        exact regularPos }
  have native : ∀ point, weights.nativeLaw point =
      (((A.belief who site).map project) point).toReal := fun point => by
    rw [map_apply_toReal_eq_sum, sum_congr rfl fun history _ =>
      belief_toReal_eq_div bayes positive history, ← sum_div, massEq]
    change ((∑ history : {history // regular history} with
          (project history.1, ()).1 = point, reach history.1) +
        ∑ history : {history // ¬ regular history} with project history.1 = point,
          reach history.1) /
      ((∑ history : {history // regular history}, reach history.1) +
        ∑ history : {history // ¬ regular history}, reach history.1) = _
    rw [sum_subtype_filter regular (fun history => project history = point),
      sum_subtype_filter (fun history => ¬ regular history)
        (fun history => project history = point),
      sum_subtype_univ regular reach, sum_subtype_univ (fun history => ¬ regular history) reach,
      sum_filter_and_add_not_and regular (fun history => project history = point), ← split]
  have source : ∀ point, weights.sourceLaw point = (B.belief who sourceSite point).toReal :=
    fun point => by
      rw [belief_toReal_eq_div sourceBayes sourcePositive point, sourceMassEq]
      change (∑ _unit : Unit, sourceReach point) /
        ∑ pair : S.InformationHistory who sourceSite.1 × Unit, sourceReach pair.1 = _
      rw [Fintype.sum_prod_type]
      simp [sourceReach]
  have bound := weights.sum_abs_nativeLaw_sub_sourceLaw_le
  rw [sum_congr rfl fun point _ => by rw [native point, source point]] at bound
  exact bound

/-- **Projected-belief transport along sequences.** If the three errors of
`sum_abs_projectedBelief_sub_le` vanish along a sequence of native and source
assessments, the `ℓ¹` distance between the projected native beliefs and the
source beliefs vanishes. -/
theorem tendsto_sum_abs_projectedBelief_sub {A : ℕ → M.BehavioralAssessment}
    {B : ℕ → S.BehavioralAssessment}
    {antichain : M.DecisionInformationAntichain} {sourceAntichain : S.DecisionInformationAntichain}
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent M (A n) antichain)
    (sourceBayes : ∀ n, BehavioralAssessment.IsBayesConsistent S (B n) sourceAntichain)
    (positive : ∀ n, 0 < M.informationMass (A n).strategy who site)
    (sourcePositive : ∀ n, 0 < S.informationMass (B n).strategy who sourceSite)
    (project : M.InformationHistory who site.1 → S.InformationHistory who sourceSite.1)
    (regular : ℕ → M.InformationHistory who site.1 → Prop) [∀ n, DecidablePred (regular n)]
    (operational : ℕ → M.InformationHistory who site.1 → ℝ) (fiberMass : ℕ → ℝ)
    {factorError fiberError remainderRatio : ℕ → ℝ}
    (operational_nonneg : ∀ n history, 0 ≤ operational n history)
    (fiberMass_nonneg : ∀ n, 0 ≤ fiberMass n)
    (factorError_nonneg : ∀ n, 0 ≤ factorError n) (fiberError_nonneg : ∀ n, 0 ≤ fiberError n)
    (factor : Tendsto factorError atTop (nhds 0)) (fiber : Tendsto fiberError atTop (nhds 0))
    (remainder : Tendsto remainderRatio atTop (nhds 0))
    (factor_close : ∀ n history, regular n history →
      |(M.historyReachWeight (A n).strategy history.1).toReal -
          (S.historyReachWeight (B n).strategy (project history).1).toReal *
            operational n history| ≤
        factorError n * ((S.historyReachWeight (B n).strategy (project history).1).toReal *
          operational n history))
    (fiber_close : ∀ n point,
      |(∑ history with regular n history ∧ project history = point, operational n history) -
          fiberMass n| ≤ fiberError n * fiberMass n)
    (remainder_le : ∀ n, ∑ history with ¬ regular n history,
        (M.historyReachWeight (A n).strategy history.1).toReal ≤
      remainderRatio n * ∑ history with regular n history,
        (M.historyReachWeight (A n).strategy history.1).toReal) :
    Tendsto (fun n => ∑ point, |((((A n).belief who site).map project) point).toReal -
        ((B n).belief who sourceSite point).toReal|) atTop (nhds 0) := by
  have factorSmall : ∀ᶠ n in atTop, factorError n < 1 :=
    factor.eventually (gt_mem_nhds (by norm_num))
  have fiberSmall : ∀ᶠ n in atTop, fiberError n < 1 :=
    fiber.eventually (gt_mem_nhds (by norm_num))
  refine squeeze_zero' (Eventually.of_forall fun _ => sum_nonneg fun _ _ => abs_nonneg _)
    ((factorSmall.and fiberSmall).mono fun n small =>
      sum_abs_projectedBelief_sub_le (bayes n) (sourceBayes n) (positive n) (sourcePositive n)
        project (regular n) (operational n) (fiberMass n) (operational_nonneg n)
        (fiberMass_nonneg n) (factorError_nonneg n) small.1 (fiberError_nonneg n) small.2
        (factor_close n) (fiber_close n) (remainder_le n))
    (tendsto_projectionErrorBound factor fiber remainder)

omit [Fintype ι] [Fintype (M.InformationHistory who site.1)]
    [DecidableEq (S.InformationHistory who sourceSite.1)] in
/-- **Projected beliefs converge to the source limit.** If the projected native
beliefs approach the source beliefs in `ℓ¹` and the source assessments
converge, the projected native belief of every source history converges to the
limit source belief. -/
theorem tendsto_projectedBelief_of_converges {A : ℕ → M.BehavioralAssessment}
    {B : ℕ → S.BehavioralAssessment} {limit : S.BehavioralAssessment}
    (converges : BehavioralAssessmentConvergesPointwise B limit)
    (project : M.InformationHistory who site.1 → S.InformationHistory who sourceSite.1)
    (close : Tendsto (fun n => ∑ point, |((((A n).belief who site).map project) point).toReal -
        ((B n).belief who sourceSite point).toReal|) atTop (nhds 0))
    (point : S.InformationHistory who sourceSite.1) :
    Tendsto (fun n => ((((A n).belief who site).map project) point).toReal) atTop
      (nhds ((limit.belief who sourceSite point).toReal)) := by
  have gap : Tendsto (fun n => ((((A n).belief who site).map project) point).toReal -
      ((B n).belief who sourceSite point).toReal) atTop (nhds 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 <| squeeze_zero (fun _ => abs_nonneg _)
      (fun n => single_le_sum (f := fun point =>
        |((((A n).belief who site).map project) point).toReal -
          ((B n).belief who sourceSite point).toReal|) (fun _ _ => abs_nonneg _)
        (mem_univ point)) close
  have sourceLimit := (converges.2 who sourceSite).toReal point
  have sum := sourceLimit.add gap
  rw [add_zero] at sum
  exact sum.congr fun n => add_sub_cancel _ _

omit [Fintype ι] [Fintype (M.InformationHistory who site.1)]
    [DecidableEq (S.InformationHistory who sourceSite.1)] in
/-- Expectations of a bounded function of the projected history under two
laws differ by at most the bound times their `ℓ¹` distance. -/
theorem abs_expect_projectedBelief_sub_le (native : PMF (M.InformationHistory who site.1))
    (source : PMF (S.InformationHistory who sourceSite.1))
    (project : M.InformationHistory who site.1 → S.InformationHistory who sourceSite.1)
    (payoff : S.InformationHistory who sourceSite.1 → ℝ) {bound : ℝ}
    (bounded : ∀ point, |payoff point| ≤ bound) :
    |expect (native.map project) payoff - expect source payoff| ≤
      bound * ∑ point, |((native.map project) point).toReal - (source point).toReal| := by
  rw [expect_eq_sum, expect_eq_sum, ← sum_sub_distrib, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun point _ => ?_)
  rw [← sub_mul, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (bounded point) (abs_nonneg _)

end Projection

end GameTheory.Protocol.InformationModel
