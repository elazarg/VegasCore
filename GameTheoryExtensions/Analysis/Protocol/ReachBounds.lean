/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.CounterfactualReach
import GameTheory.Protocol.BehavioralBayes

/-! # Bounds on the reach weight of one history

The reach weight of a nonempty history is the reach weight of its predecessor
times the mass of its last step
(`GameTheory.Protocol.InformationModel.historyReachWeight_eq_prior_mul`). Hence a
history is at most as likely as each of its prefixes and as each of its steps
(`historyReachWeight_le_of_reachesWithin`, `historyReachWeight_le_of_step`),
and a history whose every step has mass at least `c` has weight at least `c` to
the power of its length (`pow_le_historyReachWeight`). The mass of one step is
the product of the players' local choice masses and the transition mass, so a
step lower bound follows from lower bounds on those factors
(`ofReal_prod_mul_le_runBehavioralFrom_one`).

Along a family of fully mixed profiles these are the two sides of a
negligibility argument: histories through a small step are uniformly light,
histories whose every step is large are uniformly heavy, and on a finite set
the light part is at most a fixed multiple of the heavy part
(`sum_light_le_mul_sum_heavy`). At an information site this bounds the Bayes
belief of the light histories (`bayesBelief_light_le`).
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open scoped ENNReal

variable {ι : Type*} [Fintype ι] {E : ExecutionProtocol ι} (M : InformationModel E)
  (strategy : (i : ι) → M.BehavioralPolicy i)

/-- The empty history has weight one. -/
theorem historyReachWeight_initHistory :
    M.historyReachWeight strategy E.initHistory = 1 := by
  simp only [historyReachWeight, runBehavioral, runBehavioralFrom,
    ExecutionProtocol.initHistory, ExecutionProtocol.Trace.length,
    ExecutionProtocol.runRandomizedFor_zero, PMF.pure_apply, ↓reduceIte]

/-- The weight of a nonempty history is the weight of its predecessor times the
mass of its last step. -/
theorem historyReachWeight_eq_prior_mul (history : E.History)
    (positive : 0 < history.trace.length) :
    M.historyReachWeight strategy history =
      M.historyReachWeight strategy history.prior *
        M.runBehavioralFrom strategy 1 history.prior history := by
  have lengths := history.prior_trace_length positive
  unfold historyReachWeight runBehavioral runBehavioralFrom
  rw [← lengths]
  exact E.runRandomizedFor_apply_of_trace_succ _ _ _ _ (by
    simp only [ExecutionProtocol.initHistory, ExecutionProtocol.Trace.length]
    omega)

/-- A history is at most as likely as its predecessor. -/
theorem historyReachWeight_le_prior (history : E.History) :
    M.historyReachWeight strategy history ≤ M.historyReachWeight strategy history.prior := by
  rcases Nat.eq_zero_or_pos history.trace.length with zero | positive
  · rcases history with ⟨state, trace⟩
    cases trace with
    | start => exact le_rfl
    | extend => simp [ExecutionProtocol.Trace.length] at zero
  · rw [M.historyReachWeight_eq_prior_mul strategy history positive]
    exact mul_le_of_le_one_right' (PMF.coe_le_one _ _)

/-- A history is at most as likely as every history it continues. -/
theorem historyReachWeight_le_of_reachesWithin {fuel : ℕ} {start target : E.History}
    (reach : E.ReachesWithin fuel start target) :
    M.historyReachWeight strategy target ≤ M.historyReachWeight strategy start := by
  induction reach with
  | refl => exact le_rfl
  | step joint isLegal realized rest ih =>
      exact ih.trans (M.historyReachWeight_le_prior strategy _)

/-- A nonempty history is at most as likely as its last step. -/
theorem historyReachWeight_le_step (history : E.History)
    (positive : 0 < history.trace.length) :
    M.historyReachWeight strategy history ≤
      M.runBehavioralFrom strategy 1 history.prior history := by
  rw [M.historyReachWeight_eq_prior_mul strategy history positive]
  exact mul_le_of_le_one_left' (PMF.coe_le_one _ _)

/-- **A history through a light step is light.** Every continuation of a
nonempty history `step` is at most as likely as the last step of `step`. -/
theorem historyReachWeight_le_of_step {fuel : ℕ} {step target : E.History}
    (positive : 0 < step.trace.length) (reach : E.ReachesWithin fuel step target) :
    M.historyReachWeight strategy target ≤
      M.runBehavioralFrom strategy 1 step.prior step :=
  (M.historyReachWeight_le_of_reachesWithin strategy reach).trans
    (M.historyReachWeight_le_step strategy step positive)

/-- **A history through heavy steps only is heavy.** If a property is inherited
by predecessors and every nonempty history with it has a last step of mass at
least `c`, then every history with it has weight at least `c` to the power of
its length. -/
theorem pow_le_historyReachWeight (heavy : E.History → Prop) (c : ℝ≥0∞)
    (closed : ∀ history, heavy history → 0 < history.trace.length → heavy history.prior)
    (step : ∀ history, heavy history → 0 < history.trace.length →
      c ≤ M.runBehavioralFrom strategy 1 history.prior history)
    (history : E.History) (holds : heavy history) :
    c ^ history.trace.length ≤ M.historyReachWeight strategy history := by
  suffices bound : ∀ depth (history : E.History), history.trace.length = depth →
      heavy history → c ^ depth ≤ M.historyReachWeight strategy history from
    bound _ history rfl holds
  intro depth
  induction depth with
  | zero =>
      intro history length _
      rcases history with ⟨state, trace⟩
      cases trace with
      | start =>
          rw [pow_zero]
          exact (M.historyReachWeight_initHistory strategy).ge
      | extend => simp [ExecutionProtocol.Trace.length] at length
  | succ depth ih =>
      intro history length holds
      have positive : 0 < history.trace.length := by omega
      have priorLength : history.prior.trace.length = depth := by
        have := history.prior_trace_length positive
        omega
      rw [M.historyReachWeight_eq_prior_mul strategy history positive, pow_succ]
      exact mul_le_mul' (ih _ priorLength (closed _ holds positive)) (step _ holds positive)

/-- The power bound at a common fuel: a mass bound at most one, raised to any
fuel at least the history's length. -/
theorem pow_fuel_le_historyReachWeight (heavy : E.History → Prop) (c : ℝ≥0∞)
    (atMostOne : c ≤ 1)
    (closed : ∀ history, heavy history → 0 < history.trace.length → heavy history.prior)
    (step : ∀ history, heavy history → 0 < history.trace.length →
      c ≤ M.runBehavioralFrom strategy 1 history.prior history)
    {fuel : ℕ} (history : E.History) (holds : heavy history)
    (within : history.trace.length ≤ fuel) :
    c ^ fuel ≤ M.historyReachWeight strategy history :=
  (pow_le_pow_right_of_le_one' atMostOne within).trans
    (M.pow_le_historyReachWeight strategy heavy c closed step history holds)

/-- **Lower bound on one step.** Lower bounds on every player's local choice
mass and on the transition mass bound the mass of the extended history in the
one-step continuation law. -/
theorem ofReal_prod_mul_le_runBehavioralFrom_one (history : E.History)
    (running : ¬ E.terminal history.state)
    (joint : { action : ∀ i, Option (E.Action i) // E.Legal history.state action })
    (target : E.State) (realized : target ∈ (E.step history.state joint).support)
    (lower : ι → ℝ) (lowerNonneg : ∀ i, 0 ≤ lower i)
    (choiceLower : ∀ i, lower i ≤
      ((strategy i (M.infoOf i history.trace)) (M.choicesOfLegal history.trace joint i)).toReal)
    (transitionLower : ℝ) (transitionNonneg : 0 ≤ transitionLower)
    (transitionBound : transitionLower ≤ ((E.step history.state joint) target).toReal) :
    ENNReal.ofReal ((∏ i, lower i) * transitionLower) ≤
      M.runBehavioralFrom strategy 1 history (history.extend joint.2 realized) := by
  rw [ENNReal.ofReal_le_iff_le_toReal (PMF.apply_ne_top _ _),
    M.runBehavioralFrom_one_prob_extend strategy history running joint target realized,
    stepProb, M.behavioralJoint_prob_eq_prod strategy history.trace running joint]
  exact mul_le_mul (Finset.prod_le_prod₀ (fun i _ => lowerNonneg i) fun i _ => choiceLower i)
    transitionBound transitionNonneg (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg)

/-- **Belief of the light histories.** At a positive-mass information site, if
the light histories' total weight is at most `η` times the other histories'
total weight, the Bayes belief gives the light histories probability at most
`η`. -/
theorem bayesBelief_light_le {who : ι} (site : M.InformationSite who)
    (antichain : site.IsHistoryAntichain) (positive : 0 < M.informationMass strategy who site)
    (light : E.History → Prop) [DecidablePred light] (η : ℝ≥0∞)
    (negligible : (∑' history : M.InformationHistory who site.1,
        if light history.1 then M.historyReachWeight strategy history.1 else 0) ≤
      η * ∑' history : M.InformationHistory who site.1,
        if light history.1 then 0 else M.historyReachWeight strategy history.1) :
    (M.bayesBelief strategy who site antichain positive).toOuterMeasure
      {history | light history.1} ≤ η := by
  set lightMass := ∑' history : M.InformationHistory who site.1,
    if light history.1 then M.historyReachWeight strategy history.1 else 0
  set otherMass := ∑' history : M.InformationHistory who site.1,
    if light history.1 then 0 else M.historyReachWeight strategy history.1
  have total : M.informationMass strategy who site = lightMass + otherMass := by
    rw [informationMass, ← ENNReal.tsum_add]
    exact tsum_congr fun history => by split <;> simp
  have finite : M.informationMass strategy who site ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (M.informationMass_le_one strategy who site antichain)
      ENNReal.one_lt_top)
  have belief : (M.bayesBelief strategy who site antichain positive).toOuterMeasure
      {history | light history.1} = lightMass / M.informationMass strategy who site := by
    rw [PMF.toOuterMeasure_apply, ENNReal.div_eq_inv_mul, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun history => ?_
    by_cases holds : light history.1
    · simp only [Set.indicator, Set.mem_ofPred_eq, holds, ↓reduceIte, bayesBelief_apply,
        ENNReal.div_eq_inv_mul]
    · simp only [Set.indicator, Set.mem_ofPred_eq, holds, ↓reduceIte, mul_zero]
  rw [belief]
  apply ENNReal.div_le_of_le_mul
  rw [total]
  calc
    lightMass ≤ η * otherMass := negligible
    _ ≤ η * (lightMass + otherMass) := mul_le_mul_right le_add_self _

end GameTheory.Protocol.InformationModel

namespace GameTheory.Protocol

open scoped ENNReal

/-- **Light mass is negligible against heavy mass.** On finite sets, if every
light element weighs at most `τ` and every heavy element at least `m`, with
some heavy element present, the light total is at most `card · τ / m` times
the heavy total. -/
theorem sum_light_le_mul_sum_heavy {α : Type*} (weight : α → ℝ≥0∞)
    (light heavy : Finset α) (τ m : ℝ≥0∞)
    (lightBound : ∀ a ∈ light, weight a ≤ τ) (heavyBound : ∀ a ∈ heavy, m ≤ weight a)
    (present : heavy.Nonempty) (positive : m ≠ 0) (finite : m ≠ ⊤) :
    ∑ a ∈ light, weight a ≤ (light.card * τ / m) * ∑ a ∈ heavy, weight a := by
  obtain ⟨member, inside⟩ := present
  have upper : ∑ a ∈ light, weight a ≤ light.card * τ := by
    simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul light weight τ lightBound
  have heavyTotal : m ≤ ∑ a ∈ heavy, weight a :=
    (heavyBound member inside).trans (Finset.single_le_sum (fun _ _ => zero_le) inside)
  calc
    ∑ a ∈ light, weight a ≤ light.card * τ := upper
    _ = (light.card * τ / m) * m := (ENNReal.div_mul_cancel positive finite).symm
    _ ≤ (light.card * τ / m) * ∑ a ∈ heavy, weight a := mul_le_mul_right heavyTotal _

end GameTheory.Protocol
