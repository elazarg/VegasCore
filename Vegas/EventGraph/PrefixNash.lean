module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.PrefixDeviation
public import Vegas.EventGraph.CanonicalPrefix
public import Vegas.EventGraph.ConcurrentRevealNash
public import Vegas.EventGraph.RankedConfig

@[expose] public section

/-! # Prefix policies under absorbing exit payoffs

Canonical bounds for deviations that submit at bindings and ignore observations
at publications extend to unrestricted graph deviations. Prescribed prefix
policies retain the joint law of the complete terminal configuration in source
rank and every player's payoff under every public scheduler.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

private theorem update_twice (profile : graph.BehavioralProfile) (who : Player)
    (first second : graph.BehavioralPolicy who) :
    Profile.update (sig := graph.gameSignature)
        (Profile.update (sig := graph.gameSignature) profile who first) who second =
      Profile.update (sig := graph.gameSignature) profile who second := by
  funext owner
  by_cases same : owner = who
  · subst owner
    simp only [Profile.update_same]
  · simp only [Profile.update_of_ne _ _ same]

private theorem canonical_prefixProfile_bind
    (profile : graph.BehavioralProfile) (submits : graph.SubmitsBindings profile)
    (inputs : PMF graph.Inputs) :
    inputs.bind (graph.runPolicies graph.canonicalScheduler (graph.prefixProfile profile)) =
      inputs.bind (graph.runPolicies graph.canonicalScheduler profile) := by
  apply bind_congr_on_support _
  intro initial _
  exact runPolicies_canonical_prefixProfile profile submits initial

/-- Every public-scheduler deviation is bounded by canonical submitted deviations: repairing
binding omissions and withholding only raises an absorbing-exit payoff, and prefix replay
transports the remaining deviation to canonical scheduling. -/
theorem RevealRelaxedOrdered.deviation_le_of_canonical (relaxed : graph.RevealRelaxedOrdered)
    (finite : graph.FiniteActions) (profile : graph.BehavioralProfile)
    (submits : graph.SubmitsBindings profile) (oblivious : graph.ObliviousAtPublications profile)
    (who : Player) (decisive : graph.OpensDecisively who (graph.prefixPolicy who (profile who)))
    (value : graph.order.Cut × EventGraph.Store graph.layout ×
      (graph.EventId → Option graph.Completion) → ℝ)
    (excluded : ℝ) (low : ∀ config, excluded ≤ value (runKey config))
    (atDefault : ∀ config, who ∈ config.defaulted → value (runKey config) = excluded)
    (inputs : PMF graph.Inputs) (finiteInputs : inputs.support.Finite) (bound : ℝ)
    (canonical : ∀ policy : graph.BehavioralPolicy who,
      graph.PolicySubmitsBindings who policy →
      graph.PolicyObliviousAtPublications who policy →
      expect (inputs.bind (graph.runPolicies graph.canonicalScheduler
        (Profile.update (sig := graph.gameSignature) profile who policy)))
          (value ∘ runKey) ≤ bound)
    (scheduler : graph.PublicScheduler) (policy : graph.BehavioralPolicy who) :
    expect (inputs.bind (graph.runPolicies scheduler
      (Profile.update (sig := graph.gameSignature) (graph.prefixProfile profile) who policy)))
      (value ∘ runKey) ≤ bound := by
  have canonicalPrefix (policy : graph.BehavioralPolicy who)
      (policySubmits : graph.PolicySubmitsBindings who policy)
      (policyOblivious : graph.PolicyObliviousAtPublications who policy) :
      expect (inputs.bind (graph.runPolicies graph.canonicalScheduler
        (graph.prefixProfile (Profile.update (sig := graph.gameSignature) profile who policy))))
          (value ∘ runKey) ≤ bound := by
    rw [canonical_prefixProfile_bind _
      (SubmitsBindings.update graph submits who policy policySubmits) inputs]
    exact canonical policy policySubmits policyOblivious
  let deviating := Profile.update (sig := graph.gameSignature) (graph.prefixProfile profile)
    who policy
  let submitted := graph.submitPolicy who policy
  let honest := graph.prefixPolicy who (profile who)
  let improvedPolicy := graph.honestAtPublications who submitted honest
  have improvedSubmits : graph.PolicySubmitsBindings who improvedPolicy :=
    PolicySubmitsBindings.honestAtPublications graph
      (graph.policySubmitsBindings_submitPolicy who policy) honest
  have improvedOblivious : graph.PolicyObliviousAtPublications who improvedPolicy :=
    PolicyObliviousAtPublications.honestAtPublications submitted (oblivious.policy who).prefix
  have runFinite (chosen : graph.BehavioralProfile) (chosenScheduler : graph.PublicScheduler) :
      (inputs.bind (graph.runPolicies chosenScheduler chosen)).support.Finite := by
    rw [PMF.support_bind]
    exact finiteInputs.biUnion fun initial _ =>
      graph.runPolicies_support_finite chosenScheduler chosen
        (finite.profileFiniteSupport chosen) initial
  have towerInputs (chosen : graph.BehavioralProfile) (chosenScheduler : graph.PublicScheduler) :
      expect (inputs.bind (graph.runPolicies chosenScheduler chosen)) (value ∘ runKey) =
        expect inputs fun initial =>
          runValue chosen chosenScheduler (value ∘ runKey) (Config.initial initial) := by
    rw [expect_bind_tower _ _ _ (payoffIntegrable_of_finite_support _ _
      (runFinite chosen chosenScheduler))]
    apply expect_congr_on_support
    intro initial _
    rw [runValue_initial]
  have lowerOf (chosen : graph.BehavioralProfile) (chosenScheduler : graph.PublicScheduler) :
      excluded ≤ expect (inputs.bind (graph.runPolicies chosenScheduler chosen))
        (value ∘ runKey) := by
    have bound := expect_mono (f := fun _ => excluded) (g := value ∘ runKey)
      (μ := inputs.bind (graph.runPolicies chosenScheduler chosen))
      (fun config _ => low config) (payoffIntegrable_constant _ _)
      (payoffIntegrable_of_finite_support _ _ (runFinite chosen chosenScheduler))
    rwa [expect_constant] at bound
  have submittedBound : expect (inputs.bind (graph.runPolicies scheduler deviating))
      (value ∘ runKey) ≤
      expect (inputs.bind (graph.runPolicies scheduler (Profile.update
        (sig := graph.gameSignature) (graph.prefixProfile profile) who submitted)))
          (value ∘ runKey) := by
    rw [towerInputs, towerInputs]
    apply expect_mono _ (payoffIntegrable_of_finite_support _ _ finiteInputs)
      (payoffIntegrable_of_finite_support _ _ finiteInputs)
    intro initial _
    have step := submitPolicy_runValue_le finite deviating who scheduler low atDefault
      (Config.initial initial)
    simpa only [deviating, submitted, Profile.update_same, update_twice, Function.comp_def]
      using step
  have coupled : expect (inputs.bind (graph.runPolicies scheduler deviating)) (value ∘ runKey) ≤
      expect (inputs.bind (graph.runPolicies scheduler (Profile.update
        (sig := graph.gameSignature) (graph.prefixProfile profile) who improvedPolicy)))
        (value ∘ runKey) := by
    refine submittedBound.trans ?_
    rw [towerInputs, towerInputs]
    apply expect_mono _ (payoffIntegrable_of_finite_support _ _ finiteInputs)
      (payoffIntegrable_of_finite_support _ _ finiteInputs)
    intro initial _
    have step := honestAtPublications_runValue_le finite
      (Profile.update (sig := graph.gameSignature) (graph.prefixProfile profile) who submitted)
      who honest decisive scheduler (payoff := value ∘ runKey) (excluded := excluded) low atDefault
      _ (Config.initial initial) rfl
    simpa only [Profile.update_same, update_twice] using step
  refine coupled.trans ?_
  obtain ⟨mixture, law⟩ := relaxed.prefix_deviation_mixture finite profile submits oblivious who
    improvedPolicy improvedSubmits improvedOblivious scheduler inputs finiteInputs
  rw [← expect_map runKey, law]
  let replayed := fun assignment => prefixReplayPolicy
    (Profile.update (sig := graph.gameSignature) (graph.prefixProfile profile) who improvedPolicy)
      assignment who improvedPolicy
  have replayedSubmits (assignment) : graph.PolicySubmitsBindings who (replayed assignment) :=
    improvedSubmits.prefixReplay
  have replayedOblivious (assignment) :
      graph.PolicyObliviousAtPublications who (replayed assignment) :=
    improvedOblivious.prefixReplay
  have bindFinite : (mixture.bind fun assignment =>
      (inputs.bind (graph.runPolicies graph.canonicalScheduler
        (graph.prefixProfile (Profile.update (sig := graph.gameSignature) profile who
          (replayed assignment))))).map runKey).support.Finite := by
    rw [← law, PMF.support_map]
    exact (runFinite _ scheduler).image _
  rw [expect_bind_tower _ _ _ (payoffIntegrable_of_finite_support _ _ bindFinite)]
  apply expect_le_const _ _ _ bound
  · intro assignment _
    rw [expect_map]
    exact canonicalPrefix _ (replayedSubmits assignment) (replayedOblivious assignment)
  · apply payoffIntegrable_of_bounded_on_support (C := |excluded| + |bound|)
    intro assignment _
    rw [expect_map]
    have upper := canonicalPrefix (replayed assignment) (replayedSubmits assignment)
      (replayedOblivious assignment)
    have lower := lowerOf (graph.prefixProfile (Profile.update (sig := graph.gameSignature)
      profile who (replayed assignment))) graph.canonicalScheduler
    rw [abs_le]
    constructor <;> cases abs_cases excluded <;> cases abs_cases bound <;> linarith

/-- The every-scheduler deviation bound applies to any payoff determined by the final run key. -/
theorem RevealRelaxedOrdered.deviation_le_of_canonical_of_factors
    (relaxed : graph.RevealRelaxedOrdered) (finite : graph.FiniteActions)
    (profile : graph.BehavioralProfile) (submits : graph.SubmitsBindings profile)
    (oblivious : graph.ObliviousAtPublications profile) (who : Player)
    (decisive : graph.OpensDecisively who (graph.prefixPolicy who (profile who)))
    (payoff : graph.Config → ℝ)
    (factors : ∀ left right : graph.Config, runKey left = runKey right → payoff left = payoff right)
    (excluded : ℝ) (low : ∀ config, excluded ≤ payoff config)
    (atDefault : ∀ config, who ∈ config.defaulted → payoff config = excluded)
    (inputs : PMF graph.Inputs) (finiteInputs : inputs.support.Finite) (bound : ℝ)
    (canonical : ∀ policy : graph.BehavioralPolicy who,
      graph.PolicySubmitsBindings who policy →
      graph.PolicyObliviousAtPublications who policy →
      expect (inputs.bind (graph.runPolicies graph.canonicalScheduler
        (Profile.update (sig := graph.gameSignature) profile who policy)))
          payoff ≤ bound)
    (scheduler : graph.PublicScheduler) (policy : graph.BehavioralPolicy who) :
    expect (inputs.bind (graph.runPolicies scheduler
      (Profile.update (sig := graph.gameSignature) (graph.prefixProfile profile) who policy)))
      payoff ≤ bound := by
  obtain ⟨value, rfl⟩ := exists_value_of_factors payoff factors
  exact relaxed.deviation_le_of_canonical finite profile submits oblivious who decisive value
    excluded low atDefault inputs finiteInputs bound canonical scheduler policy

/-- Intended prefix-oblivious play retains its Nash error under every public scheduler once
canonical submitting deviations are bounded. Arbitrary deviations may omit or withhold. -/
theorem RevealRelaxedOrdered.isεNash_prefixProfile (relaxed : graph.RevealRelaxedOrdered)
    (finite : graph.FiniteActions) (profile : graph.BehavioralProfile)
    (submits : graph.SubmitsBindings profile) (oblivious : graph.ObliviousAtPublications profile)
    (decisive : ∀ who, graph.OpensDecisively who (graph.prefixPolicy who (profile who)))
    (payoff : Player → graph.Config → ℝ)
    (factors : ∀ who (left right : graph.Config), runKey left = runKey right →
      payoff who left = payoff who right)
    (excluded : Player → ℝ) (low : ∀ who config, excluded who ≤ payoff who config)
    (atDefault : ∀ who config, who ∈ config.defaulted → payoff who config = excluded who)
    (inputs : PMF graph.Inputs) (finiteInputs : inputs.support.Finite) (ε : ℝ)
    (canonical : ∀ who (policy : graph.BehavioralPolicy who),
      graph.PolicySubmitsBindings who policy →
      graph.PolicyObliviousAtPublications who policy →
      expect (inputs.bind (graph.runPolicies graph.canonicalScheduler
        (Profile.update (sig := graph.gameSignature) profile who policy)))
          (payoff who) ≤
        expect (inputs.bind (graph.runPolicies graph.canonicalScheduler profile))
          (payoff who) + ε)
    (scheduler : graph.PublicScheduler) :
    IsεNash (graph.gameForm inputs scheduler) (fun outcome who => payoff who outcome.1) ε
      (graph.prefixProfile profile) := by
  rw [IsεNash, isNash_iff]
  intro who deviation
  have support (chosen : Profile (graph.gameForm inputs scheduler).sig) :
      ((graph.gameForm inputs scheduler).play chosen).support.Finite :=
    graph.gameForm_play_support_finite inputs finiteInputs scheduler chosen
      (finite.profileFiniteSupport chosen)
  have honestIntegrable : UtilityIntegrable (fun outcome who => payoff who outcome.1) who
      ((graph.gameForm inputs scheduler).play (graph.prefixProfile profile)) :=
    payoffIntegrable_of_finite_support _ _ (support _)
  have deviationIntegrable : UtilityIntegrable (fun outcome who => payoff who outcome.1) who
      ((graph.gameForm inputs scheduler).play (Profile.update
        (sig := (graph.gameForm inputs scheduler).sig) (graph.prefixProfile profile) who
          deviation)) := payoffIntegrable_of_finite_support _ _ (support _)
  refine ⟨honestIntegrable.hasExpectation, deviationIntegrable.hasExpectation, ?_⟩
  rw [extendedExpectedUtility_eq honestIntegrable, extendedExpectedUtility_eq deviationIntegrable]
  refine EReal.coe_le_coe_iff.mpr ?_ |>.trans_eq (EReal.coe_add _ _)
  unfold expectedUtility
  rw [expect_gameForm_play inputs scheduler _ (payoff who),
    expect_gameForm_play inputs scheduler _ (payoff who)]
  obtain ⟨value, valueEq⟩ := exists_value_of_factors (payoff who) (factors who)
  have honest : expect (inputs.bind (graph.runPolicies scheduler (graph.prefixProfile profile)))
      (payoff who) = expect (inputs.bind (graph.runPolicies graph.canonicalScheduler
        profile)) (payoff who) := by
    calc
      _ = expect (inputs.bind (graph.runPolicies graph.canonicalScheduler
          (graph.prefixProfile profile))) (payoff who) := by
        rw [valueEq, ← expect_map runKey, ← expect_map runKey, PMF.map_bind, PMF.map_bind]
        congr 1
        apply bind_congr_on_support _
        intro initial _
        exact relaxed.runPolicies_prefixProfile_map_runKey profile oblivious scheduler initial
      _ = _ := congrArg (fun law => expect law (payoff who))
        (canonical_prefixProfile_bind profile submits inputs)
  rw [honest]
  exact relaxed.deviation_le_of_canonical_of_factors finite profile submits oblivious who
    (decisive who) (payoff who) (factors who) (excluded who) (low who) (atDefault who) inputs
    finiteInputs _ (canonical who) scheduler deviation

/-- Honest prefix play has the canonical law of every readout of its final
order-free state, for any distribution of initial inputs. -/
theorem RevealRelaxedOrdered.runPolicies_prefixProfile_map_eq_canonical
    (relaxed : graph.RevealRelaxedOrdered) (profile : graph.BehavioralProfile)
    (oblivious : graph.ObliviousAtPublications profile)
    (scheduler : graph.PublicScheduler) (inputs : PMF graph.Inputs) {β : Type}
    (observe : graph.Config → β)
    (factors : ∀ left right : graph.Config, runKey left = runKey right →
      observe left = observe right) :
    (inputs.bind (graph.runPolicies scheduler (graph.prefixProfile profile))).map observe =
      (inputs.bind (graph.runPolicies graph.canonicalScheduler
        (graph.prefixProfile profile))).map observe := by
  rw [PMF.map_bind, PMF.map_bind]
  apply bind_congr_on_support _
  intro initial _
  rw [← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
  exact bind_eq_of_map_key_eq runKey Set.univ _ _ (Set.subset_univ _) (Set.subset_univ _)
    (relaxed.runPolicies_prefixProfile_map_runKey profile oblivious scheduler initial) _
    (fun left _ right _ keys => by rw [Function.comp_apply, Function.comp_apply,
      factors left right keys])

/-- Terminal readouts have the same law whenever they depend only on the store
and individual completion records. -/
theorem RevealRelaxedOrdered.gameForm_prefixProfile_map_eq_canonical
    (relaxed : graph.RevealRelaxedOrdered) (profile : graph.BehavioralProfile)
    (oblivious : graph.ObliviousAtPublications profile)
    (scheduler : graph.PublicScheduler) (inputs : PMF graph.Inputs) {β : Type}
    (observe : graph.gameSignature.Outcome → β)
    (factors : ∀ left right : graph.gameSignature.Outcome,
      runKey left.1 = runKey right.1 → observe left = observe right) :
    ((graph.gameForm inputs scheduler).play (graph.prefixProfile profile)).map observe =
      ((graph.gameForm inputs graph.canonicalScheduler).play
        (graph.prefixProfile profile)).map observe := by
  have keyLaw :
      ((graph.gameForm inputs scheduler).play (graph.prefixProfile profile)).map
          (fun outcome => runKey outcome.1) =
        ((graph.gameForm inputs graph.canonicalScheduler).play
          (graph.prefixProfile profile)).map (fun outcome => runKey outcome.1) := by
    change (inputs.bind fun initial =>
        graph.terminalOutcomes scheduler (graph.prefixProfile profile) initial).map _ =
      (inputs.bind fun initial => graph.terminalOutcomes graph.canonicalScheduler
        (graph.prefixProfile profile) initial).map _
    rw [PMF.map_bind, PMF.map_bind]
    apply bind_congr_on_support _
    intro initial _
    change (graph.terminalOutcomes scheduler (graph.prefixProfile profile) initial).map
        (runKey ∘ Subtype.val) =
      (graph.terminalOutcomes graph.canonicalScheduler (graph.prefixProfile profile) initial).map
        (runKey ∘ Subtype.val)
    rw [← PMF.map_comp, ← PMF.map_comp, terminalOutcomes_map_val, terminalOutcomes_map_val]
    exact relaxed.runPolicies_prefixProfile_map_runKey profile oblivious scheduler initial
  rw [← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
  exact bind_eq_of_map_key_eq (fun outcome : graph.gameSignature.Outcome => runKey outcome.1)
    Set.univ _ _ (Set.subset_univ _) (Set.subset_univ _) keyLaw _
    (fun left _ right _ keys => by rw [Function.comp_apply, Function.comp_apply,
      factors left right keys])

/-- The joint law retains the complete terminal configuration in source rank
and every player's payoff, with the same arbitrary correlated initial law. -/
theorem RevealRelaxedOrdered.prefixProfile_ranked_payoff_law
    (relaxed : graph.RevealRelaxedOrdered) (profile : graph.BehavioralProfile)
    (submits : graph.SubmitsBindings profile)
    (oblivious : graph.ObliviousAtPublications profile)
    (payoff : Player → graph.Config → ℝ)
    (factors : ∀ who (left right : graph.Config), runKey left = runKey right →
      payoff who left = payoff who right)
    (scheduler : graph.PublicScheduler) (inputs : PMF graph.Inputs) :
    ((graph.gameForm inputs scheduler).play (graph.prefixProfile profile)).map
        (fun outcome => (rankedConfig (graph := graph) outcome.1 outcome.2,
          fun who => payoff who outcome.1)) =
      ((graph.gameForm inputs graph.canonicalScheduler).play profile).map
          (fun outcome => (rankedConfig (graph := graph) outcome.1 outcome.2,
            fun who => payoff who outcome.1)) := by
  rw [← gameForm_canonical_prefixProfile profile submits inputs]
  apply relaxed.gameForm_prefixProfile_map_eq_canonical profile oblivious scheduler inputs
  intro left right same
  apply Prod.ext
  · exact rankedConfig_congr same left.2 right.2
  · funext who
    exact factors who left.1 right.1 same

end Vegas.EventGraph
