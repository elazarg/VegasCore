/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.WithholdingCoupling
import GameTheory.Math.Probability.ExpectationMap

/-! # Deviation bounds under every public scheduler of concurrent reveals

Fix a graph whose only concurrency is between independent reveals, and a
profile whose kernels ignore the observation at publications, normalized so
that it ignores completion order. Its law of final store and completion records
is the same under every public scheduler. Consider a payoff of one player that
reads that final state, is never below an excluded value, and equals it once
the player has defaulted, and suppose the player's honest kernel opens
decisively. Then a bound on the player's payoff from every normalized
deviation under canonical scheduling bounds its payoff from every deviation
under every public scheduler.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

theorem PolicyObliviousAtPublications.normalize {who : Player} {policy : graph.BehavioralPolicy who}
    (oblivious : graph.PolicyObliviousAtPublications who policy) :
    graph.PolicyObliviousAtPublications who (graph.normalizePolicy who policy) := by
  intro event actor publication left right leftActive rightActive
  exact oblivious event actor publication _ _ _ _

theorem ObliviousAtPublications.policy {profile : graph.BehavioralProfile}
    (oblivious : graph.ObliviousAtPublications profile) (who : Player) :
    graph.PolicyObliviousAtPublications who (profile who) :=
  fun event actor publication left right leftActive rightActive =>
    oblivious who event actor publication left right leftActive rightActive

theorem PolicyObliviousAtPublications.honestAtPublications {who : Player}
    (policy : graph.BehavioralPolicy who) {honest : graph.BehavioralPolicy who}
    (oblivious : graph.PolicyObliviousAtPublications who honest) :
    graph.PolicyObliviousAtPublications who (graph.honestAtPublications who policy honest) := by
  intro event actor publication left right leftActive rightActive
  simp only [EventGraph.honestAtPublications, ite_eq_left publication]
  exact oblivious event actor publication left right leftActive rightActive

/-- The value of a payoff from the initial configuration is the expectation of a run. -/
theorem runValue_initial (profile : graph.BehavioralProfile) (scheduler : graph.PublicScheduler)
    (payoff : graph.Config → ℝ) (inputs : graph.Inputs) :
    runValue profile scheduler payoff (Config.initial inputs) =
      expect (graph.runPolicies scheduler profile inputs) payoff := by
  have initialRemaining : (Config.initial inputs : graph.Config).remaining =
      graph.order.eventCount := by
    simp [Config.remaining, Config.initial, EventOrder.Cut.empty]
  unfold runValue EventGraph.runPolicies EventGraph.run
  rw [initialRemaining]

/-- **Every-scheduler deviation bound.** A bound on one player's payoff from
every normalized deviation under canonical scheduling bounds its payoff from
every deviation under every public scheduler. -/
theorem RevealsOnlyConcurrent.deviation_le_of_canonical (only : graph.RevealsOnlyConcurrent)
    (finite : graph.FiniteActions) (profile : graph.BehavioralProfile)
    (oblivious : graph.ObliviousAtPublications profile) (who : Player)
    (decisive : graph.OpensDecisively who (graph.normalizePolicy who (profile who)))
    (value : graph.order.Cut × EventGraph.Store graph.layout ×
      (graph.EventId → Option graph.Completion) → ℝ)
    (excluded : ℝ) (low : ∀ config, excluded ≤ value (runKey config))
    (atDefault : ∀ config, who ∈ config.defaulted → value (runKey config) = excluded)
    (inputs : PMF graph.Inputs) (finiteInputs : inputs.support.Finite) (bound : ℝ)
    (canonical : ∀ policy : graph.BehavioralPolicy who,
      expect (inputs.bind (graph.runPolicies graph.canonicalScheduler
        (graph.normalizeProfile (Profile.update (sig := graph.gameSignature) profile who
          policy)))) (value ∘ runKey) ≤ bound)
    (scheduler : graph.PublicScheduler) (policy : graph.BehavioralPolicy who) :
    expect (inputs.bind (graph.runPolicies scheduler
      (Profile.update (sig := graph.gameSignature) (graph.normalizeProfile profile) who policy)))
      (value ∘ runKey) ≤ bound := by
  let deviating := Profile.update (sig := graph.gameSignature) (graph.normalizeProfile profile)
    who policy
  let honest := graph.normalizePolicy who (profile who)
  let improvedPolicy := graph.honestAtPublications who policy honest
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
  -- Step 1: honest opening at the player's publications.
  have coupled : expect (inputs.bind (graph.runPolicies scheduler deviating)) (value ∘ runKey) ≤
      expect (inputs.bind (graph.runPolicies scheduler (Profile.update
        (sig := graph.gameSignature) (graph.normalizeProfile profile) who improvedPolicy)))
        (value ∘ runKey) := by
    rw [towerInputs, towerInputs]
    apply expect_mono _ (payoffIntegrable_of_finite_support _ _ finiteInputs)
      (payoffIntegrable_of_finite_support _ _ finiteInputs)
    intro initial _
    have step := honestAtPublications_runValue_le finite deviating who honest
      (by simpa [deviating, honest, Profile.update_same] using decisive) scheduler
      (payoff := value ∘ runKey) (excluded := excluded) low atDefault _ (Config.initial initial)
      rfl
    have sameProfile : Profile.update (sig := graph.gameSignature) deviating who
          (graph.honestAtPublications who (deviating who) honest) =
        Profile.update (sig := graph.gameSignature) (graph.normalizeProfile profile) who
          improvedPolicy := by
      funext owner
      by_cases same : owner = who
      · subst owner
        simp only [deviating, improvedPolicy, Profile.update_same]
      · simp only [deviating, Profile.update_of_ne _ _ same]
    rwa [sameProfile] at step
  refine coupled.trans ?_
  -- Step 2: the improved deviation is a mixture of canonical normalized deviations.
  obtain ⟨mixture, law⟩ := only.deviation_mixture finite profile oblivious who improvedPolicy
    (PolicyObliviousAtPublications.honestAtPublications policy
      (oblivious.policy who).normalize) scheduler inputs finiteInputs
  rw [← expect_map runKey, law]
  have bindFinite : (mixture.bind fun assignment =>
      (inputs.bind (graph.runPolicies graph.canonicalScheduler
        (graph.normalizeProfile (Profile.update (sig := graph.gameSignature) profile who
          (replayPolicy (Profile.update (sig := graph.gameSignature)
            (graph.normalizeProfile profile) who improvedPolicy) assignment who
              improvedPolicy))))).map runKey).support.Finite := by
    rw [← law, PMF.support_map]
    exact (runFinite _ scheduler).image _
  rw [expect_bind_tower _ _ _ (payoffIntegrable_of_finite_support _ _ bindFinite)]
  apply expect_le_const _ _ _ bound
  · intro assignment _
    rw [expect_map]
    exact canonical _
  · apply payoffIntegrable_of_bounded_on_support (C := |excluded| + |bound|)
    intro assignment _
    rw [expect_map]
    have upper := canonical (replayPolicy (Profile.update (sig := graph.gameSignature)
      (graph.normalizeProfile profile) who improvedPolicy) assignment who improvedPolicy)
    have lower := lowerOf (graph.normalizeProfile (Profile.update (sig := graph.gameSignature)
      profile who (replayPolicy (Profile.update (sig := graph.gameSignature)
        (graph.normalizeProfile profile) who improvedPolicy) assignment who improvedPolicy)))
      graph.canonicalScheduler
    rw [abs_le]
    constructor <;> cases abs_cases excluded <;> cases abs_cases bound <;> linarith

omit [DecidableEq Player] in
/-- A payoff of configurations that depends only on the order-free key is a
function of that key. -/
theorem exists_value_of_factors (payoff : graph.Config → ℝ)
    (factors : ∀ left right : graph.Config, runKey left = runKey right →
      payoff left = payoff right) :
    ∃ value : graph.order.Cut × EventGraph.Store graph.layout ×
        (graph.EventId → Option graph.Completion) → ℝ, payoff = value ∘ runKey := by
  classical
  refine ⟨fun key => if found : ∃ config, runKey config = key then payoff found.choose else 0,
    funext fun config => ?_⟩
  have found : ∃ other, runKey other = runKey config := ⟨config, rfl⟩
  simp only [Function.comp_apply, dite_eq_left found]
  exact (factors _ _ found.choose_spec).symm

/-- **Every-scheduler deviation bound**, for a payoff that factors through the
order-free final state. -/
theorem RevealsOnlyConcurrent.deviation_le_of_canonical_of_factors
    (only : graph.RevealsOnlyConcurrent) (finite : graph.FiniteActions)
    (profile : graph.BehavioralProfile) (oblivious : graph.ObliviousAtPublications profile)
    (who : Player) (decisive : graph.OpensDecisively who (graph.normalizePolicy who (profile who)))
    (payoff : graph.Config → ℝ)
    (factors : ∀ left right : graph.Config, runKey left = runKey right →
      payoff left = payoff right)
    (excluded : ℝ) (low : ∀ config, excluded ≤ payoff config)
    (atDefault : ∀ config, who ∈ config.defaulted → payoff config = excluded)
    (inputs : PMF graph.Inputs) (finiteInputs : inputs.support.Finite) (bound : ℝ)
    (canonical : ∀ policy : graph.BehavioralPolicy who,
      expect (inputs.bind (graph.runPolicies graph.canonicalScheduler
        (graph.normalizeProfile (Profile.update (sig := graph.gameSignature) profile who
          policy)))) payoff ≤ bound)
    (scheduler : graph.PublicScheduler) (policy : graph.BehavioralPolicy who) :
    expect (inputs.bind (graph.runPolicies scheduler
      (Profile.update (sig := graph.gameSignature) (graph.normalizeProfile profile) who policy)))
      payoff ≤ bound := by
  obtain ⟨value, rfl⟩ := exists_value_of_factors payoff factors
  exact only.deviation_le_of_canonical finite profile oblivious who decisive value excluded low
    atDefault inputs finiteInputs bound canonical scheduler policy

end Vegas.EventGraph
