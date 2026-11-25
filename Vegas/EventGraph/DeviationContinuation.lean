module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.PolicyPatch
public import GameTheory.Math.Probability.ExpectationConditioning

@[expose] public section

/-! # Unilateral continuation bounds at canonical event boundaries -/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A behavioral head choice followed by a tail deviation on the successful branch
bounds an external payoff when failure pays at most the graph utility floor. -/
theorem canonical_owned_expected_continuation
    (reference : graph.BehavioralProfile) (focal : Player) (event : graph.EventId)
    (head : graph.BehavioralPolicy focal) (count : Nat)
    {Seed NextSeed : Type} (prior : PMF Seed)
    (source : Seed → {config : graph.Config // config.cut.IsPrefix event.val})
    (nextPrior : PMF NextSeed) (nextSource : NextSeed → graph.Config)
    (marginal : nextPrior.map nextSource = (prior.map source).bind fun config =>
      eventStep (Function.update reference focal head) config.1 event
        (config.2.ready event.isLt))
    (utility : graph.Config → ℝ) (nativeValue : NextSeed → ℝ)
    (good : NextSeed → Bool) (floor bound : ℝ)
    (utilityBound : ∀ final, |utility final| ≤ bound)
    (utilityFloor : ∀ final, floor ≤ utility final)
    (nativeIntegrable : PayoffIntegrable nextPrior nativeValue)
    (bad : ∀ seed ∈ nextPrior.support, good seed = false → nativeValue seed ≤ floor)
    (tail : ∀ _present : true ∈ (nextPrior.map good).support,
      ∃ policy : graph.BehavioralPolicy focal,
        expect (fiberPosterior nextPrior good true) nativeValue ≤
          expect ((fiberPosterior nextPrior good true).bind fun seed =>
            graph.runPlan (graph.policyPlan (Function.update reference focal policy)
              graph.canonicalScheduler) count (nextSource seed)) utility) :
    ∃ policy : graph.BehavioralPolicy focal,
      expect nextPrior nativeValue ≤ expect (prior.bind fun seed =>
        graph.runPlan (graph.policyPlan (Function.update reference focal policy)
          graph.canonicalScheduler) (count + 1) (source seed).1) utility := by
  classical
  obtain ⟨tailPolicy, goodBound⟩ : ∃ policy : graph.BehavioralPolicy focal,
      true ∈ (nextPrior.map good).support →
        expect (fiberPosterior nextPrior good true) nativeValue ≤
          expect ((fiberPosterior nextPrior good true).bind fun seed =>
            graph.runPlan (graph.policyPlan (Function.update reference focal policy)
              graph.canonicalScheduler) count (nextSource seed)) utility := by
    by_cases present : true ∈ (nextPrior.map good).support
    · obtain ⟨policy, comparison⟩ := tail present
      exact ⟨policy, fun _ => comparison⟩
    · exact ⟨reference focal, fun impossible => (present impossible).elim⟩
  let continuation := fun seed => graph.runPlan
    (graph.policyPlan (Function.update reference focal tailPolicy) graph.canonicalScheduler)
      count (nextSource seed)
  let value := fun seed => expect (continuation seed) utility
  have integrable (law : PMF NextSeed) : PayoffIntegrable (law.bind continuation) utility :=
    payoffIntegrable_of_bounded _ _ utilityBound
  have valueIntegrable : PayoffIntegrable nextPrior value :=
    payoffIntegrable_bind_conditionalExpectation nextPrior continuation utility
      (integrable nextPrior)
  have tailBound : expect nextPrior nativeValue ≤
      expect (nextPrior.bind continuation) utility := by
    rw [expect_bind_tower nextPrior continuation utility (integrable nextPrior)]
    apply expect_fiberwise_le nextPrior good nativeValue value nativeIntegrable valueIntegrable
    intro selected present
    cases selected with
    | false =>
        apply expect_mono _ (payoffIntegrable_fiberPosterior nextPrior good nativeValue
          nativeIntegrable false) (payoffIntegrable_fiberPosterior nextPrior good value
            valueIntegrable false)
        intro seed member
        obtain ⟨selected, supported⟩ := mem_support_fiberPosterior present member
        have lower : floor ≤ value seed := by
          have expected := expect_mono (fun final _ => utilityFloor final)
            (payoffIntegrable_constant (continuation seed) floor)
            (payoffIntegrable_of_bounded (continuation seed) utility utilityBound)
          simpa only [expect_constant] using expected
        exact (bad seed supported selected).trans lower
    | true =>
        have comparison := goodBound present
        rw [expect_bind_tower _ continuation utility
          (integrable (fiberPosterior nextPrior good true))] at comparison
        exact comparison
  let policy := patchPolicy event head tailPolicy
  have tails (config : graph.Config) (completed : event ∈ config.cut.completed) :
      graph.runPlan (graph.policyPlan (Function.update reference focal policy)
          graph.canonicalScheduler) count config =
        graph.runPlan (graph.policyPlan (Function.update reference focal tailPolicy)
          graph.canonicalScheduler) count config := by
    apply runPlan_congr_of_actionDistribution graph.canonicalScheduler (fun other => other = event)
      (fun current other different => actionDistribution_update_patch_of_ne reference focal event
        head tailPolicy current different) count config
    intro other same
    exact same.symm ▸ completed
  have first (config : {config : graph.Config // config.cut.IsPrefix event.val}) :
      graph.runPlan (graph.policyPlan (Function.update reference focal policy)
          graph.canonicalScheduler) (count + 1) config.1 =
        (eventStep (Function.update reference focal head) config.1 event
          (config.2.ready event.isLt)).bind fun next =>
            graph.runPlan (graph.policyPlan (Function.update reference focal tailPolicy)
              graph.canonicalScheduler) count next := by
    have ready : config.1.cut.Ready event := config.2.ready event.isLt
    have least (other : graph.EventId)
        (otherReady : config.1.cut.Ready other) : event ≤ other := by
      apply Fin.le_iff_val_le_val.mpr
      by_contra smaller
      exact otherReady.1 ((config.2.2 other).mpr (by omega))
    rw [runPlan_canonical_succ _ count config.1 ready.not_terminal event ready least]
    simp only [eventStep, policy, actionDistribution_update_patch_self, PMF.bind_bind]
    apply bind_congr_on_support _
    intro action _
    apply bind_congr_on_support _
    intro next moved
    apply tails next
    rw [config.1.step_cut event ready action next moved, EventOrder.Cut.mem_complete]
    exact Or.inl rfl
  have law : (prior.bind fun seed => graph.runPlan
      (graph.policyPlan (Function.update reference focal policy) graph.canonicalScheduler)
        (count + 1) (source seed).1) =
      nextPrior.bind (fun seed => graph.runPlan
        (graph.policyPlan (Function.update reference focal tailPolicy) graph.canonicalScheduler)
          count (nextSource seed)) := by
    calc
      _ = (prior.map source).bind (fun config => graph.runPlan
          (graph.policyPlan (Function.update reference focal policy) graph.canonicalScheduler)
            (count + 1) config.1) := by rw [PMF.bind_map]; rfl
      _ = ((prior.map source).bind fun config =>
          eventStep (Function.update reference focal head) config.1 event
            (config.2.ready event.isLt)).bind (fun next => graph.runPlan
              (graph.policyPlan (Function.update reference focal tailPolicy)
                graph.canonicalScheduler) count next) := by
        rw [PMF.bind_bind]
        apply bind_congr_on_support _
        intro config _
        exact first config
      _ = _ := by rw [← marginal, PMF.bind_map]; rfl
  exact ⟨policy, by rw [law]; exact tailBound⟩

/-- A unilateral continuation bound extends backwards across a different owner's
canonical event when its successor marginal agrees with the reference step. -/
theorem canonical_foreign_expected_continuation
    (reference : graph.BehavioralProfile) (focal owner : Player) (different : owner ≠ focal)
    (event : graph.EventId) (owned : graph.actor? event = some owner) (count : Nat)
    {Seed NextSeed : Type} (prior : PMF Seed)
    (source : Seed → {config : graph.Config // config.cut.IsPrefix event.val})
    (nextPrior : PMF NextSeed) (nextSource : NextSeed → graph.Config)
    (marginal : nextPrior.map nextSource = (prior.map source).bind fun config =>
      eventStep reference config.1 event (config.2.ready event.isLt))
    (utility : graph.Config → ℝ) (nativeValue : NextSeed → ℝ)
    (tail : ∃ policy : graph.BehavioralPolicy focal,
      expect nextPrior nativeValue ≤ expect (nextPrior.bind fun seed =>
        graph.runPlan (graph.policyPlan (Function.update reference focal policy)
          graph.canonicalScheduler) count (nextSource seed)) utility) :
    ∃ policy : graph.BehavioralPolicy focal,
      expect nextPrior nativeValue ≤ expect (prior.bind fun seed =>
        graph.runPlan (graph.policyPlan (Function.update reference focal policy)
          graph.canonicalScheduler) (count + 1) (source seed).1) utility := by
  obtain ⟨policy, comparison⟩ := tail
  have first (config : {config : graph.Config // config.cut.IsPrefix event.val}) :
      graph.runPlan (graph.policyPlan (Function.update reference focal policy)
          graph.canonicalScheduler) (count + 1) config.1 =
        (eventStep reference config.1 event (config.2.ready event.isLt)).bind fun next =>
          graph.runPlan (graph.policyPlan (Function.update reference focal policy)
            graph.canonicalScheduler) count next := by
    have ready : config.1.cut.Ready event := config.2.ready event.isLt
    have least (other : graph.EventId) (otherReady : config.1.cut.Ready other) : event ≤ other := by
      apply Fin.le_iff_val_le_val.mpr
      by_contra smaller
      exact otherReady.1 ((config.2.2 other).mpr (by omega))
    rw [runPlan_canonical_succ _ count config.1 ready.not_terminal event ready least]
    have same : actionDistribution (Function.update reference focal policy) config.1 event =
        actionDistribution reference config.1 event := by
      rw [actionDistribution_of_actor _ _ owned, actionDistribution_of_actor _ _ owned]
      simp only [Function.update_of_ne different]
    simp only [eventStep, same]
  have law : (prior.bind fun seed => graph.runPlan
      (graph.policyPlan (Function.update reference focal policy) graph.canonicalScheduler)
        (count + 1) (source seed).1) =
      nextPrior.bind (fun seed => graph.runPlan
        (graph.policyPlan (Function.update reference focal policy) graph.canonicalScheduler)
          count (nextSource seed)) := by
    calc
      _ = (prior.map source).bind (fun config => graph.runPlan
          (graph.policyPlan (Function.update reference focal policy) graph.canonicalScheduler)
            (count + 1) config.1) := by rw [PMF.bind_map]; rfl
      _ = ((prior.map source).bind fun config =>
          eventStep reference config.1 event (config.2.ready event.isLt)).bind (fun next =>
            graph.runPlan (graph.policyPlan (Function.update reference focal policy)
              graph.canonicalScheduler) count next) := by
        rw [PMF.bind_bind]
        apply bind_congr_on_support _
        intro config _
        exact first config
      _ = _ := by rw [← marginal, PMF.bind_map]; rfl
  exact ⟨policy, by rw [law]; exact comparison⟩

end Vegas.EventGraph
