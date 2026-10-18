/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastAudit
import Vegas.Examples.CommitSeedBroadcastHelperPublicPackets
import GameTheoryExtensions.Analysis.Protocol.BehavioralContinuity

/-! # Conditional original native continuation limits without a prior mass floor -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability Filter

private theorem native_continuation_uniform_limit
    (sequence : Nat → ∀ owner, rawModel.BehavioralPolicy owner)
    (profile : ∀ owner, rawModel.BehavioralPolicy owner)
    (converges : ∀ owner (site : rawModel.InformationSite owner),
      PMFConvergesPointwise (fun n => sequence n owner site.1) (profile owner site.1))
    (payoff : rawProtocol.History → ℝ) (fuel : Nat) (error : ℝ) (positive : 0 < error) :
    ∀ᶠ n in atTop, ∀ history : rawProtocol.History,
      |expect (rawModel.runBehavioralFrom (sequence n) fuel history) payoff -
        expect (rawModel.runBehavioralFrom profile fuel history) payoff| < error := by
  apply Filter.eventually_all.mpr
  intro history
  have limit := rawModel.runBehavioralFrom_expect_tendsto
    ExecutionProtocol.FiniteTransitions.of_finite_history sequence profile converges
    payoff fuel history
  simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp limit) error positive

/-- Continue the actual original public-word posterior with the approximating
strategies or their limit. Their expectation difference tends to zero uniformly
over the entire original posterior, even when the public word has vanishing
initial probability. The posterior in both branches is literally the same. -/
theorem initial_public_continuation_error_tendsto
    (sequence : Nat → ∀ owner, rawModel.BehavioralPolicy owner)
    (profile : ∀ owner, rawModel.BehavioralPolicy owner)
    (converges : ∀ owner (site : rawModel.InformationSite owner),
      PMFConvergesPointwise (fun n => sequence n owner site.1) (profile owner site.1))
    (packets : Finset (Message Player app.Payload))
    (payoff : rawProtocol.History → ℝ) {bound : ℝ}
    (bounded : ∀ history, |payoff history| ≤ bound) (fuel : Nat) :
    let posterior := fun n => fiberPosterior (rawModel.runBehavioral (sequence n) 9)
      (fun history => (history.state.map fun current =>
        initialPublicPackets current.execution).getD ∅) packets
    Tendsto (fun n =>
      expect ((posterior n).bind (rawModel.runBehavioralFrom (sequence n) fuel)) payoff -
      expect ((posterior n).bind (rawModel.runBehavioralFrom profile fuel)) payoff)
      atTop (nhds 0) := by
  classical
  dsimp only
  let posterior := fun n => fiberPosterior (rawModel.runBehavioral (sequence n) 9)
    (fun history => (history.state.map fun current =>
      initialPublicPackets current.execution).getD ∅) packets
  change Tendsto (fun n =>
    expect ((posterior n).bind (rawModel.runBehavioralFrom (sequence n) fuel)) payoff -
    expect ((posterior n).bind (rawModel.runBehavioralFrom profile fuel)) payoff) atTop (nhds 0)
  apply Metric.tendsto_nhds.mpr
  intro error positive
  have uniform := native_continuation_uniform_limit sequence profile converges payoff fuel
    (error / 2) (by positivity)
  filter_upwards [uniform] with n close
  rw [Real.dist_eq, sub_zero,
    expect_bind_tower_bounded _ _ payoff bounded,
    expect_bind_tower_bounded _ _ payoff bounded]
  let difference := fun history : rawProtocol.History =>
    expect (rawModel.runBehavioralFrom (sequence n) fuel history) payoff -
      expect (rawModel.runBehavioralFrom profile fuel history) payoff
  have expectation :
      expect (posterior n)
        (fun history => expect (rawModel.runBehavioralFrom (sequence n) fuel history) payoff) -
      expect (posterior n)
        (fun history => expect (rawModel.runBehavioralFrom profile fuel history) payoff) =
      expect (posterior n) difference := by
    let := Fintype.ofFinite rawProtocol.History
    simp only [expect, tsum_fintype, difference, mul_sub, Finset.sum_sub_distrib]
  rw [expectation]
  have limited : |expect (posterior n) difference| ≤ error / 2 :=
    expect_abs_le_of_bounded (by positivity) (fun history => (close history).le)
  exact lt_of_le_of_lt limited (by linarith)

end Vegas.Examples.CommitSeedBroadcast
