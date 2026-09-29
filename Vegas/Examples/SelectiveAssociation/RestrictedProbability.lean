/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.SelectiveAssociation.RestrictedPrefix
import Vegas.Examples.SelectiveAssociation.RestrictedSymmetry
import Interaction.ReactiveAssessmentDecoding
import GameTheoryExtensions.Math.Probability.ConditionalComparison
import GameTheoryExtensions.Math.Probability.Support

/-! # Exact native prefix probabilities

Each tuple retains every earlier raw response. Its point probability is the
product of the three or four actual response probabilities. Common behavioral
perturbations decode to the same uniform mixtures used in these calculations.
-/

noncomputable section

namespace Vegas.Examples.SelectiveAssociation.Restricted.Prefix

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

theorem carol_probability (players : Player → app.Policy) (responses : CarolResponses) :
    ((carolLaw players) responses).toReal =
      ((players alice (initial.recall alice) (initial.observe app alice)) responses.alicePrelude).toReal *
        (((players bob ((bobPreludeInput responses.alicePrelude).recall bob)
          ((bobPreludeInput responses.alicePrelude).observe app bob)) responses.bobPrelude).toReal *
          ((players alice ((aliceInput responses.alicePrelude responses.bobPrelude).recall alice)
            ((aliceInput responses.alicePrelude responses.bobPrelude).observe app alice)) responses.aliceBinding).toReal) := by
  classical
  unfold carolLaw
  rw [FinDist.prob_bind_of_unique_branch _ _ responses responses.alicePrelude (by
    intro first _ reached
    obtain ⟨second, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
    obtain ⟨third, _, same⟩ := PMF.support_map .. ▸ reached
    exact congrArg CarolResponses.alicePrelude same)]
  congr 1
  rw [FinDist.prob_bind_of_unique_branch _ _ responses responses.bobPrelude (by
    intro second _ reached
    obtain ⟨third, _, same⟩ := PMF.support_map .. ▸ reached
    exact congrArg CarolResponses.bobPrelude same)]
  congr 1
  exact FinDist.prob_map_of_injective _ (fun _ _ same =>
    congrArg CarolResponses.aliceBinding same) _ responses.aliceBinding

theorem bob_probability (players : Player → app.Policy) (responses : BobResponses) :
    ((bobLaw players) responses).toReal =
      ((carolLaw players) responses.beforeCarol).toReal *
        ((players carol ((carolInput responses.beforeCarol).recall carol)
          ((carolInput responses.beforeCarol).observe app carol)) responses.carolBinding).toReal := by
  classical
  unfold bobLaw
  rw [FinDist.prob_bind_of_unique_branch _ _ responses responses.beforeCarol (by
    intro first _ reached
    obtain ⟨second, _, same⟩ := PMF.support_map .. ▸ reached
    exact congrArg BobResponses.beforeCarol same)]
  congr 1
  exact FinDist.prob_map_of_injective _ (fun _ _ same =>
    congrArg BobResponses.carolBinding same) _ responses.carolBinding

def mixed (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) :
    Player → app.Policy := fun who past view =>
  mix weight nonnegative atMostOne (menu.uniformResponses who past view)
    (policy who past view)

theorem decode_perturbed (weight : ℝ) (positive : 0 < weight) (atMostOne : weight ≤ 1) :
    menu.decodeProfile (PMF.pure nativeInitial) nativeHorizon scheduler
      (menu.perturbedAssessment (PMF.pure nativeInitial) nativeHorizon scheduler profile
        weight positive atMostOne).strategy = mixed weight positive.le atMostOne := by
  funext who past view
  rw [menu.decode_perturbedAssessment]
  have exactPolicy := menu.decode_restrictPolicy_of_covered (PMF.pure nativeInitial)
    nativeHorizon scheduler who (policy who)
      (policy_available who)
  change mix weight positive.le atMostOne _
    (app.decodePolicy (menu.embedPolicy (PMF.pure nativeInitial) nativeHorizon scheduler who
      (menu.restrictPolicy (PMF.pure nativeInitial) nativeHorizon scheduler who
        (policy who))) past view) = _
  rw [exactPolicy]
  rfl

/-- An action outside the prescribed point mass has only its uniform tremble
weight. Flipping it cannot decrease that weight when the known identifiers,
and therefore raw menu sizes, agree. -/
theorem mixed_flip_le (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (selected : Handle nativeGraph) (who : Player)
    (firstPast secondPast : List app.PlayerEntry) (firstView secondView : app.PlayerView)
    (same : (ReactiveApplication.ResponseMenu.knownPackets firstPast firstView).map Message.id =
      (ReactiveApplication.ResponseMenu.knownPackets secondPast secondView).map Message.id)
    (chosen : app.Action) (different : chosen ≠ response who firstView) :
    ((mixed weight nonnegative atMostOne who firstPast firstView) chosen).toReal ≤
      ((mixed weight nonnegative atMostOne who secondPast secondView) (CandidateFlip.action selected chosen)).toReal := by
  classical
  simp only [mixed, mix_apply_toReal, policy, FinDist.prob_pure_of_ne different,
    mul_zero, add_zero]
  rw [CandidateFlip.uniform_prob_of_known_ids selected who firstPast secondPast firstView
    secondView same chosen]
  exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr atMostOne)
    (ENNReal.toReal_nonneg))

theorem mixed_flip_silent (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (selected : Handle nativeGraph) (who : Player)
    (firstPast secondPast : List app.PlayerEntry) (firstView secondView : app.PlayerView)
    (same : (ReactiveApplication.ResponseMenu.knownPackets firstPast firstView).map Message.id =
      (ReactiveApplication.ResponseMenu.knownPackets secondPast secondView).map Message.id)
    (firstSilent : response who firstView = ⟨none⟩)
    (secondSilent : response who secondView = ⟨none⟩) (chosen : app.Action) :
    ((mixed weight nonnegative atMostOne who firstPast firstView) chosen).toReal =
      ((mixed weight nonnegative atMostOne who secondPast secondView) (CandidateFlip.action selected chosen)).toReal := by
  classical
  have silence : CandidateFlip.action selected chosen = (⟨none⟩ : app.Action) ↔
      chosen = ⟨none⟩ := by
    change CandidateFlip.action selected chosen = CandidateFlip.action selected ⟨none⟩ ↔ _
    exact (CandidateFlip.action_involutive selected).injective.eq_iff
  simp only [mixed, mix_apply_toReal, policy, firstSilent, secondSilent,
    toReal_pure_apply, silence]
  rw [CandidateFlip.uniform_prob_of_known_ids selected who firstPast secondPast firstView
    secondView same chosen]

end Vegas.Examples.SelectiveAssociation.Restricted.Prefix
