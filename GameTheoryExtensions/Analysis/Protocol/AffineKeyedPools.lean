/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.FreeKeyedPools

/-! # Common keyed parts from affine payoff scores -/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {T : ExecutionProtocol Player} {N : InformationModel T}
  [∀ who, DecidableEq (N.InfoState who)] [Fintype T.History]
  {Outcome Key : Type*} {Opt : Type} [Finite Opt] [Nonempty Opt]

open Classical in
/-- A common scalar score orders the original pooled components when their
actual payoffs are affine in that score, up to an error. This formulation
requires no identification of a terminal failure event with a reference law. -/
theorem freeKeyed_memberGain_le_of_common_values
    (fuel : Nat) (bounded : T.BoundedHorizon fuel) (decisionRecall : N.DecisionRecall)
    (observe : T.History → Outcome) (utility : Outcome → Player → ℝ)
    (fallback : ∀ who, N.Policy who)
    (free keyed : N.InformationAgent N.playedInformation → Prop)
    (key : N.InformationAgent N.playedInformation → Key)
    (indifferent : N.InformationAgent N.playedInformation → Prop)
    (freeLaw : ∀ agent : N.InformationAgent N.playedInformation,
      N.Choice agent.1 agent.2.1 → PMF (N.Choice agent.1 agent.2.1))
    (prescribed : ∀ agent : N.InformationAgent N.playedInformation,
      PMF (N.Choice agent.1 agent.2.1))
    (keyedLaw : ∀ agent : N.InformationAgent N.playedInformation,
      Opt → PMF (N.Choice agent.1 agent.2.1))
    (weights : ∀ p, PMF (FreeKeyedPart free keyed key Opt p))
    (assessment : N.BehavioralAssessment)
    (played : assessment.strategy = N.agentBehavior N.playedInformation fallback
      fun agent => (weights (freeKeyedPool free keyed key agent)).bind
        (freeKeyedComponent freeLaw prescribed keyedLaw agent))
    (pooled : ∀ (alternative : ∀ p, PMF (FreeKeyedPart free keyed key Opt p)) p,
      ∑ agent ∈ Finset.univ.filter (fun agent => freeKeyedPool free keyed key agent = p),
        (if decision : N.IsDecisionInfo agent.1 agent.2.1 then
          localGain fuel observe utility assessment (who := agent.1) ⟨agent.2.1, decision⟩
            ((alternative (freeKeyedPool free keyed key agent)).bind
              (freeKeyedComponent freeLaw prescribed keyedLaw agent)) else 0) ≤ 0)
    (excluded : Player → ℝ)
    (noGain : ∀ who (site : N.InformationSite who), indifferent (N.agentAt site) → ∀ law,
      localGain fuel observe utility assessment site law = 0)
    (continuation : N.InformationAgent N.playedInformation → ℝ)
    (score : Key → Opt → ℝ) (error : ℝ)
    (values : ∀ agent : N.InformationAgent N.playedInformation,
      ownedKeyed free keyed agent → ¬ indifferent agent →
      ∀ decision : N.IsDecisionInfo agent.1 agent.2.1,
        excluded agent.1 ≤ continuation agent ∧ ∀ option,
        |localValue fuel observe utility assessment (who := agent.1) ⟨agent.2.1, decision⟩
            (keyedLaw agent option) -
          (excluded agent.1 + score (key agent) option *
            (continuation agent - excluded agent.1))| ≤ error) :
    ∀ who (site : N.InformationSite who), ownedKeyed free keyed (N.agentAt site) →
      ∀ alternative : PMF (FreeKeyedPart free keyed key Opt
        (freeKeyedPool free keyed key (N.agentAt site))),
      localGain fuel observe utility assessment site
        (alternative.bind (freeKeyedComponent freeLaw prescribed keyedLaw (N.agentAt site))) ≤
        Fintype.card (N.InformationAgent N.playedInformation) * (2 * max error 0) := by
  let := Fintype.ofFinite Opt
  let best := freeKeyedBest free keyed key Opt (fun k => scoreArgmax (score k))
  let cost := 2 * max error 0
  have costNonneg : 0 ≤ cost := mul_nonneg (by norm_num) (le_max_right _ _)
  intro who site siteKeyed alternative
  have nearBest : ∀ agent : N.InformationAgent N.playedInformation,
      freeKeyedPool free keyed key agent = freeKeyedPool free keyed key (N.agentAt site) →
      ∀ (decision : N.IsDecisionInfo agent.1 agent.2.1)
        (part : FreeKeyedPart free keyed key Opt (freeKeyedPool free keyed key agent)),
      localGain fuel observe utility assessment (who := agent.1) ⟨agent.2.1, decision⟩
          (freeKeyedComponent freeLaw prescribed keyedLaw agent part) ≤
        localGain fuel observe utility assessment (who := agent.1) ⟨agent.2.1, decision⟩
          (freeKeyedComponent freeLaw prescribed keyedLaw agent
            (best (freeKeyedPool free keyed key agent))) + cost := by
    intro agent samePool decision part
    have poolEq := samePool.trans (freeKeyedPool_of_not_free siteKeyed.2)
    have notFree : ¬ free agent := by
      intro isFree
      rw [freeKeyedPool_of_free isFree] at poolEq
      cases poolEq
    have isKeyed : ownedKeyed free keyed agent := by
      rw [freeKeyedPool_of_not_free notFree] at poolEq
      apply (isSome_keyedPool_iff agent).mp
      rw [Sum.inr.inj poolEq]
      exact (isSome_keyedPool_iff (N.agentAt site)).mpr siteKeyed
    by_cases noIncentive : indifferent agent
    · have ownAgent : N.agentAt (⟨agent.2.1, decision⟩ : N.InformationSite agent.1) = agent := rfl
      have noGainAgent : indifferent (N.agentAt
          (⟨agent.2.1, decision⟩ : N.InformationSite agent.1)) := by
        rw [ownAgent]
        exact noIncentive
      rw [noGain _ _ noGainAgent, noGain _ _ noGainAgent]
      simpa only [zero_add] using costNonneg
    obtain ⟨lower, approximate⟩ := values agent isKeyed noIncentive decision
    obtain ⟨identify, componentEq⟩ := freeKeyedComponent_of_not_free (key := key)
      freeLaw prescribed keyedLaw notFree
    have bestLaw := freeKeyedComponent_at_not_free freeLaw prescribed keyedLaw best notFree
    rw [show best (.inr (keyedPool (ownedKeyed free keyed) key agent)) =
        keyedBest (fun k => scoreArgmax (score k))
          (keyedPool (ownedKeyed free keyed) key agent) from rfl,
      keyedComponent_best_of_keyed prescribed keyedLaw _ isKeyed] at bestLaw
    obtain ⟨option, optionLaw⟩ := keyedComponent_of_keyed (key := key) prescribed keyedLaw isKeyed
      (identify part)
    rw [bestLaw, componentEq, optionLaw, localGain_eq_sub, localGain_eq_sub]
    have chosenNear := abs_le.mp (approximate option)
    have bestNear := abs_le.mp (approximate (scoreArgmax (score (key agent))))
    have ordered := mul_le_mul_of_nonneg_right (le_scoreArgmax (score (key agent)) option)
      (sub_nonneg.mpr lower)
    have nonnegative : error ≤ max error 0 := le_max_left _ _
    dsimp only [cost]
    linarith
  exact memberGain_le_of_common_best fuel bounded observe utility fallback
    (freeKeyedPool free keyed key) decisionRecall.actsOnceWhereItMatters
    (freeKeyedComponent freeLaw prescribed keyedLaw) weights assessment played pooled
    (freeKeyedPool free keyed key (N.agentAt site)) best cost nearBest who site rfl alternative

end GameTheory.Protocol.InformationModel
