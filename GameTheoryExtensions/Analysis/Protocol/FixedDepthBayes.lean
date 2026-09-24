/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.Bayes

/-! # Bayes beliefs at a fixed decision depth

When all histories in an information fiber have the same trace length, its
reach mass is an ordinary event probability at that depth. The existing Bayes
belief, embedded into complete histories, is exactly the behavioral history
law conditioned on that information event.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] {E : ExecutionProtocol Player}
  (M : InformationModel E) [Finite E.History]
  (strategy : ∀ who, M.BehavioralPolicy who) (who : Player) (site : M.InformationSite who)
  [Fintype (M.InformationHistory who site.1)]
  (depth : Nat) (sameDepth : ∀ history : M.InformationHistory who site.1,
    history.1.trace.length = depth)

include sameDepth in
theorem informationMass_eq_fixedDepth_probOf :
    M.informationMass strategy who site =
      (M.runBehavioral strategy depth).probOf {history | M.infoOf who history.trace = site.1} := by
  classical
  let := Fintype.ofFinite E.History
  rw [← FinDist.expect_indicator_eq_probOf, FinDist.expect_eq_sum]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype _ (p := fun history => M.infoOf who history.trace = site.1)
    (by intro history; simp) _]
  · unfold informationMass
    apply Finset.sum_congr rfl
    intro history _
    rw [historyReachProbability, sameDepth history]

include sameDepth in
theorem bayesBelief_map_eq_condOn (antichain : site.IsHistoryAntichain)
    (positive : 0 < M.informationMass strategy who site)
    (meet : ∃ history ∈ {history | M.infoOf who history.trace = site.1},
      history ∈ (M.runBehavioral strategy depth).support) :
    (M.bayesBelief strategy who site antichain positive).map Subtype.val =
      (M.runBehavioral strategy depth).condOn
        {history | M.infoOf who history.trace = site.1} meet := by
  classical
  apply FinDist.ext_of_prob
  intro history
  by_cases observed : M.infoOf who history.trace = site.1
  · let compatible : M.InformationHistory who site.1 := ⟨history, observed⟩
    have mapped := FinDist.prob_map_of_injective
      (Subtype.val : M.InformationHistory who site.1 → E.History) Subtype.val_injective
      (M.bayesBelief strategy who site antichain positive) compatible
    rw [mapped, M.bayesBelief_prob, FinDist.prob_condOn,
      ite_eq_left (show history ∈ {history | M.infoOf who history.trace = site.1} from observed),
      M.informationMass_eq_fixedDepth_probOf strategy who site depth sameDepth]
    rw [historyReachProbability, sameDepth compatible]
  · rw [FinDist.prob_condOn,
      ite_eq_right (show history ∉ {history | M.infoOf who history.trace = site.1} from observed)]
    apply FinDist.prob_eq_zero_iff.mpr
    rw [FinDist.support_map]
    rintro ⟨compatible, _, same⟩
    exact observed (same ▸ compatible.2)

end GameTheory.Protocol.InformationModel
