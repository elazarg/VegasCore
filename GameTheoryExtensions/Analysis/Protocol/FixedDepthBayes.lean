/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.Bayes
import GameTheoryExtensions.Analysis.Protocol.BehavioralContinuity
import GameTheoryExtensions.Math.Probability.Conditioning
import GameTheoryExtensions.Math.Probability.Support

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
  (M : InformationModel E)
  (strategy : ∀ who, M.BehavioralPolicy who) (who : Player) (site : M.InformationSite who)
  (depth : Nat) (sameDepth : ∀ history : M.InformationHistory who site.1,
    history.1.trace.length = depth)

include sameDepth in
theorem informationMass_eq_fixedDepth_toOuterMeasure :
    M.informationMass strategy who site =
      (M.runBehavioral strategy depth).toOuterMeasure
        {history | M.infoOf who history.trace = site.1} := by
  unfold informationMass
  rw [PMF.toOuterMeasure_apply]
  rw [← tsum_subtype {history : E.History | M.infoOf who history.trace = site.1}
    (M.runBehavioral strategy depth)]
  exact tsum_congr fun history => by rw [historyReachWeight, sameDepth history]

include sameDepth in
theorem bayesBelief_map_eq_filter (antichain : site.IsHistoryAntichain)
    (positive : 0 < M.informationMass strategy who site)
    (meet : ∃ history ∈ {history | M.infoOf who history.trace = site.1},
      history ∈ (M.runBehavioral strategy depth).support) :
    (M.bayesBelief strategy who site antichain positive).map Subtype.val =
      (M.runBehavioral strategy depth).filter
        {history | M.infoOf who history.trace = site.1} meet := by
  classical
  ext history
  rw [PMF.filter_apply, ← PMF.toOuterMeasure_apply,
    ← M.informationMass_eq_fixedDepth_toOuterMeasure strategy who site depth sameDepth]
  by_cases observed : M.infoOf who history.trace = site.1
  · let compatible : M.InformationHistory who site.1 := ⟨history, observed⟩
    rw [pmf_map_apply_of_injective _ Subtype.val_injective compatible, M.bayesBelief_apply,
      Set.indicator_of_mem (show history ∈ {history | M.infoOf who history.trace = site.1}
        from observed), historyReachWeight, sameDepth compatible, div_eq_mul_inv]
  · rw [Set.indicator_of_notMem (show history ∉ {history | M.infoOf who history.trace = site.1}
      from observed), zero_mul, PMF.apply_eq_zero_iff, PMF.support_map]
    rintro ⟨compatible, _, same⟩
    exact observed (same ▸ compatible.2)

/-- If every run at a common decision depth reaches this information set,
its consistent belief is the unconditioned history law at that depth. -/
theorem BehavioralAssessment.belief_map_eq_run_of_full_reach
    [∀ player (decision : M.InformationSite player),
      Finite (M.InformationHistory player decision.1)]
    (assessment : M.BehavioralAssessment) (antichain : M.DecisionInformationAntichain)
    (consistent : assessment.IsSequentiallyConsistent antichain)
    (sameDepth : ∀ history : M.InformationHistory who site.1,
      history.1.trace.length = depth)
    (seen : ∀ history ∈ (M.runBehavioral assessment.strategy depth).support,
      M.infoOf who history.trace = site.1) :
    (assessment.belief who site).map Subtype.val =
      M.runBehavioral assessment.strategy depth := by
  classical
  let law := M.runBehavioral assessment.strategy depth
  let information : Set E.History := {history | M.infoOf who history.trace = site.1}
  have mass : law.toOuterMeasure information = 1 :=
    (PMF.toOuterMeasure_apply_eq_one_iff law information).mpr fun history supported =>
      seen history supported
  have informationMass : M.informationMass assessment.strategy who site = 1 :=
    (M.informationMass_eq_fixedDepth_toOuterMeasure assessment.strategy who site depth
      sameDepth).trans mass
  have positive : 0 < M.informationMass assessment.strategy who site := by
    rw [informationMass]
    exact one_pos
  obtain ⟨witness, supported⟩ := law.support_nonempty
  have meet : ∃ history ∈ information, history ∈ law.support :=
    ⟨witness, seen witness supported, supported⟩
  have bayes : assessment.belief who site =
      M.bayesBelief assessment.strategy who site (antichain who site) positive := by
    ext history
    rw [M.bayesBelief_apply]
    exact consistent.isBayesConsistent antichain who site positive history
  have conditioned := M.bayesBelief_map_eq_filter assessment.strategy who site depth
    sameDepth (antichain who site) positive meet
  rw [← bayes] at conditioned
  have unchanged : law.filter information meet = law := by
    ext history
    rw [PMF.filter_apply, ← PMF.toOuterMeasure_apply, mass, inv_one, mul_one]
    by_cases member : history ∈ information
    · rw [Set.indicator_of_mem member]
    · rw [Set.indicator_of_notMem member]
      exact ((PMF.apply_eq_zero_iff law history).mpr fun supported =>
        member (seen history supported)).symm
  exact conditioned.trans unchanged

end GameTheory.Protocol.InformationModel
