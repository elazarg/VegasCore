/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.Bayes
import GameTheoryExtensions.Analysis.Protocol.BehavioralContinuity

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

omit [Fintype (M.InformationHistory who site.1)] in
/-- If every run at a common decision depth reaches this information set,
its consistent belief is the unconditioned history law at that depth. -/
theorem BehavioralAssessment.belief_map_eq_run_of_full_reach
    [∀ player (decision : M.InformationSite player),
      Fintype (M.InformationHistory player decision.1)]
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
  have mass : law.probOf information = 1 := by
    rw [← FinDist.expect_indicator_eq_probOf]
    calc
      law.expect (fun history => if history ∈ information then (1 : ℝ) else 0) =
          law.expect (fun _ => 1) := by
        apply FinDist.expect_congr
        intro history supported
        rw [ite_eq_left (show history ∈ information from seen history supported)]
      _ = 1 := FinDist.expect_const _ _
  have informationMass : M.informationMass assessment.strategy who site = 1 :=
    (M.informationMass_eq_fixedDepth_probOf assessment.strategy who site depth sameDepth).trans mass
  have positive : 0 < M.informationMass assessment.strategy who site := by
    rw [informationMass]
    norm_num
  obtain ⟨witness, supported⟩ := law.support_nonempty
  have meet : ∃ history ∈ information, history ∈ law.support :=
    ⟨witness, seen witness supported, supported⟩
  have bayes : assessment.belief who site =
      M.bayesBelief assessment.strategy who site (antichain who site) positive := by
    apply FinDist.ext_of_prob
    intro history
    rw [M.bayesBelief_prob]
    exact consistent.isBayesConsistent antichain who site positive history
  have conditioned := M.bayesBelief_map_eq_condOn assessment.strategy who site depth
    sameDepth (antichain who site) positive meet
  rw [← bayes] at conditioned
  have unchanged : law.condOn information meet = law := by
    apply FinDist.ext_of_prob
    intro history
    rw [FinDist.prob_condOn, mass, div_one]
    by_cases member : history ∈ information
    · rw [ite_eq_left member]
    · rw [ite_eq_right member]
      exact (FinDist.prob_eq_zero_iff.mpr fun supported => member (seen history supported)).symm
  exact conditioned.trans unchanged

end GameTheory.Protocol.InformationModel
