/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.Sequential

/-! # Full mixing reaches every legal decision history

Full support is required only at legal decision sites. Inactive players have
singleton menus. Thus every complete legal history has positive reach mass,
and finite information fibers admit canonical Bayes beliefs without fallbacks.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol

variable {ι : Type} {E : ExecutionProtocol ι} {M : InformationModel E}

theorem BehavioralAssessment.IsFullyMixed.support_at_history
    {assessment : M.BehavioralAssessment} (mixed : assessment.IsFullyMixed)
    (history : E.History) (running : ¬ E.terminal history.state)
    (who : ι) (choice : M.Choice who (M.infoOf who history.trace)) :
    choice ∈ (assessment.strategy who (M.infoOf who history.trace)).support := by
  cases value : choice.val with
  | none =>
      have inactive : ¬ E.active history.state who := by
        have legal := (M.menu_adequate who history.trace choice.val).mp choice.property
        simpa only [value, LegalOption] using legal
      let := M.subsingleton_choice_of_not_active history.trace inactive
      rw [FinDist.eq_pure_of_subsingleton
        (assessment.strategy who (M.infoOf who history.trace)) choice]
      exact FinDist.mem_support_pure.mpr rfl
  | some action =>
      have legal : some action ∈ M.menu who (M.infoOf who history.trace) :=
        value ▸ choice.property
      exact mixed who (M.informationSite who history action running legal) choice

variable [Fintype ι]

theorem BehavioralAssessment.IsFullyMixed.history_supported
    {assessment : M.BehavioralAssessment} (mixed : assessment.IsFullyMixed) :
    ∀ {state} (trace : E.Trace state),
      (⟨state, trace⟩ : E.History) ∈
        (M.runBehavioral assessment.strategy trace.length).support
  | _, .start => FinDist.mem_support_pure.mpr rfl
  | _, .extend (source := before) prior joint legal realized => by
      change _ ∈ (M.runBehavioralFrom assessment.strategy (prior.length + 1)
        E.initHistory).support
      rw [M.runBehavioralFrom_add, FinDist.support_bind]
      refine Set.mem_iUnion₂.mpr ⟨⟨before, prior⟩, mixed.history_supported prior, ?_⟩
      rw [M.runBehavioralFrom_succ_of_not_terminal _ 0 legal.1,
        FinDist.support_bind]
      refine Set.mem_iUnion₂.mpr ⟨⟨joint, legal⟩, ?_, ?_⟩
      · exact M.mem_support_behavioralJoint assessment.strategy prior legal.1 joint legal
          (fun who => mixed.support_at_history ⟨before, prior⟩ legal.1 who _)
      · rw [FinDist.support_bindOnSupport]
        exact Set.mem_iUnion₂.mpr ⟨_, realized, FinDist.mem_support_pure.mpr rfl⟩

theorem BehavioralAssessment.IsFullyMixed.historyReachProbability_pos
    {assessment : M.BehavioralAssessment} (mixed : assessment.IsFullyMixed)
    (history : E.History) : 0 < M.historyReachProbability assessment.strategy history :=
  FinDist.prob_pos_iff.mpr (mixed.history_supported history.trace)

theorem BehavioralAssessment.IsFullyMixed.informationMass_pos
    {assessment : M.BehavioralAssessment} (mixed : assessment.IsFullyMixed)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)] :
    0 < M.informationMass assessment.strategy who site := by
  classical
  obtain ⟨history, _⟩ := site.2
  apply lt_of_lt_of_le (mixed.historyReachProbability_pos history.1)
  exact Finset.single_le_sum
    (f := fun other : M.InformationHistory who site.1 =>
      M.historyReachProbability assessment.strategy other.1)
    (fun other _ => FinDist.prob_nonneg _ _) (Finset.mem_univ history)

omit [Fintype ι] in
/-- A bounded protocol admitting full mixing has only finitely many legal
histories, even when its ambient state carrier is infinite. -/
theorem BehavioralAssessment.IsFullyMixed.finite_history
    [Finite ι]
    {assessment : M.BehavioralAssessment} (mixed : assessment.IsFullyMixed)
    {bound : Nat} (bounded : E.BoundedHorizon bound) : Finite E.History := by
  let : Fintype ι := Fintype.ofFinite _
  have lengths : ∀ history : E.History, history.trace.length ≤ bound := by
    intro ⟨state, trace⟩
    cases trace with
    | start => exact Nat.zero_le _
    | extend prior joint legal realized =>
        have before : prior.length < bound := by
          by_contra tooLong
          exact legal.1 (bounded _ prior (by omega))
        exact Nat.succ_le_of_lt before
  have cover := Set.finite_iUnion fun index : Fin (bound + 1) =>
    (M.runBehavioral assessment.strategy index.val).support_finite
  apply Set.finite_univ_iff.mp
  apply cover.subset
  intro history _
  exact Set.mem_iUnion.mpr ⟨⟨history.trace.length, by have := lengths history; omega⟩,
    mixed.history_supported history.trace⟩

variable [∀ who (site : M.InformationSite who),
  Fintype (M.InformationHistory who site.1)]

/-- Normalize actual reach probabilities at every site of a fully mixed
profile. The input assessment contributes only its strategy, not its beliefs. -/
def BehavioralAssessment.bayes (assessment : M.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) (antichain : M.DecisionInformationAntichain) :
    M.BehavioralAssessment where
  strategy := assessment.strategy
  belief who site := M.bayesBelief assessment.strategy who site (antichain who site)
    (mixed.informationMass_pos who site)

theorem BehavioralAssessment.bayes_isFullyMixed (assessment : M.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) (antichain : M.DecisionInformationAntichain) :
    (assessment.bayes mixed antichain).IsFullyMixed := mixed

theorem BehavioralAssessment.bayes_isBayesConsistent (assessment : M.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) (antichain : M.DecisionInformationAntichain) :
    BehavioralAssessment.IsBayesConsistent M (assessment.bayes mixed antichain) antichain := by
  intro who site _ history
  exact M.bayesBelief_prob assessment.strategy who site (antichain who site)
    (mixed.informationMass_pos who site) history

end GameTheory.Protocol.InformationModel
