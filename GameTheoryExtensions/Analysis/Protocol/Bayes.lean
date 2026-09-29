/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.BehavioralBayes
import GameTheory.Protocol.Predraw
import GameTheoryExtensions.Math.Probability.Support

/-! # Full mixing reaches every legal decision history

Full support is required only at legal decision sites. Inactive players have
singleton menus. Thus every complete legal history is in the support of play.
The canonical Bayes assessment of a fully mixed strategy is upstream's
`bayesAssessment`.
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
      rw [eq_pure_of_subsingleton
        (assessment.strategy who (M.infoOf who history.trace)) choice]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
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
  | _, .start => (PMF.mem_support_pure_iff _ _).mpr rfl
  | _, .extend (source := before) prior joint legal realized => by
      change _ ∈ (M.runBehavioralFrom assessment.strategy (prior.length + 1)
        E.initHistory).support
      rw [M.runBehavioralFrom_add, PMF.support_bind]
      refine Set.mem_iUnion₂.mpr ⟨⟨before, prior⟩, mixed.history_supported prior, ?_⟩
      rw [M.runBehavioralFrom_succ_of_not_terminal _ 0 legal.1,
        PMF.support_bind]
      refine Set.mem_iUnion₂.mpr ⟨⟨joint, legal⟩, ?_, ?_⟩
      · exact M.mem_support_behavioralJoint assessment.strategy prior legal.1 joint legal
          (fun who => mixed.support_at_history ⟨before, prior⟩ legal.1 who _)
      · rw [PMF.support_bindOnSupport]
        exact Set.mem_iUnion₂.mpr ⟨_, realized, (PMF.mem_support_pure_iff _ _).mpr rfl⟩

/-- Every legal terminal history remains supported when evaluation is padded
to any larger horizon. No particular equilibrium needs to reach that history. -/
theorem BehavioralAssessment.IsFullyMixed.terminal_supported
    {assessment : M.BehavioralAssessment} (mixed : assessment.IsFullyMixed)
    (history : E.History) (terminal : E.terminal history.state)
    (fuel : Nat) (enough : history.trace.length ≤ fuel) :
    history ∈ (M.runBehavioral assessment.strategy fuel).support := by
  rw [show fuel = history.trace.length + (fuel - history.trace.length) by omega]
  change history ∈ (M.runBehavioralFrom assessment.strategy _ E.initHistory).support
  rw [M.runBehavioralFrom_add, PMF.support_bind]
  refine Set.mem_iUnion₂.mpr ⟨history, mixed.history_supported history.trace, ?_⟩
  rw [M.runBehavioralFrom_of_terminal assessment.strategy _ terminal]
  exact (PMF.mem_support_pure_iff _ _).mpr rfl

omit [Fintype ι] in
/-- A bounded protocol admitting full mixing has only finitely many legal
histories when its choices and transitions branch finitely, even when its
ambient state carrier is infinite. -/
theorem BehavioralAssessment.IsFullyMixed.finite_history
    [Finite ι]
    {assessment : M.BehavioralAssessment} (mixed : assessment.IsFullyMixed)
    {bound : Nat} (bounded : E.BoundedHorizon bound)
    (finiteChoices : ∀ who info, (assessment.strategy who info).support.Finite)
    (finiteSteps : ∀ {state : E.State}
      (draw : { joint : ∀ i, Option (E.Action i) // E.Legal state joint }),
      (E.step state draw).support.Finite) : Finite E.History := by
  classical
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
    M.runBehavioralFrom_support_finite_of_finite_branching assessment.strategy index.val
      E.initHistory (fun history _ who => finiteChoices who _) finiteSteps
  apply Set.finite_univ_iff.mp
  apply cover.subset
  intro history _
  exact Set.mem_iUnion.mpr ⟨⟨history.trace.length, by have := lengths history; omega⟩,
    mixed.history_supported history.trace⟩

/-- The canonical Bayes assessment of a fully mixed strategy is fully mixed. -/
theorem bayesAssessment_isFullyMixed (strategy : (who : ι) → M.BehavioralPolicy who)
    (mixed : ∀ who (site : M.InformationSite who) (choice : M.Choice who site.1),
      choice ∈ (strategy who site.1).support)
    (antichain : M.DecisionInformationAntichain) :
    (M.bayesAssessment strategy mixed antichain).IsFullyMixed :=
  mixed

end GameTheory.Protocol.InformationModel
