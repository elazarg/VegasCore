/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryEquilibriumConstruction

/-! # Extending a chosen intended equilibrium to proposal recovery

The intended assessment's consistency witness supplies the mixed Bayes
sequence. Its finite information masses determine positive perturbation rates
before the pooled completion is selected.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

open Classical in
/-- Every intended sequential equilibrium extends to proposal recovery,
preserving its entire initialized history law and its typed outcome/payoff law. -/
theorem exists_proposalRecovery_sequentialEquilibrium_extension
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed)
    (source : setup.intendedModel.BehavioralAssessment)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (below : ∀ terminal who, excludedPayoff who ≤ utility terminal who)
    (equilibrium : source.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories
      (fun who history => (setup.protocolReadout history.state).elim 0
        (fun terminal => utility terminal who))) :
    ∃ target : setup.proposalRecoveryModel.BehavioralAssessment,
      target.IsSequentialEquilibrium setup.proposalRecoveryModel_decisionAntichain
        setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
        (setup.proposalRecoveryPayoff utility excludedPayoff) ∧
      (setup.proposalRecoveryRestriction wellFormed).ExtendsProfile
        source.strategy target.strategy ∧
      (∀ fuel, (setup.intendedModel.runBehavioral source.strategy fuel).map
          (setup.proposalRecoveryIntendedLift wellFormed) =
        setup.proposalRecoveryModel.runBehavioral target.strategy fuel) ∧
      (∀ fuel, (setup.intendedModel.runBehavioral source.strategy fuel).map
          (fun history => (setup.protocolReadout history.state,
            fun who => (setup.protocolReadout history.state).elim 0
              (fun terminal => utility terminal who))) =
        (setup.proposalRecoveryModel.runBehavioral target.strategy fuel).map
          (fun history => (setup.protocolReadout (setup.commitRecoverySourceState history.state),
            fun who => setup.proposalRecoveryPayoff utility excludedPayoff who history))) := by
  classical
  let _ := setup.proposalRecovery_finite_history finite
  let _ := Fintype.ofFinite setup.proposalRecoveryProtocol.History
  let restriction := setup.proposalRecoveryRestriction wellFormed
  have : Finite setup.intendedProtocol.History :=
    Finite.of_injective restriction.history restriction.history.injective
  let _ := Fintype.ofFinite (Σ who, setup.intendedModel.InformationSite who)
  obtain ⟨sequence, approximates, converges⟩ := equilibrium.2
  let mass (n : ℕ) (entry : Σ who, setup.intendedModel.InformationSite who) : ℝ :=
    (setup.intendedModel.informationMass (sequence n).strategy entry.1 entry.2).toReal
  have massPositive (n : ℕ) (entry : Σ who, setup.intendedModel.InformationSite who) :
      0 < mass n entry :=
    ENNReal.toReal_pos
      (setup.intendedModel.informationMass_pos_of_fullSupport _
        (approximates n).1 entry.1 entry.2).ne'
      (ne_top_of_le_ne_top ENNReal.one_ne_top
        (setup.intendedModel.informationMass_le_one _ entry.1 entry.2
          (setup.intended_decision_antichain entry.1 entry.2)))
  let reach (n : ℕ) : ℝ := ∏ entry, min (1 : ℝ) (mass n entry)
  have reachPositive (n : ℕ) : 0 < reach n :=
    Finset.prod_pos fun entry _ => lt_min zero_lt_one (massPositive n entry)
  have reachBound (n : ℕ) (entry : Σ who, setup.intendedModel.InformationSite who) :
      reach n ≤ mass n entry := by
    have bound := Finset.prod_le_prod_of_subset_of_le_one₀
      (s := {entry}) (t := Finset.univ) (f := fun other => min (1 : ℝ) (mass n other))
      (Finset.subset_univ _) (fun other _ => (lt_min zero_lt_one (massPositive n other)).le)
      (fun other _ _ => min_le_left _ _)
    have single : reach n ≤ min (1 : ℝ) (mass n entry) := by
      simpa only [Finset.prod_singleton] using bound
    exact single.trans (min_le_right _ _)
  let rate := relativeTremble reach
  have positive := relativeTremble_pos reach reachPositive
  have small := relativeTremble_lt_one reach
  obtain ⟨_weights, _selected, target, _index, _mixed, _bayes, _increasing,
      _converges, _prescribed, _gains, rational, agrees, initialized, joint⟩ :=
    setup.exists_proposalRecovery_sequentialEquilibrium_construction finite wellFormed
      sequence source (fun n => (approximates n).1) (fun n => (approximates n).2) converges
      reach reachPositive (fun n who site => reachBound n ⟨who, site⟩)
      rate rate rate rate positive small positive small positive small positive small
      (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)
      utility excludedPayoff below equilibrium
  exact ⟨target, rational, agrees, initialized, joint⟩

end Vegas.SourceProgram.Setup
