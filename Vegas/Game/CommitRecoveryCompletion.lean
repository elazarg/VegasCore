/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryRetainedHistory
import Vegas.Game.CommitRecoveryReference
import GameTheoryExtensions.Analysis.Protocol.PassageRestrictionExtension
import GameTheory.Protocol.RestrictionExecution

/-! # Consistent source recovery completions retaining intended play -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

open Classical in
/-- One consistent assessment retains the original intended strategies and
beliefs and completes every new recovery information agent optimally. The
initialized history law is exact at every horizon. Rationality at retained
sites, including deviations using the enlarged menus, is a separate obligation. -/
theorem exists_consistent_commitRecovery_completion
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed)
    (source : setup.intendedModel.BehavioralAssessment)
    (consistent : source.IsSequentiallyConsistent setup.intended_decision_antichain)
    (payoff : Player → setup.commitRecoveryProtocol.History → ℝ) :
    ∃ target : setup.commitRecoveryModel.BehavioralAssessment,
      target.IsSequentiallyConsistent setup.commitRecoveryModel_decisionAntichain ∧
      (setup.commitRecoveryRestriction wellFormed).ExtendsProfile
        source.strategy target.strategy ∧
      (∀ who site, target.belief who ((setup.commitRecoveryRestriction wellFormed).site who site) =
        (source.belief who site).map
          ((setup.commitRecoveryRestriction wellFormed).informationHistory who site)) ∧
      (∀ who (site : setup.commitRecoveryModel.InformationSite who),
        ¬ (setup.commitRecoveryRestriction wellFormed).Retained who site.1 →
        ∀ law : PMF (setup.commitRecoveryModel.Choice who site.1),
          (target.continuationContext
              setup.commitRecoveryProtocol_bounded.wellFoundedHistories site (payoff who)).value
              ((target.strategy who).withLaw site.1 law) ≤
            (target.continuationContext
              setup.commitRecoveryProtocol_bounded.wellFoundedHistories site (payoff who)).value
              (target.strategy who)) ∧
      ∀ fuel, (setup.intendedModel.runBehavioral source.strategy fuel).map
          (setup.commitRecoveryLiftHistory wellFormed) =
        setup.commitRecoveryModel.runBehavioral target.strategy fuel := by
  classical
  let _ := setup.commitRecovery_finite_history finite
  let restriction := setup.commitRecoveryRestriction wellFormed
  have decisionMemory := setup.commitRecoveryModel.decisionRecall_of_perfectRecall
    setup.commitRecoveryModel_perfectRecall
  obtain ⟨target, targetConsistent, agrees, beliefs, optimal⟩ :=
    restriction.exists_consistent_extension_unclocked source
      setup.intended_decision_antichain consistent
      (setup.commitRecoveryReference finite) (setup.commitRecoveryReference_fullyMixed finite)
      decisionMemory setup.commitRecoveryProtocol_bounded.wellFoundedHistories payoff
  refine ⟨target, targetConsistent, agrees, beliefs, optimal, ?_⟩
  exact fun fuel => restriction.initialized_law source.strategy target.strategy agrees fuel

end Vegas.SourceProgram.Setup
