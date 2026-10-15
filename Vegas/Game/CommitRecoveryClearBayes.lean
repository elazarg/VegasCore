/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryClearFiber
import GameTheoryExtensions.Analysis.Protocol.Bayes
import GameTheoryExtensions.Analysis.Protocol.PassageBayes

/-! # Actual auxiliary Bayes laws over clear source prefixes -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- Full mixing gives every genuine clear source prefix positive weight,
without restricting future omissions or replacing latent foreign choices. -/
theorem commitRecovery_clear_prefix_supported
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    (⟨state, trace⟩ : setup.commitRecoveryProtocol.History) ∈
      (setup.commitRecoveryModel.runBehavioral assessment.strategy trace.length).support :=
  mixed.history_supported trace

/-- The actual auxiliary Bayes law samples the source-ranked history at
genuine passage. The behavioral source runner retains repeated-owner choices,
their updated views and their separate physical omission flags. Only the
encountered prefix is clear; no later source omission is conditioned away. -/
theorem commitRecovery_clear_bayes_passage (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (bayes : assessment.IsBayesConsistent setup.commitRecoveryModel
      setup.commitRecoveryModel_decisionAntichain)
    (who : Player) (view : setup.ProtocolView who)
    (decision : setup.commitRecoveryModel.IsDecisionInfo who
      (setup.commitRecoveryClearInformation wellFormed who view)) :
    let site : setup.commitRecoveryModel.InformationSite who :=
      ⟨setup.commitRecoveryClearInformation wellFormed who view, decision⟩
    (assessment.belief who site).map some =
      fiberPosterior
        ((setup.commitRecoveryModel.runBehavioralTerminalFrom
          setup.commitRecoveryProtocol_bounded.wellFoundedHistories assessment.strategy
          setup.commitRecoveryProtocol.initHistory).map
            (site.ancestor? setup.commitRecoveryModel)) Option.isSome true := by
  intro site
  have positive := setup.commitRecoveryModel.informationMass_pos_of_fullSupport
    assessment.strategy mixed who site
  have belief := (InformationModel.BehavioralAssessment.isBayesConsistentAt_iff
    setup.commitRecoveryModel assessment who site
      (setup.commitRecoveryModel_decisionAntichain who site) positive).mp
        (bayes who site positive)
  rw [belief]
  exact site.bayesBelief_eq_conditional_ancestor setup.commitRecoveryModel
    (setup.commitRecoveryModel_decisionAntichain who site)
    setup.commitRecoveryProtocol_bounded.wellFoundedHistories assessment.strategy positive

end Vegas.SourceProgram.Setup
