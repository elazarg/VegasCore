/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryBayes
import Vegas.Game.ProposalRecoveryContinuation

/-! # Actual Bayes-sampled enriched source continuation laws -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- Exact full-fiber Bayes exchange followed by the original stopped runner.
Future play may use every control and the complete canonical proposal archive. -/
theorem proposalRecovery_bayes_stopped_eq
    (finite : setup.program.FiniteBindingTypes)
    (beliefProfile : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (mixed : ∀ who (site : setup.proposalRecoveryModel.InformationSite who) choice,
      choice ∈ (beliefProfile who site.1).support)
    (profile : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (normalized : ∀ who first second,
      setup.proposalRecoveryQuery who first = setup.proposalRecoveryQuery who second →
        (profile who first).map Subtype.val = (profile who second).map Subtype.val)
    (certificate : setup.proposalRecoveryProtocol.WellFoundedHistories)
    (stopped : setup.ProposalRecoveryHistoryImage → Prop)
    (focal : Player) (target source : setup.proposalRecoveryModel.InformationSite focal)
    (semantic : setup.commitRecoveryErasedInformation focal
        (setup.proposalRecoveryEraseInfo focal target.1) =
      setup.commitRecoveryErasedInformation focal (setup.proposalRecoveryEraseInfo focal source.1))
    (archive : setup.proposalRecoveryArchive focal target.1 =
      setup.proposalRecoveryArchive focal source.1) :
    ((setup.proposalRecoveryModel.bayesBelief beliefProfile focal source
        (setup.proposalRecoveryModel_decisionAntichain focal source)
        (setup.proposalRecoveryModel.informationMass_pos_of_fullSupport
          beliefProfile mixed focal source)).bind fun history =>
      setup.proposalRecoveryModel.runBehavioralUntil certificate profile
        (stopped ∘ setup.proposalRecoveryErasedHistory) history.1).map
          setup.proposalRecoveryErasedHistory =
      ((setup.proposalRecoveryModel.bayesBelief beliefProfile focal target
        (setup.proposalRecoveryModel_decisionAntichain focal target)
        (setup.proposalRecoveryModel.informationMass_pos_of_fullSupport
          beliefProfile mixed focal target)).bind fun history =>
      setup.proposalRecoveryModel.runBehavioralUntil certificate profile
        (stopped ∘ setup.proposalRecoveryErasedHistory) history.1).map
          setup.proposalRecoveryErasedHistory := by
  obtain ⟨exchange, exchangeSpec, bayes⟩ :=
    setup.proposalRecovery_bayes_eq_of_erased_information_archive finite beliefProfile mixed
      focal target source semantic archive
  rw [PMF.map_bind, PMF.map_bind]
  have rewritten := congrArg (fun law => law.bind fun history :
      setup.proposalRecoveryModel.InformationHistory focal target.1 =>
        (setup.proposalRecoveryModel.runBehavioralUntil certificate profile
          (stopped ∘ setup.proposalRecoveryErasedHistory) history.1).map
            setup.proposalRecoveryErasedHistory) bayes
  rw [PMF.bind_map] at rewritten
  rw [← rewritten]
  apply congrArg (PMF.bind _)
  funext history
  exact setup.proposalRecovery_runUntil_erased_eq profile normalized certificate stopped
    history.1 (exchange history).1 (exchangeSpec history).2.2.symm

/-- The same actual belief exchange preserves the complete terminal image,
including semantic fields that arbitrary terminal utilities may read. -/
theorem proposalRecovery_bayes_terminal_eq
    (finite : setup.program.FiniteBindingTypes)
    (beliefProfile : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (mixed : ∀ who (site : setup.proposalRecoveryModel.InformationSite who) choice,
      choice ∈ (beliefProfile who site.1).support)
    (profile : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (normalized : ∀ who first second,
      setup.proposalRecoveryQuery who first = setup.proposalRecoveryQuery who second →
        (profile who first).map Subtype.val = (profile who second).map Subtype.val)
    (certificate : setup.proposalRecoveryProtocol.WellFoundedHistories)
    (focal : Player) (target source : setup.proposalRecoveryModel.InformationSite focal)
    (semantic : setup.commitRecoveryErasedInformation focal
        (setup.proposalRecoveryEraseInfo focal target.1) =
      setup.commitRecoveryErasedInformation focal (setup.proposalRecoveryEraseInfo focal source.1))
    (archive : setup.proposalRecoveryArchive focal target.1 =
      setup.proposalRecoveryArchive focal source.1) :
    ((setup.proposalRecoveryModel.bayesBelief beliefProfile focal source
        (setup.proposalRecoveryModel_decisionAntichain focal source)
        (setup.proposalRecoveryModel.informationMass_pos_of_fullSupport
          beliefProfile mixed focal source)).bind fun history =>
      setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate profile history.1).map
          setup.proposalRecoveryErasedHistory =
      ((setup.proposalRecoveryModel.bayesBelief beliefProfile focal target
        (setup.proposalRecoveryModel_decisionAntichain focal target)
        (setup.proposalRecoveryModel.informationMass_pos_of_fullSupport
          beliefProfile mixed focal target)).bind fun history =>
      setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate profile history.1).map
          setup.proposalRecoveryErasedHistory := by
  obtain ⟨exchange, exchangeSpec, bayes⟩ :=
    setup.proposalRecovery_bayes_eq_of_erased_information_archive finite beliefProfile mixed
      focal target source semantic archive
  rw [PMF.map_bind, PMF.map_bind]
  have rewritten := congrArg (fun law => law.bind fun history :
      setup.proposalRecoveryModel.InformationHistory focal target.1 =>
        (setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate profile history.1).map
          setup.proposalRecoveryErasedHistory) bayes
  rw [PMF.bind_map] at rewritten
  rw [← rewritten]
  apply congrArg (PMF.bind _)
  funext history
  exact setup.proposalRecovery_terminal_erased_eq profile normalized certificate
    history.1 (exchange history).1 (exchangeSpec history).2.2.symm

end Vegas.SourceProgram.Setup
