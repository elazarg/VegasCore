/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryClearBayes
import Vegas.Game.PhaseBindingCounterpart

/-! # Source Bayes prefix laws at actual clear native binding callbacks -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- An actual initialized clear binding callback determines a positive-mass
auxiliary source decision site. Its Bayes belief is the original source runner's
conditional ancestor law, including all earlier latent foreign binding choices.
The theorem does not identify that source law with native history weights. -/
theorem phase_ready_binding_bayes_prefix
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (ready : control.execution.application.current.native.config.cut.Ready event)
    (clear : control.execution.application.current.excluded = ∅)
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (bayes : assessment.IsBayesConsistent setup.commitRecoveryModel
      setup.commitRecoveryModel_decisionAntichain) :
    ∃ site : setup.commitRecoveryModel.InformationSite who,
      site.1 = setup.commitRecoveryClearInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event
          (control.execution.observe (phaseApplication runtime leaks) who)) ∧
      0 < setup.commitRecoveryModel.informationMass assessment.strategy who site ∧
      (assessment.belief who site).map some =
        fiberPosterior
          ((setup.commitRecoveryModel.runBehavioralTerminalFrom
            setup.commitRecoveryProtocol_bounded.wellFoundedHistories assessment.strategy
            setup.commitRecoveryProtocol.initHistory).map
              (site.ancestor? setup.commitRecoveryModel)) Option.isSome true := by
  let view := phaseSourceView? setup mode runtime leaks who event
    (control.execution.observe (phaseApplication runtime leaks) who)
  obtain ⟨source, sourceTrace, excluded, _generation, actor, decoded⟩ :=
    phase_ready_binding_sourceView setup mode runtime leaks plan maximal horizon scheduler trace
      who event payload binding ready clear
  have decision := commitRecovery_isDecisionInfo_of_actor setup source sourceTrace who
    excluded actor
  have observed := setup.commitRecoveryClearInformation_observed wellFormed who sourceTrace excluded
  rw [observed] at decision
  have identified : some (ProtocolState.observe who setup.program source.point) = view :=
    decoded.symm
  change setup.commitRecoveryModel.IsDecisionInfo who
    (setup.commitRecoveryClearInformation wellFormed who
      (some (ProtocolState.observe who setup.program source.point))) at decision
  rw [identified] at decision
  let site : setup.commitRecoveryModel.InformationSite who :=
    ⟨setup.commitRecoveryClearInformation wellFormed who view, decision⟩
  refine ⟨site, rfl, setup.commitRecoveryModel.informationMass_pos_of_fullSupport
    assessment.strategy mixed who site, ?_⟩
  exact setup.commitRecovery_clear_bayes_passage wellFormed assessment mixed bayes who view decision

end Vegas
