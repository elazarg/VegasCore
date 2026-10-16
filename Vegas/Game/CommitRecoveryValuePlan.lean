/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryValuePolicy
import GameTheory.Protocol.PolicyRandomization
import GameTheory.Analysis.Protocol.ExtensiveFormPerfection
import GameTheoryExtensions.Analysis.Protocol.Bayes

/-! # One original ordinary source policy predrawn across all source sites -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

omit [Fintype Player] in
private theorem ordinary_history_finite [Finite Player]
    (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] :
    Finite (setup.executionProtocol (CommitmentInterface.forfeiture setup.program)).History := by
  classical
  let model := setup.informationModel (CommitmentInterface.forfeiture setup.program)
  let reference : model.BehavioralAssessment := .ofStrategy fun who info =>
    let := setup.finite_choice finite (CommitmentInterface.forfeiture setup.program) who info
    let := Fintype.ofFinite (model.Choice who info)
    let := setup.choice_nonempty (CommitmentInterface.forfeiture setup.program) who info
    PMF.uniformOfFintype _
  have mixed : reference.IsFullyMixed := by
    intro who site choice
    let := setup.finite_choice finite (CommitmentInterface.forfeiture setup.program) who site.1
    let := Fintype.ofFinite (model.Choice who site.1)
    let := setup.choice_nonempty (CommitmentInterface.forfeiture setup.program) who site.1
    exact PMF.mem_support_uniformOfFintype choice
  exact mixed.finite_history (setup.protocol_bounded _)
    (fun who info => by
      let := setup.finite_choice finite (CommitmentInterface.forfeiture setup.program) who info
      exact Set.toFinite _)
    (fun {state} draw => setup.protocolStep_support_finite state draw.1)

/-- Predraw one complete ordinary source policy at every played source site.
This is the existing finite-site sampling construction, shared across all
later physical blocks; it never resamples the private initial draw. -/
def commitRecoveryValuePlan (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) (who : Player) :
    PMF ((setup.informationModel (CommitmentInterface.forfeiture setup.program)).Policy who) := by
  classical
  let := ordinary_history_finite setup finite
  let := Fintype.ofFinite
    (setup.executionProtocol (CommitmentInterface.forfeiture setup.program)).History
  let model := setup.informationModel (CommitmentInterface.forfeiture setup.program)
  let policy := setup.commitRecoveryNonmissingSourcePolicy wellFormed profile who
  exact policy.toMixedWithin model (model.playedInformation who) (policy.supportFallback model)

/-- The original global policy draw has the exact conditional ordinary action
law at every genuine clear source input, including inputs outside intended play. -/
theorem commitRecoveryValuePlan_clear_readout (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] (wellFormed : setup.WellFormed)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (history : setup.commitRecoveryProtocol.History)
    (clear : setup.CommitRecoveryClear history.state)
    (running : ¬ setup.commitRecoveryProtocol.terminal history.state) (who : Player) :
    (setup.commitRecoveryValuePlan finite wellFormed profile who).map
        (fun member => member (setup.commitRecoveryPrivate who history.state)) =
      setup.commitRecoveryNonmissingSourcePolicy wellFormed profile who
        (setup.commitRecoveryPrivate who history.state) := by
  classical
  let := ordinary_history_finite setup finite
  let := Fintype.ofFinite
    (setup.executionProtocol (CommitmentInterface.forfeiture setup.program)).History
  let model := setup.informationModel (CommitmentInterface.forfeiture setup.program)
  let policy := setup.commitRecoveryNonmissingSourcePolicy wellFormed profile who
  have sourceRunning : ¬ (setup.executionProtocol
      (CommitmentInterface.forfeiture setup.program)).terminal
        (setup.commitRecoverySourceState history.state) := by
    cases state : history.state with
    | none => exact id
    | some current =>
        rw [state] at running
        exact running
  have played := model.mem_playedInformation (who := who)
    (history := ⟨_, setup.commitRecoveryClearTrace history.trace clear⟩) sourceRunning
  rw [setup.commitRecoveryClearTrace_observe] at played
  change (policy.toMixedWithin model (model.playedInformation who)
    (policy.supportFallback model)).map _ = _
  rw [InformationModel.BehavioralPolicy.toMixedWithin_eq_sampleOn]
  exact FiniteAssignment.sampleOn_map_eval_of_mem policy (model.playedInformation who)
    (policy.supportFallback model) played

/-- The SAME original global source-policy draw reconstructs every actual
clear auxiliary local law when combined with its original fresh omission draw.
This is an unconditioned prior identity; own-recall conditioning remains explicit. -/
theorem commitRecoveryValuePlan_clear_law (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) (history : setup.commitRecoveryProtocol.History)
    (clear : setup.CommitRecoveryClear history.state)
    (running : ¬ setup.commitRecoveryProtocol.terminal history.state) (who : Player) :
    (setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who).bind
        (fun member => setup.commitRecoveryValuePolicy wellFormed assessment.strategy who member
          (setup.commitRecoveryClearInformation wellFormed who
            (setup.commitRecoveryPrivate who history.state))) =
      assessment.strategy who (setup.commitRecoveryClearInformation wellFormed who
        (setup.commitRecoveryPrivate who history.state)) :=
  setup.commitRecoveryValuePolicy_clear_mixture wellFormed assessment mixed history clear running
    who _ (setup.commitRecoveryValuePlan_clear_readout finite wellFormed assessment.strategy
      history clear running who)


/-- One immutable original source-policy profile realizes the entire ordinary
chronological history law. The original private draw is still inside that
history; no independent source entry is selected at later physical blocks. -/
theorem commitRecoveryValuePlan_source_run
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) (fuel : Nat) :
    (setup.informationModel (CommitmentInterface.forfeiture setup.program)).runMixed
        (fun who => setup.commitRecoveryValuePlan finite wellFormed profile who) fuel =
      (setup.informationModel (CommitmentInterface.forfeiture setup.program)).runBehavioral
        (fun who => setup.commitRecoveryNonmissingSourcePolicy wellFormed profile who) fuel := by
  classical
  let := ordinary_history_finite setup finite
  let := Fintype.ofFinite
    (setup.executionProtocol (CommitmentInterface.forfeiture setup.program)).History
  let model := setup.informationModel (CommitmentInterface.forfeiture setup.program)
  let policy := fun who => setup.commitRecoveryNonmissingSourcePolicy wellFormed profile who
  change model.runMixed (fun who => (policy who).toMixedWithin model
    (model.playedInformation who) ((policy who).supportFallback model)) fuel = _
  exact model.runMixed_toMixedWithin
    (setup.protocol_decisionRecall _).actsOnceWhereItMatters model.playedInformation policy
    (fun who => (policy who).supportFallback model) fuel
    (model.coversInformationSites_playedInformation fuel)

end Vegas.SourceProgram.Setup
