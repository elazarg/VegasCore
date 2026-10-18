/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastEarlyPreparationContext
import Vegas.Examples.CommitSeedBroadcastAssessedResponse

/-! # Sequentially supported initial declarations have usable Boolean preparations -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

open Classical in
/-- A supported initial transmission has a usable private Boolean preparation,
including at initial inputs with zero equilibrium probability. -/
theorem raw_early_supported_transmission_usable
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 0)
    (word : execution.recall owner = [])
    (site : rawModel.InformationSite owner)
    (atSite : site.1 = countedModel.infoOf owner source.trace)
    (choice : rawModel.Choice owner site.1)
    (supported : choice ∈ (assessment.strategy owner site.1).support)
    (material : WitnessedSubmission graph) (selected : choice.1 = some ⟨some material⟩) :
    ∃ value : Bool, (material.call.opening.bind fun raw => raw.as? .bool) = some value := by
  have safe := raw_proper_early_context_value_nonnegative assessment equilibrium source remaining
    execution owner current request clock word site atSite
  have factor := rawModel.runnerFactorsAt_terminal canonicalCertificate
    (rawMenu.decisionRecall initial horizon scheduler).actsOnceWhereItMatters
    (rawMenu.informationSite_allNonterminal initial horizon scheduler owner site)
  have integrable (policy : rawModel.BehavioralPolicy owner) :=
    assessment.continuationContext_integrable_of_bounded_terminal canonicalCertificate site
      (rawPayoff owner) (9 / 2) (fun final _ => rawPayoff_abs_le owner final) policy
  have better := assessment.supported_choice_optimal
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site factor (rawPayoff owner)
    (equilibrium.1 owner site) (integrable (assessment.strategy owner)) choice supported
      (scheduledProperContinuation 0 owner) (integrable (scheduledProperContinuation 0 owner))
  have lower := safe.trans better
  have atInput : site.1 = some (execution.recall owner, execution.observe app owner) := by
    rw [atSite]
    change (countedMenu.signals initial horizon scheduler).infoOf owner source.trace = _
    rw [countedMenu.info, current]
    simp only [ReactiveApplication.observe, ite_true]
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun value _ => PhaseCount.countClean_initial runtime leaks value) source.trace
  rw [current] at clean
  have own : OwnPermitted owner execution :=
    ⟨clean.1, fun message member _ => clean.2 message member⟩
  have pastClean := (ownPermitted_iff_past owner execution clean.1).mp own
  have offered := clean_supported_response_counted assessment equilibrium owner site
    (execution.recall owner) (execution.observe app owner) atInput pastClean choice supported
      ⟨some material⟩ selected
  cases decoded : material.call.opening.bind (fun raw => raw.as? .bool) with
  | some value => exact ⟨value, rfl⟩
  | none =>
      have loss := raw_unusable_early_context_value assessment equilibrium source remaining
        execution owner current request clock material offered decoded site atSite choice selected
      have impossible := lower.trans_eq loss
      norm_num at impossible

/-- The literal raw response kernel can transmit only usable initial material.
Old opponent preparations and later opponent policies remain unchanged. -/
theorem raw_early_response_usable
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 0)
    (word : execution.recall owner = [])
    (material : WitnessedSubmission graph)
    (chosen : (⟨some material⟩ : app.Action) ∈
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy owner
        (execution.recall owner) (execution.observe app owner)).support) :
    ∃ value : Bool, (material.call.opening.bind fun raw => raw.as? .bool) = some value := by
  classical
  have running : ¬ countedProtocol.terminal source.state := by
    rw [current]
    intro stopped
    cases stopped.2
  have active : countedProtocol.active source.state owner := by rw [current]; rfl
  obtain ⟨countedSite, observedSite⟩ := countedModel.exists_informationSite_of_active owner source
    running active
  let site := (countedInRaw.actionRestriction initial horizon scheduler).site owner countedSite
  have atSite : site.1 = countedModel.infoOf owner source.trace := observedSite
  have atInput : site.1 = some (execution.recall owner, execution.observe app owner) := by
    rw [atSite]
    change (countedMenu.signals initial horizon scheduler).infoOf owner source.trace = _
    rw [countedMenu.info, current]
    simp only [ReactiveApplication.observe, ite_true]
  have law : rawMenu.decodeProfile initial horizon scheduler assessment.strategy owner
      (execution.recall owner) (execution.observe app owner) =
      (assessment.strategy owner site.1).map (fun choice => choice.1.getD ⟨none⟩) := by
    rw [atInput]
    simp only [ReactiveApplication.ResponseMenu.decodeProfile, ReactiveApplication.decodePolicy,
      ReactiveApplication.ResponseMenu.embedPolicy, PMF.map_comp, Function.comp_def,
      ReactiveApplication.ResponseMenu.rawChoice]
  rw [law] at chosen
  obtain ⟨choice, supported, same⟩ := PMF.support_map .. ▸ chosen
  have selected : choice.1 = some ⟨some material⟩ := by
    cases declared : choice.1 with
    | none => simp only [declared, Option.getD_none] at same; cases same
    | some response =>
        simp only [declared, Option.getD_some] at same
        exact congrArg some same
  exact raw_early_supported_transmission_usable assessment equilibrium source remaining execution
    owner current request clock word site atSite choice supported material selected

/-- The globally covered counted representation has the same usable-response
restriction at every genuine initial input. -/
theorem counted_early_response_usable
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 0)
    (word : execution.recall owner = [])
    (material : WitnessedSubmission graph)
    (chosen : (⟨some material⟩ : app.Action) ∈
      (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment)
        owner (execution.recall owner) (execution.observe app owner)).support) :
    ∃ value : Bool, (material.call.opening.bind fun raw => raw.as? .bool) = some value := by
  rw [counted_assessment_response_law assessment equilibrium source remaining execution owner
    current] at chosen
  exact raw_early_response_usable assessment equilibrium source remaining execution owner current
    request clock word material chosen

end Vegas.Examples.CommitSeedBroadcast
