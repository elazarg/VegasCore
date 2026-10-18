/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastHelperClockTwoTransmissionContext
import Vegas.Examples.CommitSeedBroadcastAssessedResponse

/-! # Strict waiting incentives at the receipted first-late input -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

open Classical in
/-- Every supported current choice waits: a permitted transmission has the
fixed exclusion loss, while WAIT followed by the proper continuation is feasible. -/
theorem raw_helper_clock_two_supported_choice_wait
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 2) (receipted : execution.receipts ≠ [])
    (first : app.PlayerEntry) (word : execution.recall owner = [first])
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (silent : first.action.transmission = none)
    (zero : first.beforeView.application.2.native.clock = 0)
    (site : rawModel.InformationSite owner)
    (atSite : site.1 = countedModel.infoOf owner source.trace)
    (choice : rawModel.Choice owner site.1)
    (supported : choice ∈ (assessment.strategy owner site.1).support) :
    choice.1 = some ⟨none⟩ := by
  have safe := raw_helper_clock_two_proper_context_value_nonnegative assessment equilibrium source
    remaining execution owner current request clock receipted first word firstRequest silent zero
      site atSite
  have factor := rawModel.runnerFactorsAt_terminal canonicalCertificate
    (rawMenu.decisionRecall initial horizon scheduler).actsOnceWhereItMatters
    (rawMenu.informationSite_allNonterminal initial horizon scheduler owner site)
  have integrable (policy : rawModel.BehavioralPolicy owner) :=
    assessment.continuationContext_integrable_of_bounded_terminal canonicalCertificate site
      (rawPayoff owner) (9 / 2) (fun final _ => rawPayoff_abs_le owner final) policy
  have better := assessment.supported_choice_optimal
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site factor (rawPayoff owner)
    (equilibrium.1 owner site) (integrable (assessment.strategy owner)) choice supported
      (scheduledProperContinuation 3 owner) (integrable (scheduledProperContinuation 3 owner))
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
  have available : choice.1 ∈ rawModel.menu owner
      (some (execution.recall owner, execution.observe app owner)) := by
    simpa only [atInput] using choice.2
  obtain ⟨response, _rawAllowed, selected⟩ := available
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact selected
  | some material =>
      have offered := clean_supported_response_counted assessment equilibrium owner site
        (execution.recall owner) (execution.observe app owner) atInput pastClean choice supported
          ⟨some material⟩ selected
      have failed := raw_helper_clock_two_transmission_context_value assessment equilibrium source
        remaining execution owner current request clock receipted material offered site atSite
          choice selected
      have impossible := lower.trans_eq failed
      norm_num at impossible

/-- The literal unchanged raw response law is pure WAIT at every genuine
helper input, including inputs with zero equilibrium reach. -/
theorem raw_helper_clock_two_response_wait
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 2) (receipted : execution.receipts ≠ [])
    (first : app.PlayerEntry) (word : execution.recall owner = [first])
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (silent : first.action.transmission = none)
    (zero : first.beforeView.application.2.native.clock = 0) :
    rawMenu.decodeProfile initial horizon scheduler assessment.strategy owner
      (execution.recall owner) (execution.observe app owner) = PMF.pure ⟨none⟩ := by
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
  rw [law]
  apply pmf_eq_pure_of_support_subset_singleton
  intro response chosen
  obtain ⟨choice, supported, responseEq⟩ := PMF.support_map .. ▸ chosen
  have selected := raw_helper_clock_two_supported_choice_wait assessment equilibrium source
    remaining execution owner current request clock receipted first word firstRequest silent zero
      site atSite choice supported
  apply Set.mem_singleton_iff.mpr
  simpa only [selected, Option.getD_some] using responseEq.symm

/-- The globally count-covered representation has the same literal WAIT law. -/
theorem counted_helper_clock_two_response_wait
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 2) (receipted : execution.receipts ≠ [])
    (first : app.PlayerEntry) (word : execution.recall owner = [first])
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (silent : first.action.transmission = none)
    (zero : first.beforeView.application.2.native.clock = 0) :
    countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment) owner
      (execution.recall owner) (execution.observe app owner) = PMF.pure ⟨none⟩ := by
  rw [counted_assessment_response_law assessment equilibrium source remaining execution owner
    current]
  exact raw_helper_clock_two_response_wait assessment equilibrium source remaining execution owner
    current request clock receipted first word firstRequest silent zero

end Vegas.Examples.CommitSeedBroadcast
