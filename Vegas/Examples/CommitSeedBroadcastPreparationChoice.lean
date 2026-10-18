/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastPreparationContext
import Vegas.Examples.CommitSeedBroadcastPublicationContinuation
import Vegas.Examples.CommitSeedBroadcastFirstLateTiming

/-! # Usable first-late declarations in every native sequential equilibrium -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

open Classical in
/-- An unusable permitted preparation cannot be supported at an original
empty-ledger clock-two information set. The full continuation loss is strict. -/
theorem raw_unusable_clock_two_choice_not_supported
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 2) (empty : execution.receipts = [])
    (first : app.PlayerEntry) (word : execution.recall owner = [first])
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (silent : first.action.transmission = none)
    (zero : first.beforeView.application.2.native.clock = 0)
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions owner
      (execution.recall owner) (execution.observe app owner))
    (unusable : (material.call.opening.bind fun raw => raw.as? .bool) = none)
    (site : rawModel.InformationSite owner)
    (atSite : site.1 = countedModel.infoOf owner source.trace)
    (choice : rawModel.Choice owner site.1) (selected : choice.1 = some ⟨some material⟩) :
    choice ∉ (assessment.strategy owner site.1).support := by
  intro supported
  have gap := raw_unusable_clock_two_context_gap assessment equilibrium source remaining execution
    owner current request clock empty first word firstRequest silent zero material offered unusable
      site atSite choice selected
  have factor := rawModel.runnerFactorsAt_terminal canonicalCertificate
    (rawMenu.decisionRecall initial horizon scheduler).actsOnceWhereItMatters
    (rawMenu.informationSite_allNonterminal initial horizon scheduler owner site)
  have integrable (policy : rawModel.BehavioralPolicy owner) :=
    assessment.continuationContext_integrable_of_bounded_terminal canonicalCertificate site
      (rawPayoff owner) (9 / 2) (fun final _ => rawPayoff_abs_le owner final) policy
  have optimal := assessment.supported_choice_optimal
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site factor (rawPayoff owner)
    (equilibrium.1 owner site) (integrable (assessment.strategy owner)) choice supported
      (scheduledProperContinuation 2 owner) (integrable (scheduledProperContinuation 2 owner))
  change (assessment.continuationContext canonicalCertificate site (rawPayoff owner)).value
      (scheduledProperContinuation 2 owner) ≤
    (assessment.continuationContext canonicalCertificate site (rawPayoff owner)).value
      ((assessment.strategy owner).commit site.1 choice) at optimal
  linarith

/-- Every supported raw response at a genuine empty-ledger first-late input
is a nonsilent declaration with an actual well-typed opening preparation. -/
theorem raw_first_late_response_usable
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 2) (empty : execution.receipts = [])
    (first : app.PlayerEntry) (word : execution.recall owner = [first])
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (silent : first.action.transmission = none)
    (zero : first.beforeView.application.2.native.clock = 0)
    (response : app.Action)
    (responded : response ∈ (rawMenu.decodeProfile initial horizon scheduler assessment.strategy
      owner (execution.recall owner) (execution.observe app owner)).support) :
    ∃ material : WitnessedSubmission graph, ∃ value : Bool,
      response = ⟨some material⟩ ∧
        (material.call.opening.bind fun raw => raw.as? .bool) = some value := by
  classical
  have trace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩) :=
    current ▸ source.trace
  have nonwait := raw_first_late_response_ne_wait assessment equilibrium source remaining execution
    owner current request clock empty first word firstRequest silent zero
  have nonsilent : response.transmission ≠ none := by
    intro silentResponse
    have same : response = (⟨none⟩ : app.Action) := by
      have eta : response = ⟨response.transmission⟩ := by cases response; rfl
      exact eta.trans (congrArg ReactiveApplication.Action.mk silentResponse)
    exact nonwait (same ▸ responded)
  obtain ⟨material, emitted⟩ := Option.ne_none_iff_exists'.mp nonsilent
  have responseEq : response = (⟨some material⟩ : app.Action) := by
    have eta : response = ⟨response.transmission⟩ := by cases response; rfl
    exact eta.trans (congrArg ReactiveApplication.Action.mk emitted)
  have offered := counted_equilibrium_response_allowed assessment equilibrium remaining execution
    owner trace response responded
  rw [responseEq] at offered
  have running : ¬ countedProtocol.terminal source.state := by
    rw [current]
    intro stopped
    cases stopped.2
  have active : countedProtocol.active source.state owner := by rw [current]; rfl
  obtain ⟨site, atSite⟩ := countedModel.exists_informationSite_of_active owner source running active
  let rawSite := (countedInRaw.actionRestriction initial horizon scheduler).site owner site
  have observed : rawSite.1 = some (execution.recall owner, execution.observe app owner) := by
    change site.1 = _
    rw [atSite]
    change (countedMenu.signals initial horizon scheduler).infoOf owner source.trace = _
    rw [countedMenu.info, current]
    simp only [ReactiveApplication.observe, ite_true]
  have encoded := congrFun (app.encode_decodePolicy
    (rawMenu.embedPolicy initial horizon scheduler owner (assessment.strategy owner)))
      (some (execution.recall owner, execution.observe app owner))
  have projection := congrArg (fun law => law.map Subtype.val) encoded
  have mapped : (rawMenu.decodeProfile initial horizon scheduler assessment.strategy owner
      (execution.recall owner) (execution.observe app owner)).map some =
        (assessment.strategy owner rawSite.1).map Subtype.val := by
    rw [observed]
    simpa only [ReactiveApplication.encodePolicy,
      ReactiveApplication.ResponseMenu.decodeProfile,
      ReactiveApplication.ResponseMenu.embedPolicy, PMF.map_comp, Function.comp_def,
      ReactiveApplication.ResponseMenu.rawChoice] using projection
  have present : some response ∈
      ((assessment.strategy owner rawSite.1).map Subtype.val).support := by
    rw [← mapped, PMF.support_map]
    exact ⟨response, responded, rfl⟩
  obtain ⟨choice, supported, selected⟩ := PMF.support_map .. ▸ present
  have selectedMaterial : choice.1 = some ⟨some material⟩ :=
    selected.trans (congrArg some responseEq)
  have usable : (material.call.opening.bind fun raw => raw.as? .bool) ≠ none := by
    intro unusable
    exact raw_unusable_clock_two_choice_not_supported assessment equilibrium source remaining
      execution owner current request clock empty first word firstRequest silent zero material
        offered unusable rawSite atSite choice selectedMaterial supported
  obtain ⟨value, interpreted⟩ := Option.ne_none_iff_exists'.mp usable
  exact ⟨material, value, responseEq, interpreted⟩

/-- Restricting the assessed raw strategy retains the same usable declaration
support at every genuine counted first-late decision, even off equilibrium path. -/
theorem counted_first_late_response_usable
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 2) (empty : execution.receipts = [])
    (first : app.PlayerEntry) (word : execution.recall owner = [first])
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (silent : first.action.transmission = none)
    (zero : first.beforeView.application.2.native.clock = 0)
    (response : app.Action)
    (responded : response ∈
      (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment)
        owner (execution.recall owner) (execution.observe app owner)).support) :
    ∃ material : WitnessedSubmission graph, ∃ value : Bool,
      response = ⟨some material⟩ ∧
        (material.call.opening.bind fun raw => raw.as? .bool) = some value := by
  rw [counted_assessment_response_law assessment equilibrium source remaining execution owner
    current] at responded
  exact raw_first_late_response_usable assessment equilibrium source remaining execution owner
    current request clock empty first word firstRequest silent zero response responded

end Vegas.Examples.CommitSeedBroadcast
