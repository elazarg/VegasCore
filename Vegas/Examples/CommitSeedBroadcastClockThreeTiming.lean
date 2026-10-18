/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastClockThreeWaitContext

/-! # Strict final original transmission incentives in the actual raw game -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

open Classical in
/-- After observing and remembering the middle receipt signal, an owner
never supports WAIT at its last original opportunity in a raw sequential equilibrium. -/
theorem raw_clock_three_supported_choice_ne_wait
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 3)
    (first second : app.PlayerEntry) (word : execution.recall owner = [first, second])
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (secondRequest : PhaseRuntimeState.requests second.beforeView.application.2 owner
      (originalCoordinate owner))
    (secondClock : second.beforeView.application.2.native.clock = 2)
    (receipted : second.beforeView.receipts ≠ [])
    (silent : first.action.transmission = none)
    (secondSilent : second.action.transmission = none)
    (zero : first.beforeView.application.2.native.clock = 0)
    (site : rawModel.InformationSite owner)
    (atSite : site.1 = countedModel.infoOf owner source.trace)
    (choice : rawModel.Choice owner site.1)
    (supported : choice ∈ (assessment.strategy owner site.1).support) :
    choice.1 ≠ some (⟨none⟩ : app.Action) := by
  intro selected
  have lower := raw_proper_clock_three_context_value_nonnegative assessment equilibrium source
    remaining execution owner current request clock first second word firstRequest secondRequest
      secondClock receipted silent secondSilent zero site atSite
  have upper := raw_clock_three_wait_context_value assessment equilibrium source remaining
    execution owner current request clock first second word firstRequest secondRequest secondClock
      silent secondSilent zero site atSite choice selected
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
  have comparison := lower.trans (better.trans_eq upper)
  norm_num at comparison

/-- The unchanged actual decoded raw strategy sends a packet at every such
clock-three input, including decisions with zero equilibrium reach. -/
theorem raw_clock_three_response_ne_wait
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 3)
    (first second : app.PlayerEntry) (word : execution.recall owner = [first, second])
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (secondRequest : PhaseRuntimeState.requests second.beforeView.application.2 owner
      (originalCoordinate owner))
    (secondClock : second.beforeView.application.2.native.clock = 2)
    (receipted : second.beforeView.receipts ≠ [])
    (silent : first.action.transmission = none)
    (secondSilent : second.action.transmission = none)
    (zero : first.beforeView.application.2.native.clock = 0) :
    (⟨none⟩ : app.Action) ∉ (rawMenu.decodeProfile initial horizon scheduler assessment.strategy
      owner (execution.recall owner) (execution.observe app owner)).support := by
  classical
  intro waiting
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
  have present : some (⟨none⟩ : app.Action) ∈
      ((assessment.strategy owner rawSite.1).map Subtype.val).support := by
    rw [← mapped, PMF.support_map]
    exact ⟨⟨none⟩, waiting, rfl⟩
  obtain ⟨choice, supported, selected⟩ := PMF.support_map .. ▸ present
  exact raw_clock_three_supported_choice_ne_wait assessment equilibrium source remaining
    execution owner current request clock first second word firstRequest secondRequest secondClock
      receipted silent secondSilent zero rawSite atSite choice supported selected

end Vegas.Examples.CommitSeedBroadcast
