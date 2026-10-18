/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastPreparationLaw
import Vegas.Examples.CommitSeedBroadcastProperTimingContext

/-! # Strict usable-preparation comparisons on the full raw information fiber -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

open Classical in
/-- The strict gain is integrated on the original complete native information
fiber, without identifying distinct later response draws in the two experiments. -/
theorem raw_unusable_clock_two_context_advantage
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
    (assessment.continuationContext canonicalCertificate site (rawPayoff owner)).value
        ((assessment.strategy owner).commit site.1 choice) +
      expect (assessment.belief owner site)
        (fun history => preparationAdvantageValue history.1.state owner) ≤
    (assessment.continuationContext canonicalCertificate site (rawPayoff owner)).value
      (scheduledProperContinuation 2 owner) := by
  have sourceTrace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩) :=
    current ▸ source.trace
  let incumbent := countedMenu.decodeProfile initial horizon scheduler
    (countedAssessmentProfile assessment)
  let policy := scheduledProperPolicy 2 owner
  let profile := Function.update (countedAssessmentProfile assessment) owner
    (countedMenu.restrictPolicy initial horizon scheduler owner policy)
  let players := countedMenu.decodeProfile initial horizon scheduler profile
  have playersEq : players = Function.update incumbent owner policy := by
    funext who
    by_cases same : who = owner
    · subst who
      change app.decodePolicy (countedMenu.embedPolicy initial horizon scheduler owner
        ((Function.update (countedAssessmentProfile assessment) owner
          (countedMenu.restrictPolicy initial horizon scheduler owner policy)) owner)) = _
      rw [Function.update_self, Function.update_self]
      exact countedMenu.decode_restrictPolicy_of_covered initial horizon scheduler owner policy
        (scheduledProperPolicy_counted 2 owner)
    · change app.decodePolicy (countedMenu.embedPolicy initial horizon scheduler who
        ((Function.update (countedAssessmentProfile assessment) owner
          (countedMenu.restrictPolicy initial horizon scheduler owner policy)) who)) = _
      rw [Function.update_of_ne same, Function.update_of_ne same]
      rfl
  have incumbentCovered who past view action
      (supported : action ∈ (incumbent who past view).support) :
      action ∈ countedMenu.actions who past view :=
    countedMenu.decode_embedPolicy_covered initial horizon scheduler who
      (countedAssessmentProfile assessment who) past view action supported
  have fiber (target : rawModel.InformationHistory owner site.1) :
      expect (rawModel.runBehavioralTerminalFrom canonicalCertificate
        (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy owner
          ((assessment.strategy owner).commit site.1 choice)) target.1) (rawPayoff owner) +
        preparationAdvantageValue target.1.state owner ≤
      expect (rawModel.runBehavioralTerminalFrom canonicalCertificate
        (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy owner
          (scheduledProperContinuation 2 owner)) target.1) (rawPayoff owner) := by
    let sameInput : rawModel.InformationHistory owner (countedModel.infoOf owner source.trace) :=
      ⟨target.1, target.2.trans atSite⟩
    obtain ⟨count, next, state, ⟨countedTrace⟩, recalled, observed⟩ :=
      counted_information_raw_fiber_control source remaining execution owner current sameInput
    have rawTrace : rawProtocol.Trace (some ⟨count, some owner, next⟩) := state ▸ target.1.trace
    have valid := raw_native_valid scheduler ⟨remaining, some owner, execution⟩
      (countedMenu.toRawTrace initial horizon scheduler sourceTrace)
    have publicSource := (execution.application.requests_publicView valid owner
      (originalCoordinate owner)).mpr request
    have publicNext : PhaseRuntimeState.requests next.application.publicView owner
        (originalCoordinate owner) := by
      change PhaseRuntimeState.requests (next.observe app owner).application.2 owner _
      rw [observed]
      exact publicSource
    have nextValid := raw_native_valid scheduler ⟨count, some owner, next⟩
      (rawMenu.toRawTrace initial horizon scheduler rawTrace)
    have requestNext := (next.application.requests_publicView nextValid owner
      (originalCoordinate owner)).mp publicNext
    have clockNext : next.application.current.native.clock = 2 := by
      change (next.observe app owner).application.2.native.clock = 2
      rw [observed]
      exact clock
    have emptyNext : next.receipts = [] := by
      change (next.observe app owner).receipts = []
      rw [observed]
      exact empty
    have wordNext : next.recall owner = [first] := recalled.trans word
    have outputs := silent_own_outputs_of_history scheduler ⟨count, some owner, next⟩
      (rawMenu.toRawTrace initial horizon scheduler rawTrace) owner (by
        intro entry member
        rw [wordNext, List.mem_singleton] at member
        subst entry
        exact silent)
    have past : policy.Consistent (next.recall owner) := by
      rw [wordNext]
      exact proper_clock_two_initial_wait_consistent owner first firstRequest zero silent
    have offeredNext : (⟨some material⟩ : app.Action) ∈ countedMenu.actions owner
        (next.recall owner) (next.observe app owner) := by
      simpa only [recalled, observed] using offered
    have bound := counted_unusable_clock_two_finish_gap assessment equilibrium count next owner
      countedTrace requestNext clockNext emptyNext
        (by rw [outputs]; exact fun _ member => (List.not_mem_nil member).elim)
          past material offeredNext unusable (incumbent owner) (incumbentCovered owner)
    have unchanged : Function.update incumbent owner (incumbent owner) = incumbent :=
      Function.update_eq_self owner incumbent
    change expect (app.finish initial horizon scheduler
      (Function.update incumbent owner (incumbent owner)) _) _ + _ ≤ _ at bound
    rw [unchanged, ← playersEq] at bound
    obtain ⟨responded⟩ := countedMenu.trace_respond initial horizon scheduler count next owner
      ⟨some material⟩ countedTrace offeredNext
    let after : countedProtocol.History :=
      ⟨some ⟨count, none, next.respond app owner ⟨some material⟩⟩, responded⟩
    have physicalBad := counted_assessment_finish_eq assessment equilibrium after
    change app.finish initial horizon scheduler incumbent after.state = _ at physicalBad
    rw [physicalBad] at bound
    have enough : app.rank horizon target.1.state ≤ 2 * horizon + 1 := by
      rw [state]
      exact (Nat.le_add_left _ _).trans (app.trace_bound initial horizon scheduler
        (rawMenu.toRawTrace initial horizon scheduler rawTrace))
    have projection := rawMenu.run_local_law_finish_of_information initial horizon scheduler
      assessment.strategy target.1 owner count next state site.1 target.2 (PMF.pure choice)
        (2 * horizon) enough
    change (rawModel.runBehavioralFrom
      (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy owner
        ((assessment.strategy owner).commit site.1 choice)) (2 * horizon + 1)
          target.1).map History.state = _ at projection
    rw [PMF.pure_map, selected, Option.getD_some, PMF.pure_bind] at projection
    have badLaw : (rawModel.runBehavioralTerminalFrom canonicalCertificate
        (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy owner
          ((assessment.strategy owner).commit site.1 choice)) target.1).map History.state =
        app.finish initial horizon scheduler
          (rawMenu.decodeProfile initial horizon scheduler assessment.strategy) after.state := by
      rw [rawModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
        canonicalCertificate (rawMenu.bounded initial horizon scheduler)]
      exact projection
    have badExpected := congrArg (fun law : PMF app.ProtocolState =>
      expect law (fun terminal => netPayoff terminal owner)) badLaw
    rw [expect_map] at badExpected
    change expect _ (rawPayoff owner) = _ at badExpected
    let retained : countedProtocol.History := ⟨some ⟨count, some owner, next⟩, countedTrace⟩
    have physicalProper := countedInRaw.runFrom_restrictPolicy_finish initial horizon scheduler
      (countedAssessmentProfile assessment) assessment.strategy
        (raw_equilibrium_extends_counted assessment equilibrium) owner policy
        (scheduledProperPolicy_counted 2 owner) (app.rank horizon retained.state) retained le_rfl
    rw [countedMenu.run_eq_finish initial horizon scheduler profile
      (app.rank horizon retained.state) retained le_rfl] at physicalProper
    have properLaw := raw_terminal_state_law
      (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy owner
        (scheduledProperContinuation 2 owner)) target.1
    rw [rawMenu.decodeProfile_update, decode_scheduledProperContinuation, state] at properLaw
    have properExpected := congrArg (fun law : PMF app.ProtocolState =>
      expect law (fun terminal => netPayoff terminal owner)) properLaw
    rw [expect_map] at properExpected
    change expect _ (rawPayoff owner) = _ at properExpected
    rw [state, badExpected, properExpected, ← physicalProper]
    exact bound
  have badIntegrable := assessment.continuationContext_integrable_of_bounded_terminal
    canonicalCertificate site (rawPayoff owner) (9 / 2)
      (fun final _ => rawPayoff_abs_le owner final)
        ((assessment.strategy owner).commit site.1 choice)
  have properIntegrable := assessment.continuationContext_integrable_of_bounded_terminal
    canonicalCertificate site (rawPayoff owner) (9 / 2)
      (fun final _ => rawPayoff_abs_le owner final) (scheduledProperContinuation 2 owner)
  change (assessment.continuationContextWith
      (rawModel.runBehavioralTerminalFrom canonicalCertificate) site (rawPayoff owner)).value
        ((assessment.strategy owner).commit site.1 choice) + _ ≤
    (assessment.continuationContextWith
      (rawModel.runBehavioralTerminalFrom canonicalCertificate) site (rawPayoff owner)).value
        (scheduledProperContinuation 2 owner)
  rw [assessment.continuationContextWith_value_tower
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site (rawPayoff owner)
      ((assessment.strategy owner).commit site.1 choice) badIntegrable,
    assessment.continuationContextWith_value_tower
      (rawModel.runBehavioralTerminalFrom canonicalCertificate) site (rawPayoff owner)
        (scheduledProperContinuation 2 owner) properIntegrable,
    ← expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)]
  exact expect_mono (fun target _ => fiber target)
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)

open Classical in
/-- At the same actual raw information set, an unusable current declaration
loses at least one thirty-second to the feasible whole proper continuation. -/
theorem raw_unusable_clock_two_context_gap
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
    (assessment.continuationContext canonicalCertificate site (rawPayoff owner)).value
        ((assessment.strategy owner).commit site.1 choice) + (1 / 32 : ℝ) ≤
    (assessment.continuationContext canonicalCertificate site (rawPayoff owner)).value
      (scheduledProperContinuation 2 owner) := by
  have advantage := raw_unusable_clock_two_context_advantage assessment equilibrium source remaining
    execution owner current request clock empty first word firstRequest silent zero material
      offered unusable site atSite choice selected
  have mass := assessed_preparation_advantage_lower assessment equilibrium.2 source
    remaining
    execution owner current request clock empty site atSite
  linarith

end Vegas.Examples.CommitSeedBroadcast
