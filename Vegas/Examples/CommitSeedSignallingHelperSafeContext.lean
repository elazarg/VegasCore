/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingHelperProperFuture
import Vegas.Examples.CommitSeedSignallingHelperCountedTrace
import Vegas.Examples.CommitSeedSignallingHelperTypedReceipt
import Vegas.Examples.CommitSeedSignallingOriginalLastInput

/-! # Safe whole continuations on the actual helper information fibers -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- At an actual counted helper prefix the whole proper comparator has
nonnegative net value against the unchanged assessed raw opponents. Its seed
is drawn from the original transcript posterior and is not reinitialized. -/
theorem counted_helper_clock_two_proper_value_nonnegative
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (remaining : Nat) (execution : app.Execution)
    (trace : countedProtocol.Trace (some ⟨remaining, some alice, execution⟩))
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (marker : Message Player (CommitAttemptPacket graph))
    (sender : marker.sender = bob) (addressed : marker.payload.attempt = originalAttempt)
    (visible : marker ∈ (execution.observe app alice).messages.leaked ∨
      marker ∈ (execution.observe app alice).messages.ledger)
    (known : Bool)
    (readout : (∃ accepted, (marker.id, accepted) ∈ (execution.observe app alice).receipts) ↔
      known = true) :
    0 ≤ expect (app.finish initial horizon scheduler
      (Function.update (rawMenu.decodeProfile initial horizon scheduler assessment.strategy) alice
        (properPolicy (helperTimingRule known) alice))
      (some ⟨remaining, some alice, execution⟩)) (fun state => netPayoff state alice) := by
  let history : countedProtocol.History := ⟨some ⟨remaining, some alice, execution⟩, trace⟩
  let profile := Function.update (countedAssessmentProfile assessment) alice
    (countedMenu.restrictPolicy initial horizon scheduler alice
      (properPolicy (helperTimingRule known) alice))
  let players := countedMenu.decodeProfile initial horizon scheduler profile
  have covered : ∀ owner past view response, response ∈ (players owner past view).support →
      response ∈ countedMenu.actions owner past view := by
    intro owner
    exact countedMenu.decode_embedPolicy_covered initial horizon scheduler owner (profile owner)
  have proper : players alice = properPolicy (helperTimingRule known) alice := by
    change app.decodePolicy (countedMenu.embedPolicy initial horizon scheduler alice
      (profile alice)) = _
    dsimp only [profile]
    rw [Function.update_self]
    exact countedMenu.decode_restrictPolicy_of_covered initial horizon scheduler alice _
      (properPolicy_counted (helperTimingRule known) alice)
  have enough : app.rank horizon history.state ≤ app.rank horizon history.state := le_rfl
  have source := countedMenu.run_eq_finish initial horizon scheduler profile
    (app.rank horizon history.state) history enough
  have target := countedInRaw.runFrom_restrictPolicy_finish initial horizon scheduler
    (countedAssessmentProfile assessment) assessment.strategy
    (raw_equilibrium_extends_counted assessment equilibrium) alice
    (properPolicy (helperTimingRule known) alice)
    (properPolicy_counted (helperTimingRule known) alice) (app.rank horizon history.state)
      history enough
  have same := source.symm.trans target
  change app.finish initial horizon scheduler players
    (some ⟨remaining, some alice, execution⟩) = _ at same
  rw [← same]
  apply expect_nonneg
  intro state reached
  change state ∈ (((app.resume players (some alice) execution).bind
    (app.runRounds scheduler players remaining)).map app.finished).support at reached
  obtain ⟨final, physical, stateEq⟩ := PMF.support_map .. ▸ reached
  obtain ⟨responded, responseSupport, rounds⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ physical)
  obtain ⟨action, supported, responseEq⟩ := PMF.support_map .. ▸ responseSupport
  subst responded
  have realized : (implementation.posterior
      (execution.respond app alice action).environmentRecall).bind
      (fun seed => app.runRounds (family seed) players remaining
        (execution.respond app alice action)) =
      app.runRounds scheduler players remaining (execution.respond app alice action) := by
    have joint := implementation.realize players remaining (execution.respond app alice action)
    simp only [implementation, app.schedulerMixture_runJoint, PMF.map_bind,
      PMF.map_comp, Function.comp_def] at joint
    change (implementation.posterior (execution.respond app alice action).environmentRecall).bind
      (fun seed => (app.runRounds (family seed) players remaining
        (execution.respond app alice action)).map id) =
          app.runRounds scheduler players remaining (execution.respond app alice action) at joint
    simpa only [PMF.map_id] using joint
  rw [← realized, PMF.support_bind] at rounds
  obtain ⟨seed, supportedSeed, familyReached⟩ := Set.mem_iUnion₂.mp rounds
  rw [app.respond_environmentRecall] at supportedSeed
  obtain ⟨_originalSupport, ⟨fixed⟩⟩ := menu_original_posterior_trace countedMenu
    ⟨remaining, some alice, execution⟩ trace seed supportedSeed
  have rawFixed := countedInRaw.trace initial horizon (family seed) fixed
  have rawMixed := countedInRaw.trace initial horizon scheduler trace
  have seedRead := alice_helper_clock_two_seed seed ⟨remaining, some alice, execution⟩ rawFixed
    rfl request clock marker sender addressed visible
  have bit : seedBits seed alice = known := by
    have sameBit := seedRead.trans readout
    cases value : seedBits seed alice <;> cases known <;> simp_all
  have retained := app.retained_envelopes_mem_inputs execution
    (app.history_provenance initial horizon scheduler
      (countedMenu.toRawTrace initial horizon scheduler trace))
    (app.history_inputRecall initial horizon scheduler
      (countedMenu.toRawTrace initial horizon scheduler trace))
  have input : marker ∈ execution.network.inputs := by
    rcases visible with leaked | ledger
    · exact retained.leaked alice marker leaked
    · exact retained.ledger marker ledger
  have position := original_first_late_input_index seed ⟨remaining, some alice, execution⟩ rawFixed
    alice rfl request.1.symm clock
  change execution.environmentRecall.length = 4 + if seedBits seed alice then 3 else 1 at position
  have early : execution.environmentRecall.length ≤ 12 := by
    split_ifs at position <;> omega
  obtain ⟨identified, permitted⟩ := observed_helper_packet_permission seed
    ⟨remaining, some alice, execution⟩ trace rawFixed request early marker input sender
  have bobAccepted : known = true → PhaseService.BindingAccepted runtime leaks
      (originalCoordinate bob) bob execution := by
    intro knownTrue
    have late : 6 ≤ execution.environmentRecall.length := by
      rw [bit, knownTrue] at position
      simp only [ite_true] at position
      omega
    exact counted_helper_bob_binding_accepted seed ⟨remaining, some alice, execution⟩ trace fixed
      request quiet early late marker input sender
  have safe := helper_clock_two_proper_rule_future_outcome seed remaining execution rawMixed fixed
    known bit request clock quiet marker input sender identified permitted bobAccepted players
      covered proper action supported final familyReached
  rw [← stateEq]
  exact safe.2

/-- After the remembered clock-two WAIT, the proper whole comparator is
safe at the genuine clock-three source against the same assessed opponents. -/
theorem counted_helper_clock_three_proper_value_nonnegative
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (remaining : Nat) (execution : app.Execution)
    (trace : countedProtocol.Trace (some ⟨remaining, some alice, execution⟩))
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 3)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (helper : app.PlayerEntry) (remembered : helper ∈ execution.recall alice)
    (helperClock : helper.beforeView.application.2.native.clock = 2)
    (waited : helper.action.transmission = none)
    (marker : Message Player (CommitAttemptPacket graph))
    (input : marker ∈ execution.network.inputs) (sender : marker.sender = bob)
    (addressed : marker.payload.attempt = originalAttempt)
    (visible : marker ∈ helper.beforeView.messages.leaked ∨
      marker ∈ helper.beforeView.messages.ledger)
    (receipted : ∃ accepted, (marker.id, accepted) ∈ helper.beforeView.receipts) :
    0 ≤ expect (app.finish initial horizon scheduler
      (Function.update (rawMenu.decodeProfile initial horizon scheduler assessment.strategy) alice
        (properPolicy (helperTimingRule true) alice))
      (some ⟨remaining, some alice, execution⟩)) (fun state => netPayoff state alice) := by
  let history : countedProtocol.History := ⟨some ⟨remaining, some alice, execution⟩, trace⟩
  let profile := Function.update (countedAssessmentProfile assessment) alice
    (countedMenu.restrictPolicy initial horizon scheduler alice
      (properPolicy (helperTimingRule true) alice))
  let players := countedMenu.decodeProfile initial horizon scheduler profile
  have covered : ∀ owner past view response, response ∈ (players owner past view).support →
      response ∈ countedMenu.actions owner past view := by
    intro owner
    exact countedMenu.decode_embedPolicy_covered initial horizon scheduler owner (profile owner)
  have proper : players alice = properPolicy (helperTimingRule true) alice := by
    change app.decodePolicy (countedMenu.embedPolicy initial horizon scheduler alice
      (profile alice)) = _
    dsimp only [profile]
    rw [Function.update_self]
    exact countedMenu.decode_restrictPolicy_of_covered initial horizon scheduler alice _
      (properPolicy_counted (helperTimingRule true) alice)
  have enough : app.rank horizon history.state ≤ app.rank horizon history.state := le_rfl
  have source := countedMenu.run_eq_finish initial horizon scheduler profile
    (app.rank horizon history.state) history enough
  have target := countedInRaw.runFrom_restrictPolicy_finish initial horizon scheduler
    (countedAssessmentProfile assessment) assessment.strategy
    (raw_equilibrium_extends_counted assessment equilibrium) alice
    (properPolicy (helperTimingRule true) alice)
    (properPolicy_counted (helperTimingRule true) alice) (app.rank horizon history.state)
      history enough
  have same := source.symm.trans target
  change app.finish initial horizon scheduler players
    (some ⟨remaining, some alice, execution⟩) = _ at same
  rw [← same]
  apply expect_nonneg
  intro state reached
  change state ∈ (((app.resume players (some alice) execution).bind
    (app.runRounds scheduler players remaining)).map app.finished).support at reached
  obtain ⟨final, physical, stateEq⟩ := PMF.support_map .. ▸ reached
  obtain ⟨responded, responseSupport, rounds⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ physical)
  obtain ⟨action, supported, responseEq⟩ := PMF.support_map .. ▸ responseSupport
  subst responded
  have realized : (implementation.posterior
      (execution.respond app alice action).environmentRecall).bind
      (fun seed => app.runRounds (family seed) players remaining
        (execution.respond app alice action)) =
      app.runRounds scheduler players remaining (execution.respond app alice action) := by
    have joint := implementation.realize players remaining (execution.respond app alice action)
    simp only [implementation, app.schedulerMixture_runJoint, PMF.map_bind,
      PMF.map_comp, Function.comp_def] at joint
    change (implementation.posterior (execution.respond app alice action).environmentRecall).bind
      (fun seed => (app.runRounds (family seed) players remaining
        (execution.respond app alice action)).map id) =
          app.runRounds scheduler players remaining (execution.respond app alice action) at joint
    simpa only [PMF.map_id] using joint
  rw [← realized, PMF.support_bind] at rounds
  obtain ⟨seed, supportedSeed, familyReached⟩ := Set.mem_iUnion₂.mp rounds
  rw [app.respond_environmentRecall] at supportedSeed
  obtain ⟨_originalSupport, ⟨fixed⟩⟩ := menu_original_posterior_trace countedMenu
    ⟨remaining, some alice, execution⟩ trace seed supportedSeed
  have rawFixed := countedInRaw.trace initial horizon (family seed) fixed
  have bit := (alice_recalled_helper_seed seed ⟨remaining, some alice, execution⟩ rawFixed request
    helper remembered helperClock marker sender addressed visible).mpr receipted
  have position := alice_original_clock_three_input_index seed
    ⟨remaining, some alice, execution⟩ rawFixed rfl request.1.symm clock
  have bobAccepted := counted_helper_bob_binding_accepted seed
    ⟨remaining, some alice, execution⟩ trace fixed request quiet (by omega) (by omega)
      marker input sender
  have safe := helper_clock_three_proper_rule_future_outcome seed remaining execution fixed bit
    request clock position quiet helper remembered helperClock waited bobAccepted players covered
      proper action supported final familyReached
  rw [← stateEq]
  exact safe.2
private theorem helper_same_input_counted_trace
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (current : source.state = some ⟨remaining, some alice, execution⟩)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock ≤ 3)
    (marker : Message Player (CommitAttemptPacket graph)) (sender : marker.sender = bob)
    (sourceInput : marker ∈ execution.network.inputs)
    (target : rawModel.InformationHistory alice (countedModel.infoOf alice source.trace))
    (count : Nat) (next : app.Execution)
    (state : target.1.state = some ⟨count, some alice, next⟩)
    (recalled : next.recall alice = execution.recall alice)
    (observed : next.observe app alice = execution.observe app alice)
    (targetInput : marker ∈ next.network.inputs) :
    Nonempty (countedProtocol.Trace (some ⟨count, some alice, next⟩)) := by
  have sourceTrace : countedProtocol.Trace (some ⟨remaining, some alice, execution⟩) :=
    current ▸ source.trace
  have targetTrace : rawProtocol.Trace (some ⟨count, some alice, next⟩) := state ▸ target.1.trace
  obtain ⟨sourceSeed, sourceSupported⟩ :=
    (implementation.posterior execution.environmentRecall).support_nonempty
  obtain ⟨_sourceOriginal, ⟨sourceFixed⟩⟩ := menu_original_posterior_trace countedMenu
    ⟨remaining, some alice, execution⟩ sourceTrace sourceSeed sourceSupported
  obtain ⟨targetSeed, targetSupported⟩ :=
    (implementation.posterior next.environmentRecall).support_nonempty
  obtain ⟨_targetOriginal, ⟨targetFixed⟩⟩ := menu_original_posterior_trace rawMenu
    ⟨count, some alice, next⟩ targetTrace targetSeed targetSupported
  exact raw_helper_input_counted_trace sourceSeed targetSeed
    ⟨remaining, some alice, execution⟩ ⟨count, some alice, next⟩ sourceTrace
      (countedInRaw.trace initial horizon (family sourceSeed) sourceFixed) targetTrace
        targetFixed request clock recalled observed marker sender sourceInput targetInput

open Classical in
/-- The proper whole comparator is safe at EVERY raw history in the actual
clock-two helper fiber, including histories with zero assessed probability. -/
theorem raw_clock_two_helper_safe_alternative_value_nonnegative
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (current : source.state = some ⟨remaining, some alice, execution⟩)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (marker : Message Player (CommitAttemptPacket graph))
    (sender : marker.sender = bob) (addressed : marker.payload.attempt = originalAttempt)
    (visible : marker ∈ (execution.observe app alice).messages.leaked ∨
      marker ∈ (execution.observe app alice).messages.ledger)
    (known : Bool)
    (readout : (∃ accepted, (marker.id, accepted) ∈ (execution.observe app alice).receipts) ↔
      known = true)
    (site : rawModel.InformationSite alice)
    (atSite : site.1 = countedModel.infoOf alice source.trace) :
    0 ≤ (assessment.continuationContext canonicalCertificate site (rawPayoff alice)).value
      (properContinuation (helperTimingRule known) alice) := by
  have fiber (target : rawModel.InformationHistory alice site.1) :
      0 ≤ expect (rawModel.runBehavioralTerminalFrom canonicalCertificate
        (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy alice
          (properContinuation (helperTimingRule known) alice)) target.1) (rawPayoff alice) := by
    let retained : rawModel.InformationHistory alice (countedModel.infoOf alice source.trace) :=
      ⟨target.1, target.2.trans atSite⟩
    obtain ⟨count, next, state, recalled, observed⟩ :=
      raw_information_control_of_counted_view source remaining execution alice current retained
    have sourceTrace : countedProtocol.Trace (some ⟨remaining, some alice, execution⟩) :=
      current ▸ source.trace
    have targetTrace : rawProtocol.Trace (some ⟨count, some alice, next⟩) := state ▸ target.1.trace
    have sourceRaw := countedMenu.toRawTrace initial horizon scheduler sourceTrace
    have targetRaw := rawMenu.toRawTrace initial horizon scheduler targetTrace
    have sourceValid := raw_native_valid scheduler ⟨remaining, some alice, execution⟩ sourceRaw
    have targetValid := raw_native_valid scheduler ⟨count, some alice, next⟩ targetRaw
    have publicSource := (execution.application.requests_publicView sourceValid alice
      (originalCoordinate alice)).mpr request
    have publicTarget : PhaseRuntimeState.requests next.application.publicView alice
        (originalCoordinate alice) := by
      change PhaseRuntimeState.requests (next.observe app alice).application.2 alice _
      rw [observed]
      exact publicSource
    have requested := (next.application.requests_publicView targetValid alice
      (originalCoordinate alice)).mp publicTarget
    have clockHere : next.application.current.native.clock = 2 := by
      have same := congrArg (fun view : app.PlayerView => view.application.2.native.clock) observed
      exact same.trans clock
    have quietHere : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ next.recall alice := by
      rwa [recalled]
    have sourceRetained := app.retained_envelopes_mem_inputs execution
      (app.history_provenance initial horizon scheduler sourceRaw)
      (app.history_inputRecall initial horizon scheduler sourceRaw)
    have targetRetained := app.retained_envelopes_mem_inputs next
      (app.history_provenance initial horizon scheduler targetRaw)
      (app.history_inputRecall initial horizon scheduler targetRaw)
    have sourceInput : marker ∈ execution.network.inputs := by
      rcases visible with leaked | ledger
      · exact sourceRetained.leaked alice marker leaked
      · exact sourceRetained.ledger marker ledger
    have visibleHere : marker ∈ (next.observe app alice).messages.leaked ∨
        marker ∈ (next.observe app alice).messages.ledger := by
      rwa [observed]
    have targetInput : marker ∈ next.network.inputs := by
      rcases visibleHere with leaked | ledger
      · exact targetRetained.leaked alice marker leaked
      · exact targetRetained.ledger marker ledger
    obtain ⟨countedTrace⟩ := helper_same_input_counted_trace source remaining execution current
      request (by omega) marker sender sourceInput retained count next state recalled observed
        targetInput
    have law := raw_terminal_state_law
      (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy alice
        (properContinuation (helperTimingRule known) alice)) target.1
    rw [rawMenu.decodeProfile_update, decode_properContinuation, state] at law
    change 0 ≤ expect (rawModel.runBehavioralTerminalFrom canonicalCertificate
      (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy alice
        (properContinuation (helperTimingRule known) alice)) target.1)
          (fun final => netPayoff final.state alice)
    have expected := congrArg (fun distribution : PMF app.ProtocolState =>
      expect distribution (fun state => netPayoff state alice)) law
    rw [expect_map] at expected
    have positive := counted_helper_clock_two_proper_value_nonnegative assessment equilibrium count
      next countedTrace requested clockHere quietHere marker sender addressed visibleHere known
        (by simpa only [observed] using readout)
    simpa only [Function.comp_def] using positive.trans_eq expected.symm
  have integrable := assessment.continuationContext_integrable_of_bounded_terminal
    canonicalCertificate site (rawPayoff alice) 6 (fun final _ => rawPayoff_abs_le alice final)
      (properContinuation (helperTimingRule known) alice)
  change 0 ≤ (assessment.continuationContextWith
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site (rawPayoff alice)).value
      (properContinuation (helperTimingRule known) alice)
  rw [assessment.continuationContextWith_value_tower
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site (rawPayoff alice)
      (properContinuation (helperTimingRule known) alice) integrable]
  apply expect_nonneg
  intro target _
  exact fiber target

/-- Sequential rationality compares with the concrete safe whole policy,
so every actual clock-two helper context has nonnegative incumbent value. -/
theorem raw_clock_two_helper_context_value_nonnegative
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (current : source.state = some ⟨remaining, some alice, execution⟩)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (marker : Message Player (CommitAttemptPacket graph))
    (sender : marker.sender = bob) (addressed : marker.payload.attempt = originalAttempt)
    (visible : marker ∈ (execution.observe app alice).messages.leaked ∨
      marker ∈ (execution.observe app alice).messages.ledger)
    (site : rawModel.InformationSite alice)
    (atSite : site.1 = countedModel.infoOf alice source.trace) :
    0 ≤ (assessment.continuationContext canonicalCertificate site (rawPayoff alice)).value
      (assessment.strategy alice) := by
  classical
  let known := decide (∃ accepted, (marker.id, accepted) ∈ (execution.observe app alice).receipts)
  have readout : (∃ accepted, (marker.id, accepted) ∈ (execution.observe app alice).receipts) ↔
      known = true := (decide_eq_true_iff).symm
  have safe := raw_clock_two_helper_safe_alternative_value_nonnegative assessment equilibrium
    source remaining execution current request clock quiet marker sender addressed visible known
      readout site atSite
  have integrable (alternative : rawModel.BehavioralPolicy alice) :=
    assessment.continuationContext_integrable_of_bounded_terminal
      canonicalCertificate site (rawPayoff alice) 6
      (fun final _ => rawPayoff_abs_le alice final) alternative
  have compare := (Context.isLocallyOptimal_iff_of_integrable
    (integrable (assessment.strategy alice)) (fun alternative _ => integrable alternative)).mp
    (equilibrium.1 alice site)
  exact safe.trans (compare (properContinuation (helperTimingRule known) alice) (Set.mem_univ _))
private theorem remembered_helper_marker_input (remaining : Nat) (execution : app.Execution)
    (trace : rawProtocol.Trace (some ⟨remaining, some alice, execution⟩))
    (helper : app.PlayerEntry) (recorded : helper ∈ execution.recall alice)
    (marker : Message Player (CommitAttemptPacket graph))
    (visible : marker ∈ helper.beforeView.messages.leaked ∨
      marker ∈ helper.beforeView.messages.ledger) : marker ∈ execution.network.inputs := by
  obtain ⟨before, prior, kept, _active, observed, _allowed, _later⟩ :=
    rawMenu.recorded_response_prefix initial horizon scheduler
      ⟨remaining, some alice, execution⟩ trace alice helper recorded
  have rawBefore := rawMenu.toRawTrace initial horizon scheduler prior
  have rawCurrent := rawMenu.toRawTrace initial horizon scheduler trace
  have retained := app.retained_envelopes_mem_inputs before.execution
    (app.history_provenance initial horizon scheduler rawBefore)
    (app.history_inputRecall initial horizon scheduler rawBefore)
  rw [observed] at visible
  have oldInput : marker ∈ before.execution.network.inputs := by
    rcases visible with leaked | ledger
    · exact retained.leaked alice marker leaked
    · exact retained.ledger marker ledger
  obtain ⟨entry, authored, material, _transmitted, emitted, _packet⟩ :=
    (app.history_provenance initial horizon scheduler rawBefore).inputs marker oldInput
  have recalled := app.reaches_recall_prefix initial horizon scheduler
    (rawMenu.reaches_raw initial horizon scheduler kept.reachesWithin)
      before ⟨remaining, some alice, execution⟩ rfl rfl marker.sender
  have output : marker ∈ app.outputs (execution.recall marker.sender) := by
    exact List.mem_filterMap.mpr ⟨entry, recalled.subset authored, emitted⟩
  rw [← app.history_inputRecall initial horizon scheduler rawCurrent marker.sender] at output
  exact (List.mem_filter.mp output).1

open Classical in
/-- The remembered WAIT and helper input are retained literally on every raw
member of the clock-three information set. The proper whole comparator is
safe there against the unchanged assessed future, including at zero reach. -/
theorem raw_clock_three_helper_safe_alternative_value_nonnegative
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (current : source.state = some ⟨remaining, some alice, execution⟩)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 3)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (helper : app.PlayerEntry) (remembered : helper ∈ execution.recall alice)
    (helperClock : helper.beforeView.application.2.native.clock = 2)
    (waited : helper.action.transmission = none)
    (marker : Message Player (CommitAttemptPacket graph))
    (sender : marker.sender = bob) (addressed : marker.payload.attempt = originalAttempt)
    (visible : marker ∈ helper.beforeView.messages.leaked ∨
      marker ∈ helper.beforeView.messages.ledger)
    (receipted : ∃ accepted, (marker.id, accepted) ∈ helper.beforeView.receipts)
    (site : rawModel.InformationSite alice)
    (atSite : site.1 = countedModel.infoOf alice source.trace) :
    0 ≤ (assessment.continuationContext canonicalCertificate site (rawPayoff alice)).value
      (properContinuation (helperTimingRule true) alice) := by
  have fiber (target : rawModel.InformationHistory alice site.1) :
      0 ≤ expect (rawModel.runBehavioralTerminalFrom canonicalCertificate
        (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy alice
          (properContinuation (helperTimingRule true) alice)) target.1) (rawPayoff alice) := by
    let retained : rawModel.InformationHistory alice (countedModel.infoOf alice source.trace) :=
      ⟨target.1, target.2.trans atSite⟩
    obtain ⟨count, next, state, recalled, observed⟩ :=
      raw_information_control_of_counted_view source remaining execution alice current retained
    have sourceTrace : countedProtocol.Trace (some ⟨remaining, some alice, execution⟩) :=
      current ▸ source.trace
    have targetTrace : rawProtocol.Trace (some ⟨count, some alice, next⟩) := state ▸ target.1.trace
    have sourceRaw := countedMenu.toRawTrace initial horizon scheduler sourceTrace
    have targetRaw := rawMenu.toRawTrace initial horizon scheduler targetTrace
    have sourceValid := raw_native_valid scheduler ⟨remaining, some alice, execution⟩ sourceRaw
    have targetValid := raw_native_valid scheduler ⟨count, some alice, next⟩ targetRaw
    have publicSource := (execution.application.requests_publicView sourceValid alice
      (originalCoordinate alice)).mpr request
    have publicTarget : PhaseRuntimeState.requests next.application.publicView alice
        (originalCoordinate alice) := by
      change PhaseRuntimeState.requests (next.observe app alice).application.2 alice _
      rw [observed]
      exact publicSource
    have requested := (next.application.requests_publicView targetValid alice
      (originalCoordinate alice)).mp publicTarget
    have clockHere : next.application.current.native.clock = 3 := by
      have same := congrArg (fun view : app.PlayerView => view.application.2.native.clock) observed
      exact same.trans clock
    have quietHere : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ next.recall alice := by
      rwa [recalled]
    have rememberedHere : helper ∈ next.recall alice := by
      rwa [recalled]
    have sourceInput := remembered_helper_marker_input remaining execution
      (countedInRaw.trace initial horizon scheduler sourceTrace) helper remembered marker visible
    have targetInput := remembered_helper_marker_input count next targetTrace helper rememberedHere
      marker visible
    obtain ⟨countedTrace⟩ := helper_same_input_counted_trace source remaining execution current
      request (by omega) marker sender sourceInput retained count next state recalled observed
        targetInput
    have law := raw_terminal_state_law
      (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy alice
        (properContinuation (helperTimingRule true) alice)) target.1
    rw [rawMenu.decodeProfile_update, decode_properContinuation, state] at law
    change 0 ≤ expect (rawModel.runBehavioralTerminalFrom canonicalCertificate
      (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy alice
        (properContinuation (helperTimingRule true) alice)) target.1)
          (fun final => netPayoff final.state alice)
    have expected := congrArg (fun distribution : PMF app.ProtocolState =>
      expect distribution (fun state => netPayoff state alice)) law
    rw [expect_map] at expected
    have positive := counted_helper_clock_three_proper_value_nonnegative assessment equilibrium
      count next countedTrace requested clockHere quietHere helper rememberedHere helperClock waited
        marker targetInput sender addressed visible receipted
    simpa only [Function.comp_def] using positive.trans_eq expected.symm
  have integrable := assessment.continuationContext_integrable_of_bounded_terminal
    canonicalCertificate site (rawPayoff alice) 6 (fun final _ => rawPayoff_abs_le alice final)
      (properContinuation (helperTimingRule true) alice)
  change 0 ≤ (assessment.continuationContextWith
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site (rawPayoff alice)).value
      (properContinuation (helperTimingRule true) alice)
  rw [assessment.continuationContextWith_value_tower
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site (rawPayoff alice)
      (properContinuation (helperTimingRule true) alice) integrable]
  apply expect_nonneg
  intro target _
  exact fiber target
/-- The actual incumbent has nonnegative value at each known eligible helper
site. A clock-three site retains the real earlier WAIT; its past is never
replaced by the fixed-late policy's different past. -/
theorem raw_helper_context_value_nonnegative
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (current : source.state = some ⟨remaining, some alice, execution⟩)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (bit : Bool) (clock : execution.application.current.native.clock = if bit then 3 else 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (helper : app.PlayerEntry)
    (remembered : helper ∈ execution.recall alice ∨
      helper = originalResponseEntry execution alice ⟨none⟩)
    (_helperRequest : PhaseRuntimeState.requests helper.beforeView.application.2 alice
      (originalCoordinate alice))
    (helperClock : helper.beforeView.application.2.native.clock = 2)
    (waited : bit = true → helper.action.transmission = none)
    (marker : Message Player (CommitAttemptPacket graph))
    (sender : marker.sender = bob) (addressed : marker.payload.attempt = originalAttempt)
    (visible : marker ∈ helper.beforeView.messages.leaked ∨
      marker ∈ helper.beforeView.messages.ledger)
    (readout : (∃ accepted, (marker.id, accepted) ∈ helper.beforeView.receipts) ↔ bit = true)
    (site : rawModel.InformationSite alice)
    (atSite : site.1 = countedModel.infoOf alice source.trace) :
    0 ≤ (assessment.continuationContext canonicalCertificate site (rawPayoff alice)).value
      (assessment.strategy alice) := by
  cases bit with
  | false =>
      change execution.application.current.native.clock = 2 at clock
      rcases remembered with old | currentHelper
      · have sourceTrace : countedProtocol.Trace (some ⟨remaining, some alice, execution⟩) :=
          current ▸ source.trace
        obtain ⟨seed, seedSupport⟩ :=
          (implementation.posterior execution.environmentRecall).support_nonempty
        obtain ⟨_initial, ⟨fixed⟩⟩ := menu_original_posterior_trace countedMenu
          ⟨remaining, some alice, execution⟩ sourceTrace seed seedSupport
        have recalled := alice_clock_two_initial_wait_recall seed remaining execution
          (countedInRaw.trace initial horizon (family seed) fixed) request clock quiet
        rw [recalled, List.mem_singleton] at old
        rw [old] at helperClock
        have zero :
            (originalResponseEntry aliceFirst alice ⟨none⟩).beforeView.application.2.native.clock =
              0 := by
          change aliceFirst.application.current.native.clock = 0
          rw [aliceFirst_application]
          exact initialState_clock
        rw [zero] at helperClock
        omega
      · subst helper
        exact raw_clock_two_helper_context_value_nonnegative assessment equilibrium source
          remaining execution current request clock quiet marker sender addressed visible
            site atSite
  | true =>
      change execution.application.current.native.clock = 3 at clock
      have old : helper ∈ execution.recall alice := by
        rcases remembered with old | currentHelper
        · exact old
        · rw [currentHelper] at helperClock
          change execution.application.current.native.clock = 2 at helperClock
          omega
      have safe := raw_clock_three_helper_safe_alternative_value_nonnegative assessment equilibrium
        source remaining execution current request clock quiet helper old helperClock (waited rfl)
          marker sender addressed visible (readout.mpr rfl) site atSite
      have integrable (alternative : rawModel.BehavioralPolicy alice) :=
        assessment.continuationContext_integrable_of_bounded_terminal
          canonicalCertificate site (rawPayoff alice) 6
          (fun final _ => rawPayoff_abs_le alice final) alternative
      have compare := (Context.isLocallyOptimal_iff_of_integrable
        (integrable (assessment.strategy alice)) (fun alternative _ => integrable alternative)).mp
        (equilibrium.1 alice site)
      exact safe.trans
        (compare (properContinuation (helperTimingRule true) alice) (Set.mem_univ _))
end Vegas.Examples.CommitSeedSignalling
