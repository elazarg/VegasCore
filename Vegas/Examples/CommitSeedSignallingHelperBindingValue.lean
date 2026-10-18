/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingHelperInitialRecall
import Vegas.Examples.CommitSeedSignallingOwnContinuation
import Vegas.Examples.CommitSeedSignallingRealization
import Vegas.Examples.CommitSeedSignallingSubmissionShape

/-! # The actual assessed value after a known wrong-slot Alice declaration -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

theorem recorded_helper_seed_iff_receipt (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (entry : app.PlayerEntry) (recorded : entry ∈ execution.recall alice)
    (request : PhaseRuntimeState.requests entry.beforeView.application.2 alice
      (originalCoordinate alice))
    (clock : entry.beforeView.application.2.native.clock = 2)
    (marker : Message Player (CommitAttemptPacket graph))
    (sender : marker.sender = bob) (addressed : marker.payload.attempt = originalAttempt)
    (visible : marker ∈ entry.beforeView.messages.leaked ∨
      marker ∈ entry.beforeView.messages.ledger) :
    seedBits seed alice = true ↔
      ∃ accepted, (marker.id, accepted) ∈ entry.beforeView.receipts := by
  obtain ⟨before, prior, _kept, active, observed, _allowed, _later⟩ :=
    rawMenu.recorded_response_prefix initial horizon (family seed)
      ⟨remaining, none, execution⟩ trace alice entry recorded
  have valid := raw_native_valid (family seed) before
    (rawMenu.toRawTrace initial horizon (family seed) prior)
  have publicHere : PhaseRuntimeState.requests before.execution.application.publicView alice
      (originalCoordinate alice) := by
    rw [observed] at request
    exact request
  have requested := (before.execution.application.requests_publicView valid alice
    (originalCoordinate alice)).mp publicHere
  rw [observed] at clock visible ⊢
  exact alice_helper_clock_two_seed seed before prior active requested clock marker sender
    addressed visible

/-- The incumbent's unchanged whole continuation gives exactly minus one
following a real clean wrong-slot declaration at a receipted-helper input.
The original seed is read from each actual terminal history's retained input. -/
theorem raw_wrong_helper_binding_assessed_value
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (remaining : Nat) (execution : app.Execution)
    (trace : rawProtocol.Trace (some ⟨remaining, none, execution⟩))
    (clean : OwnPermitted alice execution)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (entry : app.PlayerEntry) (recorded : entry ∈ execution.recall alice)
    (request : PhaseRuntimeState.requests entry.beforeView.application.2 alice
      (originalCoordinate alice))
    (clock : entry.beforeView.application.2.native.clock = 2)
    (message : Message Player (CommitAttemptPacket graph)) (emitted : entry.emitted = some message)
    (packet : PhaseSeedScheduler.ownPacket (originalCoordinate alice) alice message = true)
    (marker : Message Player (CommitAttemptPacket graph))
    (sender : marker.sender = bob) (addressed : marker.payload.attempt = originalAttempt)
    (visible : marker ∈ entry.beforeView.messages.leaked ∨
      marker ∈ entry.beforeView.messages.ledger)
    (receipted : ∃ accepted, (marker.id, accepted) ∈ entry.beforeView.receipts) :
    expect (app.finish initial horizon scheduler
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
      (some ⟨remaining, none, execution⟩)) (fun state => netPayoff state alice) = -1 := by
  let history : rawProtocol.History := ⟨some ⟨remaining, none, execution⟩, trace⟩
  let players := rawMenu.decodeProfile initial horizon scheduler assessment.strategy
  have law := raw_terminal_state_law assessment.strategy history
  change (rawModel.runBehavioralTerminalFrom canonicalCertificate assessment.strategy history).map
    History.state = app.finish initial horizon scheduler players
      (some ⟨remaining, none, execution⟩) at law
  rw [← law, expect_map, ← expect_constant _ (-1 : ℝ)]
  apply expect_congr_on_support
  intro final supported
  have retained := supported
  rw [rawModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded canonicalCertificate
    (rawMenu.bounded initial horizon scheduler)] at retained
  have own := raw_equilibrium_ownPermitted_run assessment equilibrium alice (2 * horizon + 1)
    history final clean retained
  have physical : final.state ∈ ((rawModel.runBehavioralTerminalFrom canonicalCertificate
      assessment.strategy history).map History.state).support := by
    rw [PMF.support_map]
    exact ⟨final, supported, rfl⟩
  rw [law] at physical
  change final.state ∈ (((PMF.pure execution).bind
    (app.runRounds scheduler players remaining)).map app.finished).support at physical
  rw [PMF.pure_bind] at physical
  obtain ⟨after, rounds, stateEq⟩ := PMF.support_map .. ▸ physical
  have finalState : final.state = some (⟨0, none, after⟩ : app.Control) := stateEq.symm
  have terminal := rawModel.runBehavioralTerminalFrom_support_terminal canonicalCertificate
    assessment.strategy history final supported
  have finalTrace : rawProtocol.Trace (some ⟨0, none, after⟩) := finalState ▸ final.trace
  have raw := rawMenu.toRawTrace initial horizon scheduler finalTrace
  rw [finalState] at terminal own
  have complete := scheduler_completesPlay ⟨0, none, after⟩ raw terminal
  have quietAfter : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ after.recall alice :=
    runRounds_recall_mono scheduler players remaining execution after rounds alice quiet
  have remembered : entry ∈ after.recall alice :=
    runRounds_recall_mono scheduler players remaining execution after rounds alice recorded
  obtain ⟨seed, supportedSeed⟩ :=
    (implementation.posterior after.environmentRecall).support_nonempty
  obtain ⟨_originalSupport, ⟨fixed⟩⟩ := menu_original_posterior_trace rawMenu
    ⟨0, none, after⟩ finalTrace seed supportedSeed
  have bit := (recorded_helper_seed_iff_receipt seed 0 after fixed entry remembered request clock
    marker sender addressed visible).mpr receipted
  have excluded := alice_wrong_packet_excluded_of_initial_wait seed after finalTrace fixed
    quietAfter bit own entry remembered request clock message emitted packet
  change rawPayoff alice final = -1
  rw [rawPayoff_terminal_formula final ⟨0, none, after⟩ finalState complete alice own,
    ite_eq_left excluded]

private theorem alice_counted_binding_material (remaining : Nat) (execution : app.Execution)
    (trace : countedProtocol.Trace (some ⟨remaining, some alice, execution⟩))
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (material : WitnessedSubmission graph)
    (allowed : (⟨some material⟩ : app.Action) ∈ countedMenu.actions alice
      (execution.recall alice) (execution.observe app alice)) :
    ∃ serial preparation evidence,
      material = ⟨⟨.commitment aliceBinding (alice, .prepared serial), preparation⟩, evidence⟩ := by
  have original : execution.application.attempt = originalAttempt := request.1.symm
  have requested : execution.application.SeedRequest alice
      ⟨execution.application.attempt, aliceBinding⟩ := by
    simpa only [original, originalCoordinate, bindingEvent, ite_true] using request
  have shaped : ∃ (serial : Nat) (preparation : Option (Raw simpleExpr))
      (evidence : EvidenceRequest graph),
      material = ⟨⟨.commitment aliceBinding (alice, .prepared serial), preparation⟩, evidence⟩ ∧
        serial < bounds.candidateCount ∧
        execution.application.current.native.candidates.lookup (alice, .prepared serial) =
          .fresh :=
    counted_submission_binding_shape scheduler remaining execution alice trace aliceBinding .bool
      binding_layouts.1 requested material allowed
  obtain ⟨serial, preparation, evidence, shape, _bounded, _fresh⟩ := shaped
  exact ⟨serial, preparation, evidence, shape⟩

private theorem alice_original_binding_envelope (execution : app.Execution)
    (original : execution.application.attempt = originalAttempt)
    (material : WitnessedSubmission graph)
    (serial : Nat) (preparation : Option (Raw simpleExpr)) (evidence : EvidenceRequest graph)
    (shape : material =
      ⟨⟨.commitment aliceBinding (alice, .prepared serial), preparation⟩, evidence⟩) :
    PhaseSeedScheduler.ownPacket (originalCoordinate alice) alice
      (⟨(alice, execution.network.nextSerial alice),
        app.packet (app.submit execution.application alice material) alice
          (execution.network.known alice) material⟩ :
          Message Player (CommitAttemptPacket graph)) = true := by
  let message : Message Player (CommitAttemptPacket graph) :=
    ⟨(alice, execution.network.nextSerial alice),
      app.packet (app.submit execution.application alice material) alice
        (execution.network.known alice) material⟩
  have packetAttempt : message.payload.attempt = originalAttempt := by
    change ((execution.application.submit alice material).emit alice
      (execution.network.known alice) material).attempt = originalAttempt
    rw [PhaseCount.emit_after_submit]
    exact original
  have packetCall : message.payload.packet.call =
      .commitment aliceBinding (alice, .prepared serial) := by
    change ((execution.application.submit alice material).emit alice
      (execution.network.known alice) material).packet.call = _
    rw [phase_emit_call, shape]
  change PhaseSeedScheduler.ownPacket (originalCoordinate alice) alice message = true
  simp only [PhaseSeedScheduler.ownPacket, Message.sender, packetAttempt, packetCall,
    originalCoordinate, bindingEvent, ite_true, Payload.event?, and_self]
  apply decide_eq_true
  exact ⟨rfl, trivial⟩

private theorem wrong_helper_binding_value_on_same_information
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (current : source.state = some ⟨remaining, some alice, execution⟩)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (material : app.Submission)
    (allowed : (⟨some material⟩ : app.Action) ∈ countedMenu.actions alice
      (execution.recall alice) (execution.observe app alice))
    (marker : Message Player (CommitAttemptPacket graph))
    (sender : marker.sender = bob) (addressed : marker.payload.attempt = originalAttempt)
    (visible : marker ∈ (execution.observe app alice).messages.leaked ∨
      marker ∈ (execution.observe app alice).messages.ledger)
    (receipted : ∃ accepted, (marker.id, accepted) ∈ (execution.observe app alice).receipts)
    (target : rawModel.InformationHistory alice (countedModel.infoOf alice source.trace)) :
    ∃ count next, target.1.state = some (⟨count, some alice, next⟩ : app.Control) ∧
      expect (app.finish initial horizon scheduler
        (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
        (some ⟨count, none, next.respond app alice ⟨some material⟩⟩))
          (fun state => netPayoff state alice) = -1 := by
  obtain ⟨count, next, state, recalled, observed⟩ :=
    raw_information_control_of_counted_view source remaining execution alice current target
  have sourceTrace : countedProtocol.Trace (some ⟨remaining, some alice, execution⟩) :=
    current ▸ source.trace
  have targetTrace : rawProtocol.Trace (some ⟨count, some alice, next⟩) := state ▸ target.1.trace
  have sourceRaw := countedMenu.toRawTrace initial horizon scheduler sourceTrace
  have targetRaw := rawMenu.toRawTrace initial horizon scheduler targetTrace
  have sourceValid := raw_native_valid scheduler ⟨remaining, some alice, execution⟩ sourceRaw
  have sourceOriginal : execution.application.attempt = originalAttempt := request.1.symm
  obtain ⟨serial, preparation, evidence, shape⟩ :=
    alice_counted_binding_material remaining execution sourceTrace request material allowed
  have publicSource := (execution.application.requests_publicView sourceValid alice
    (originalCoordinate alice)).mpr request
  have publicTarget : PhaseRuntimeState.requests next.application.publicView alice
      (originalCoordinate alice) := by
    change PhaseRuntimeState.requests (next.observe app alice).application.2 alice _
    rw [observed]
    exact publicSource
  have allowedHere : (⟨some material⟩ : app.Action) ∈ countedMenu.actions alice
      (next.recall alice) (next.observe app alice) := by
    rw [recalled, observed]
    exact allowed
  have rawAllowed := ((PhaseCount.mem_onePacketActions runtime leaks bounds alice _ _ _).mp
    allowedHere).1
  have sourceClean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun value _ => PhaseCount.countClean_initial runtime leaks value) source.trace
  rw [current] at sourceClean
  have sourceOwn : OwnPermitted alice execution :=
    ⟨sourceClean.1, fun message member _ => sourceClean.2 message member⟩
  have targetRecall := PhaseCount.countRecall_history runtime leaks targetRaw
  have clean : OwnPermitted alice next :=
    (ownPermitted_iff_past alice next targetRecall).mpr (by
      rw [recalled]
      exact (ownPermitted_iff_past alice execution sourceOwn.1).mp sourceOwn)
  obtain ⟨respondedTrace⟩ := rawMenu.trace_respond initial horizon scheduler count next alice
    ⟨some material⟩ targetTrace rawAllowed
  let action : app.Action := ⟨some material⟩
  let responded := next.respond app alice action
  let entry := originalResponseEntry next alice action
  let message : Message Player (CommitAttemptPacket graph) :=
    ⟨(alice, next.network.nextSerial alice), app.packet (app.submit next.application alice material)
      alice (next.network.known alice) material⟩
  have cleanAfter : OwnPermitted alice responded :=
    ownPermitted_counted_respond alice next action clean allowedHere
  have quietHere : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ next.recall alice :=
    recalled.symm ▸ quiet
  have quietAfter : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ responded.recall alice :=
    app.respond_recall_mono next alice alice action quietHere
  have recorded : entry ∈ responded.recall alice := by
    change entry ∈ (next.respond app alice action).recall alice
    rw [respond_originalResponseEntry]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have requested : PhaseRuntimeState.requests entry.beforeView.application.2 alice
      (originalCoordinate alice) := publicTarget
  have clockHere : entry.beforeView.application.2.native.clock = 2 := by
    change (next.observe app alice).application.2.native.clock = 2
    rw [observed]
    exact clock
  have emitted : entry.emitted = some message := rfl
  have originalHere : next.application.attempt = originalAttempt := by
    have same := congrArg (fun view : app.PlayerView => view.application.2.attempt) observed
    exact same.trans sourceOriginal
  have packet : PhaseSeedScheduler.ownPacket (originalCoordinate alice) alice message = true :=
    alice_original_binding_envelope next originalHere material serial preparation evidence shape
  have visibleHere : marker ∈ entry.beforeView.messages.leaked ∨
      marker ∈ entry.beforeView.messages.ledger := by
    change marker ∈ (next.observe app alice).messages.leaked ∨
      marker ∈ (next.observe app alice).messages.ledger
    rw [observed]
    exact visible
  have receiptedHere : ∃ accepted, (marker.id, accepted) ∈ entry.beforeView.receipts := by
    change ∃ accepted, (marker.id, accepted) ∈ (next.observe app alice).receipts
    rw [observed]
    exact receipted
  refine ⟨count, next, state, ?_⟩
  exact raw_wrong_helper_binding_assessed_value assessment equilibrium count responded
    respondedTrace cleanAfter quietAfter entry recorded requested clockHere message emitted packet
      marker sender addressed visibleHere receiptedHere

open Classical in
/-- Every nonsilent counted current response at the clock-two helper input
with a published Bob packet has committed value minus one at EVERY compatible
raw history. The unchanged incumbent continuation and its actual own-clean
support are retained; no assessed reach or seed-fairness premise is imposed. -/
theorem raw_wrong_helper_binding_fiber_committed_value
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (current : source.state = some ⟨remaining, some alice, execution⟩)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (material : app.Submission)
    (allowed : (⟨some material⟩ : app.Action) ∈ countedMenu.actions alice
      (execution.recall alice) (execution.observe app alice))
    (marker : Message Player (CommitAttemptPacket graph))
    (sender : marker.sender = bob) (addressed : marker.payload.attempt = originalAttempt)
    (visible : marker ∈ (execution.observe app alice).messages.leaked ∨
      marker ∈ (execution.observe app alice).messages.ledger)
    (receipted : ∃ accepted, (marker.id, accepted) ∈ (execution.observe app alice).receipts)
    (site : rawModel.InformationSite alice)
    (atSite : site.1 = countedModel.infoOf alice source.trace)
    (choice : rawModel.Choice alice site.1) (selected : choice.1 = some ⟨some material⟩)
    (target : rawModel.InformationHistory alice site.1) :
    expect (rawModel.runBehavioralTerminalFrom canonicalCertificate
      (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy alice
        ((assessment.strategy alice).commit site.1 choice)) target.1) (rawPayoff alice) = -1 := by
  let retained : rawModel.InformationHistory alice (countedModel.infoOf alice source.trace) :=
    ⟨target.1, target.2.trans atSite⟩
  obtain ⟨count, next, state, value⟩ := wrong_helper_binding_value_on_same_information assessment
    equilibrium source remaining execution current request clock quiet material allowed marker
      sender addressed visible receipted retained
  have bound := app.trace_bound initial horizon scheduler
    (rawMenu.toRawTrace initial horizon scheduler target.1.trace)
  have projection := rawMenu.run_local_law_finish_of_information initial horizon scheduler
    assessment.strategy target.1 alice count next state site.1 target.2 (PMF.pure choice)
      (2 * horizon) ((Nat.le_add_left _ _).trans bound)
  change (rawModel.runBehavioralFrom
    (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy alice
      ((assessment.strategy alice).commit site.1 choice)) (2 * horizon + 1) target.1).map
        History.state = _ at projection
  rw [PMF.pure_map, selected, Option.getD_some, PMF.pure_bind] at projection
  have terminalProjection : (rawModel.runBehavioralTerminalFrom canonicalCertificate
      (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy alice
        ((assessment.strategy alice).commit site.1 choice)) target.1).map History.state =
      app.finish initial horizon scheduler
        (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
        (some ⟨count, none, next.respond app alice ⟨some material⟩⟩) := by
    rw [rawModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded canonicalCertificate
      (rawMenu.bounded initial horizon scheduler)]
    exact projection
  have expected := congrArg (fun law : PMF app.ProtocolState =>
    expect law (fun state => netPayoff state alice)) terminalProjection
  rw [expect_map] at expected
  exact expected.trans value

open Classical in
/-- The same minus-one value integrates against the assessment's actual
belief, including at a site of zero assessed reach. -/
theorem raw_wrong_helper_binding_context_value
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (current : source.state = some ⟨remaining, some alice, execution⟩)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (material : app.Submission)
    (allowed : (⟨some material⟩ : app.Action) ∈ countedMenu.actions alice
      (execution.recall alice) (execution.observe app alice))
    (marker : Message Player (CommitAttemptPacket graph))
    (sender : marker.sender = bob) (addressed : marker.payload.attempt = originalAttempt)
    (visible : marker ∈ (execution.observe app alice).messages.leaked ∨
      marker ∈ (execution.observe app alice).messages.ledger)
    (receipted : ∃ accepted, (marker.id, accepted) ∈ (execution.observe app alice).receipts)
    (site : rawModel.InformationSite alice)
    (atSite : site.1 = countedModel.infoOf alice source.trace)
    (choice : rawModel.Choice alice site.1) (selected : choice.1 = some ⟨some material⟩) :
    (assessment.continuationContext canonicalCertificate site (rawPayoff alice)).value
      ((assessment.strategy alice).commit site.1 choice) = -1 := by
  have integrable := assessment.continuationContext_integrable_of_bounded_terminal
    canonicalCertificate site (rawPayoff alice) 6 (fun final _ => rawPayoff_abs_le alice final)
      ((assessment.strategy alice).commit site.1 choice)
  change (assessment.continuationContextWith
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site (rawPayoff alice)).value
      ((assessment.strategy alice).commit site.1 choice) = -1
  rw [assessment.continuationContextWith_value_tower
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site (rawPayoff alice)
      ((assessment.strategy alice).commit site.1 choice) integrable,
    ← expect_constant (assessment.belief alice site) (-1 : ℝ)]
  apply expect_congr_on_support
  intro target _
  exact raw_wrong_helper_binding_fiber_committed_value assessment equilibrium source remaining
    execution current request clock quiet material allowed marker sender addressed visible receipted
      site atSite choice selected target

end Vegas.Examples.CommitSeedSignalling
