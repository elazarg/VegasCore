/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingHelperOmission
import Vegas.Examples.CommitSeedSignallingHelperBindingValue

/-! # Withholding the known eligible original declaration loses the exclusion stake -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob)

/-- An actual omitted eligible response has value minus one under the
unchanged assessed continuation. The eligibility bit is recovered from an
authentic retained helper observation on each terminal history. -/
theorem raw_helper_binding_wait_assessed_value
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
    (bit : Bool) (clock : entry.beforeView.application.2.native.clock = if bit then 3 else 2)
    (omitted : entry.action.transmission = none)
    (helper : app.PlayerEntry) (remembered : helper ∈ execution.recall alice)
    (helperRequest : PhaseRuntimeState.requests helper.beforeView.application.2 alice
      (originalCoordinate alice))
    (helperClock : helper.beforeView.application.2.native.clock = 2)
    (marker : Message Player (CommitAttemptPacket graph))
    (sender : marker.sender = bob) (addressed : marker.payload.attempt = originalAttempt)
    (visible : marker ∈ helper.beforeView.messages.leaked ∨
      marker ∈ helper.beforeView.messages.ledger)
    (readout : (∃ accepted, (marker.id, accepted) ∈ helper.beforeView.receipts) ↔ bit = true) :
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
  have quietAfter := runRounds_recall_mono scheduler players remaining execution after rounds alice
    quiet
  have entryAfter := runRounds_recall_mono scheduler players remaining execution after rounds alice
    recorded
  have helperAfter := runRounds_recall_mono scheduler players remaining execution after rounds alice
    remembered
  obtain ⟨seed, supportedSeed⟩ :=
    (implementation.posterior after.environmentRecall).support_nonempty
  obtain ⟨_originalSupport, ⟨fixed⟩⟩ := menu_original_posterior_trace rawMenu
    ⟨0, none, after⟩ finalTrace seed supportedSeed
  have decoded := recorded_helper_seed_iff_receipt seed 0 after fixed helper helperAfter
    helperRequest helperClock marker sender addressed visible
  have bitEq : seedBits seed alice = bit := by
    have same : seedBits seed alice = true ↔ bit = true := decoded.trans readout
    cases value : seedBits seed alice <;> cases bit <;> simp_all
  have eligible : entry.beforeView.application.2.native.clock =
      lateClock alice (seedBits seed alice) := by
    rw [bitEq]
    cases bit <;> simpa [lateClock] using clock
  have excluded := alice_eligible_wait_excluded seed after finalTrace fixed quietAfter entry
    entryAfter request eligible omitted
  change rawPayoff alice final = -1
  rw [rawPayoff_terminal_formula final ⟨0, none, after⟩ finalState complete alice own,
    ite_eq_left excluded]

open Classical in
/-- At either known eligible binding slot, committing to WAIT gives minus one
under the actual assessment belief on its full raw information set. The helper
observation is either recalled or the current input itself. -/
theorem raw_helper_binding_wait_context_value
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
    (helperRequest : PhaseRuntimeState.requests helper.beforeView.application.2 alice
      (originalCoordinate alice))
    (helperClock : helper.beforeView.application.2.native.clock = 2)
    (marker : Message Player (CommitAttemptPacket graph))
    (sender : marker.sender = bob) (addressed : marker.payload.attempt = originalAttempt)
    (visible : marker ∈ helper.beforeView.messages.leaked ∨
      marker ∈ helper.beforeView.messages.ledger)
    (readout : (∃ accepted, (marker.id, accepted) ∈ helper.beforeView.receipts) ↔ bit = true)
    (site : rawModel.InformationSite alice)
    (atSite : site.1 = countedModel.infoOf alice source.trace)
    (choice : rawModel.Choice alice site.1) (selected : choice.1 = some ⟨none⟩) :
    (assessment.continuationContext canonicalCertificate site (rawPayoff alice)).value
      ((assessment.strategy alice).commit site.1 choice) = -1 := by
  have fiber (target : rawModel.InformationHistory alice site.1) :
      expect (rawModel.runBehavioralTerminalFrom canonicalCertificate
        (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy alice
          ((assessment.strategy alice).commit site.1 choice)) target.1) (rawPayoff alice) = -1 := by
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
    have publicSource := (execution.application.requests_publicView sourceValid alice
      (originalCoordinate alice)).mpr request
    have publicTarget : PhaseRuntimeState.requests next.application.publicView alice
        (originalCoordinate alice) := by
      change PhaseRuntimeState.requests (next.observe app alice).application.2 alice _
      rw [observed]
      exact publicSource
    have sourceClean :=
      (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
        initial horizon (fun value _ => PhaseCount.countClean_initial runtime leaks value)
          source.trace
    rw [current] at sourceClean
    have sourceOwn : OwnPermitted alice execution :=
      ⟨sourceClean.1, fun message member _ => sourceClean.2 message member⟩
    have targetRecall := PhaseCount.countRecall_history runtime leaks targetRaw
    have clean : OwnPermitted alice next :=
      (ownPermitted_iff_past alice next targetRecall).mpr (by
        rw [recalled]
        exact (ownPermitted_iff_past alice execution sourceOwn.1).mp sourceOwn)
    have allowed : (⟨none⟩ : app.Action) ∈ countedMenu.actions alice
        (next.recall alice) (next.observe app alice) :=
      PhaseCount.silence_onePacket runtime leaks bounds alice _ _
    have rawAllowed := ((PhaseCount.mem_onePacketActions runtime leaks bounds alice _ _ _).mp
      allowed).1
    obtain ⟨respondedTrace⟩ := rawMenu.trace_respond initial horizon scheduler count next alice
      ⟨none⟩ targetTrace rawAllowed
    let responded := next.respond app alice ⟨none⟩
    let entry := originalResponseEntry next alice ⟨none⟩
    have cleanAfter : OwnPermitted alice responded :=
      ownPermitted_counted_respond alice next ⟨none⟩ clean allowed
    have quietHere : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ next.recall alice :=
      recalled.symm ▸ quiet
    have quietAfter : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ responded.recall alice :=
      app.respond_recall_mono next alice alice ⟨none⟩ quietHere
    have recorded : entry ∈ responded.recall alice := by
      change entry ∈ (next.respond app alice ⟨none⟩).recall alice
      rw [respond_originalResponseEntry]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    have clockHere : entry.beforeView.application.2.native.clock = if bit then 3 else 2 := by
      change (next.observe app alice).application.2.native.clock = _
      rw [observed]
      exact clock
    have helperAfter : helper ∈ responded.recall alice := by
      rcases remembered with old | same
      · exact app.respond_recall_mono next alice alice ⟨none⟩ (recalled.symm ▸ old)
      · have sameInput : originalResponseEntry next alice ⟨none⟩ =
            originalResponseEntry execution alice ⟨none⟩ := by
          simp only [originalResponseEntry, observed, Option.map_none]
        rw [same, ← sameInput]
        exact recorded
    have value := raw_helper_binding_wait_assessed_value assessment equilibrium count responded
      respondedTrace cleanAfter quietAfter entry recorded publicTarget bit clockHere rfl helper
        helperAfter helperRequest helperClock marker sender addressed visible readout
    have bound := app.trace_bound initial horizon scheduler targetRaw
    have enough : app.rank horizon target.1.state ≤ 2 * horizon + 1 := by
      rw [state]
      exact (Nat.le_add_left _ _).trans bound
    have projection := rawMenu.run_local_law_finish_of_information initial horizon scheduler
      assessment.strategy target.1 alice count next state site.1 target.2 (PMF.pure choice)
        (2 * horizon) enough
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
          (some ⟨count, none, responded⟩) := by
      rw [rawModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded canonicalCertificate
        (rawMenu.bounded initial horizon scheduler)]
      exact projection
    have expected := congrArg (fun law : PMF app.ProtocolState =>
      expect law (fun state => netPayoff state alice)) terminalProjection
    rw [expect_map] at expected
    exact expected.trans value
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
  exact fiber target

end Vegas.Examples.CommitSeedSignalling
