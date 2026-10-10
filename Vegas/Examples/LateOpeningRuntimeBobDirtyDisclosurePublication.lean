/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeGame
import Vegas.Examples.LateOpeningRuntimeBobDirtyOptimization
import Vegas.Examples.LateOpeningRuntimeAliceFullFiberFloor
import Vegas.Examples.LateOpeningRuntimeAliceSuccessFloor
import Vegas.Examples.LateOpeningRuntimeOptionalPacket
import Vegas.Examples.LateOpeningRuntimeBobDirtyOptionalFiber
import Vegas.Examples.LateOpeningRuntimeBobDirtyFinalFiber
import Vegas.Examples.LateOpeningRuntimeBobDisclosurePublication

/-! # Actual publication after a sunk rejected Bob receipt

Every supported continuation of a successful binding retains the incumbent
future strategy. Full information-class rationality rules out failed optional
disclosure and forces final publication when the optional callback stays ready.
The resulting payoff floor includes the unchanged actual audit deduction.
-/

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeBobDirtyDisclosurePublication
open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeBobSuccessPayoff
variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (reward forfeit : ℝ) (deposit : Player → ℝ)
  (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
theorem final_response_publication
    (execution : app.Execution) (answer : Answer)
    (bound : execution.application.config.store (.inr bobBindEvent) = some (.success answer))
    (ready : execution.application.config.cut.Ready bobRevealEvent)
    (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobRevealEvent)
    (serial : Nat) (rejected : ((bob, serial), false) ∈ execution.receipts)
    (boundedTrace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨6, some bob, execution⟩))
    (forfeitPositive : 0 < forfeit)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeGame.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (response : app.Action)
    (supported : response ∈ (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob
        (execution.recall bob) (execution.observe app bob)).support)
    (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 6 (execution.respond app bob response)).support) :
    final.application.config.store (.inr bobRevealEvent) = some (.success answer) := by
  have executionTrace := rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) boundedTrace
  let history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).History :=
    ⟨some ⟨6, some bob, execution⟩, boundedTrace⟩
  have running : ¬ (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).terminal history.state := by
    change ¬ (6 = 0 ∧ some bob = none)
    simp
  obtain ⟨site, same⟩ := (LateOpeningRuntimeGame.model weight nonnegative)
    |>.exists_informationSite_of_active bob history running rfl
  let representative : (LateOpeningRuntimeGame.model weight nonnegative).InformationHistory
      bob site.1 := ⟨history, same.symm⟩
  have current : representative.1.state = some ⟨6, some bob, execution⟩ := rfl
  have info : site.1 = some (execution.recall bob, execution.observe app bob) := by
    rw [← representative.2]
    change (rawMenu.signals _ _ _).infoOf bob representative.1.trace = _
    rw [rawMenu.info, current]
    rfl
  have selected : response ∈ ((assessment.strategy bob site.1).map
      (fun choice => choice.1.getD ⟨none⟩)).support := by
    rw [info]
    unfold ReactiveApplication.ResponseMenu.decodeProfile ReactiveApplication.decodePolicy
      ReactiveApplication.ResponseMenu.embedPolicy at supported
    rw [PMF.map_comp] at supported
    exact supported
  have valid := LateOpeningRuntimeBobInformation.executionOfInformation_spec weight nonnegative
    site representative execution executionTrace current representative
  have recovered : (LateOpeningRuntimeBobInformation.executionOfInformation weight nonnegative
      site representative execution executionTrace current representative) = execution := by
    have states := congrArg (fun state : Option app.Control =>
      state.map (fun control => control.execution)) (current.symm.trans valid.1)
    simpa only [Option.map_some, Option.some.injEq] using states.symm
  have localRational := rational bob site
  dsimp only at localRational
  rw [assessment.continuationContext_eq_truncated_of_bounded
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative))] at localRational
  apply LateOpeningRuntimeBobDirtyFinalFiber.rational_supported_publication weight nonnegative
    site representative execution executionTrace current answer bound ready timely serial rejected
    reward forfeit deposit forfeitPositive assessment localRational representative response selected
    players final
  rwa [recovered]

theorem optional_response_not_failure
    (execution : app.Execution) (answer : Answer)
    (bound : execution.application.config.store (.inr bobBindEvent) = some (.success answer))
    (ready : execution.application.config.cut.Ready bobRevealEvent)
    (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobRevealEvent)
    (serial : Nat) (rejected : ((bob, serial), false) ∈ execution.receipts)
    (boundedTrace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨12, some bob, execution⟩))
    (forfeitPositive : 0 < forfeit)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeGame.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (response : app.Action)
    (supported : response ∈ (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob
        (execution.recall bob) (execution.observe app bob)).support)
    : (LateOpeningRuntimeBobFinalObservation.serviced execution response).application.config.store
      (.inr bobRevealEvent) ≠ some .failure := by
  have executionTrace := rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) boundedTrace
  let history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).History :=
    ⟨some ⟨12, some bob, execution⟩, boundedTrace⟩
  have running : ¬ (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).terminal history.state := by
    change ¬ (12 = 0 ∧ some bob = none)
    simp
  obtain ⟨site, same⟩ := (LateOpeningRuntimeGame.model weight nonnegative)
    |>.exists_informationSite_of_active bob history running rfl
  let representative : (LateOpeningRuntimeGame.model weight nonnegative).InformationHistory
      bob site.1 := ⟨history, same.symm⟩
  have current : representative.1.state = some ⟨12, some bob, execution⟩ := rfl
  have info : site.1 = some (execution.recall bob, execution.observe app bob) := by
    rw [← representative.2]
    change (rawMenu.signals _ _ _).infoOf bob representative.1.trace = _
    rw [rawMenu.info, current]
    rfl
  have localRational := rational bob site
  dsimp only at localRational
  rw [assessment.continuationContext_eq_truncated_of_bounded
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative))] at localRational
  exact LateOpeningRuntimeBobDirtyOptionalFiber.rational_supported_response_not_failure
    weight nonnegative site representative execution executionTrace current answer bound ready
    timely
    serial rejected reward forfeit deposit forfeitPositive assessment localRational response
    supported

theorem unpublished_optional_publication
    (execution : app.Execution) (answer : Answer)
    (boundedTrace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨12, some bob, execution⟩))
    (bound : execution.application.config.store (.inr bobBindEvent) = some (.success answer))
    (ready : execution.application.config.cut.Ready bobRevealEvent)
    (timer : execution.application.activatedAt bobRevealEvent = some 3)
    (clock : execution.application.clock = 3)
    (serial : Nat) (rejected : ((bob, serial), false) ∈ execution.receipts)
    (forfeitPositive : 0 < forfeit)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeGame.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (response : app.Action)
    (supported : response ∈ (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob
        (execution.recall bob) (execution.observe app bob)).support)
    (unpublished : (LateOpeningRuntimeBobFinalObservation.serviced
      execution response).application.config.store (.inr bobRevealEvent) = none)
    (players : Player → app.Policy)
    (bobPolicy : players bob = rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 12 (execution.respond app bob response)).support) :
    final.application.config.store (.inr bobRevealEvent) = some (.success answer) := by
  let decoded := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy
  have covered := rawMenu.decode_embedPolicy_covered initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)
  have executionTrace := rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) boundedTrace
  let first := LateOpeningRuntimeBobFinalObservation.serviced execution response
  have preserved := LateOpeningRuntimeOptionalPacket.unpublished_service_preserves
    weight nonnegative execution executionTrace response ready unpublished
  have firstBound : first.application.config.store (.inr bobBindEvent) =
      some (.success answer) := by
    rw [preserved.1]
    exact bound
  have firstReady : first.application.config.cut.Ready bobRevealEvent := by
    rw [preserved.1]
    exact ready
  have firstTimer : first.application.activatedAt bobRevealEvent = some 3 := by
    rw [preserved.2.2]
    exact timer
  have firstClock : first.application.clock = 3 := preserved.2.1.trans clock
  obtain ⟨respondedTrace⟩ := rawMenu.trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 12 execution bob response boundedTrace
      (covered bob (assessment.strategy bob) _ _ response supported)
  obtain ⟨firstTrace⟩ := rawMenu.trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) decoded
      (fun who => covered who (assessment.strategy who)) 11 1 _ first respondedTrace (by
        simp only [ReactiveApplication.runRounds, PMF.bind_pure]
        change first ∈ (app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
          decoded (execution.respond app bob response)).support
        rw [LateOpeningRuntimeBobFinalObservation.serviced_round weight nonnegative 12
          execution executionTrace response decoded]
        exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  have firstPosition : first.environmentRecall.length = 15 := by
    have counted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)
      (rawMenu.toRawTrace _ _ _ firstTrace)
    change first.environmentRecall.length + 11 = 26 at counted
    omega
  let before := LateOpeningRuntimeBobDisclosureChronology.beforeFinalAfterService first
  have prefixLaw := LateOpeningRuntimeBobDisclosureChronology.live_prefix_law weight nonnegative
    first
    decoded firstPosition firstReady
  obtain ⟨beforeTrace⟩ := rawMenu.trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) decoded
      (fun who => covered who (assessment.strategy who)) 7 4 first before firstTrace (by
        rw [prefixLaw]
        exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  rw [app.runRounds_add (LateOpeningRuntimeService.scheduler weight nonnegative) players 1 11,
    show app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 1
      (execution.respond app bob response) = PMF.pure first from by
        simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using
          LateOpeningRuntimeBobFinalObservation.serviced_round weight nonnegative 12 execution
            executionTrace response players, PMF.pure_bind,
    app.runRounds_add (LateOpeningRuntimeService.scheduler weight nonnegative) players 4 7,
    LateOpeningRuntimeBobDisclosureChronology.live_prefix_law weight nonnegative first players
      firstPosition firstReady, PMF.pure_bind] at reached
  obtain ⟨next, advanced, suffix⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
  have position : before.environmentRecall.length = 19 := by
    have counted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)
      (rawMenu.toRawTrace _ _ _ beforeTrace)
    change before.environmentRecall.length + 7 = 26 at counted
    omega
  have chosen : LateOpeningRuntimeService.scheduler weight nonnegative before.environmentRecall
      (before.observeEnvironment app) = PMF.pure (.activate bob) := by
    change stageChoice weight nonnegative _ _ = _
    rw [position]
    rfl
  rw [ReactiveApplication.round, chosen, PMF.pure_bind, ReactiveApplication.dispatch] at advanced
  obtain ⟨observed, sampled, responded⟩ := (PMF.mem_support_bind_iff _ _ _).mp advanced
  obtain ⟨lastResponse, lastSelected, rfl⟩ := PMF.support_map .. ▸ responded
  obtain ⟨⟨observedRawTrace⟩, observedBound, observedReady, observedTimely, _⟩ :=
    LateOpeningRuntimeBobDisclosureChronology.final_of_live_prefix weight nonnegative first answer
      (rawMenu.toRawTrace _ _ _ firstTrace) firstBound firstReady firstTimer firstClock observed
        sampled
  obtain ⟨observedTrace⟩ := rawMenu.trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 6 before observed (.activate bob)
      beforeTrace (by rw [chosen]; exact (PMF.mem_support_pure_iff _ _).mpr rfl) sampled
  have lastSupported : lastResponse ∈ (decoded bob (observed.recall bob)
      (observed.observe app bob)).support := by
    change lastResponse ∈ (players bob _ _).support at lastSelected
    rwa [bobPolicy] at lastSelected
  have firstRejected : ((bob, serial), false) ∈ first.receipts := by
    have respondedRejected : ((bob, serial), false) ∈
        (execution.respond app bob response).receipts := by
      rw [app.respond_receipts]
      exact rejected
    apply (app.receipt_policyInvariant decoded ((bob, serial), false)).runRounds
      (LateOpeningRuntimeService.scheduler weight nonnegative) 1 _ first respondedRejected
    simp only [ReactiveApplication.runRounds, PMF.bind_pure]
    rw [LateOpeningRuntimeBobFinalObservation.serviced_round weight nonnegative 12 execution
      executionTrace response decoded]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have beforeRejected := (app.receipt_policyInvariant decoded ((bob, serial), false)).runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) 4 first before firstRejected (by
      rw [prefixLaw]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  have observedRejected := (app.environmentStep_receipts_prefix before observed (.activate bob)
    sampled).subset beforeRejected
  exact final_response_publication weight nonnegative reward forfeit deposit assessment observed
    answer observedBound observedReady observedTimely serial observedRejected observedTrace
    forfeitPositive rational lastResponse lastSupported players final suffix

theorem optional_response_publication
    (execution : app.Execution) (answer : Answer)
    (boundedTrace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨12, some bob, execution⟩))
    (bound : execution.application.config.store (.inr bobBindEvent) = some (.success answer))
    (ready : execution.application.config.cut.Ready bobRevealEvent)
    (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobRevealEvent)
    (timer : execution.application.activatedAt bobRevealEvent = some 3)
    (clock : execution.application.clock = 3)
    (serial : Nat) (rejected : ((bob, serial), false) ∈ execution.receipts)
    (forfeitPositive : 0 < forfeit)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeGame.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (response : app.Action)
    (supported : response ∈ (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob
        (execution.recall bob) (execution.observe app bob)).support)
    (players : Player → app.Policy)
    (bobPolicy : players bob = rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 12 (execution.respond app bob response)).support) :
    final.application.config.store (.inr bobRevealEvent) = some (.success answer) := by
  have executionTrace := rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) boundedTrace
  have noFailure := optional_response_not_failure weight nonnegative reward forfeit deposit
    assessment
    execution answer bound ready timely serial rejected boundedTrace forfeitPositive rational
    response
    supported
  let first := LateOpeningRuntimeBobFinalObservation.serviced execution response
  cases stored : first.application.config.store (.inr bobRevealEvent) with
  | none =>
      exact unpublished_optional_publication weight nonnegative reward forfeit deposit assessment
        execution answer boundedTrace bound ready timer clock serial rejected forfeitPositive
        rational
        response supported stored players bobPolicy final reached
  | some result =>
      cases result with
      | failure => exact (noFailure stored).elim
      | success opened =>
          have firstReached : first ∈ (app.runRounds
              (LateOpeningRuntimeService.scheduler weight nonnegative) players 1
              (execution.respond app bob response)).support := by
            simp only [ReactiveApplication.runRounds, PMF.bind_pure]
            rw [LateOpeningRuntimeBobFinalObservation.serviced_round weight nonnegative 12
              execution executionTrace response players]
            exact (PMF.mem_support_pure_iff _ _).mpr rfl
          obtain ⟨bit, label, invariant⟩ := history_initial_invariant
            LateOpeningRuntimeService.runtime leaks LateOpeningRuntimeService.horizon
              (LateOpeningRuntimeService.scheduler weight nonnegative)
              ⟨12, some bob, execution⟩ executionTrace
          have same := bob_continuation_success_immutable
            LateOpeningRuntimeService.runtime leaks players
              (LateOpeningRuntimeService.scheduler weight nonnegative) 1 execution first
              _ invariant answer bound response firstReached opened stored
          rw [same] at stored
          rw [app.runRounds_add (LateOpeningRuntimeService.scheduler weight nonnegative)
            players 1 11,
            show app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 1
              (execution.respond app bob response) = PMF.pure first from by
                simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using
                  LateOpeningRuntimeBobFinalObservation.serviced_round weight nonnegative 12
                    execution executionTrace response players, PMF.pure_bind] at reached
          exact (ReactiveApplication.Invariant.policyInvariant app
            (LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks (.inr bobRevealEvent)
              (.success answer)) players).runRounds
                (LateOpeningRuntimeService.scheduler weight nonnegative) 11 first final stored
                reached

theorem binding_response_publication (execution : app.Execution)
    (boundedTrace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (ready : execution.application.config.cut.Ready bobBindEvent)
    (bindingResponse : app.Action) (answer : Answer)
    (available : bindingResponse ∈ rawMenu.actions bob (execution.recall bob)
      (execution.observe app bob))
    (selected : (LateOpeningRuntimeBobFinalObservation.serviced
      execution bindingResponse).application.config.store (.inr bobBindEvent) =
      some (.success answer))
    (serial : Nat) (rejected : ((bob, serial), false) ∈ execution.receipts)
    (forfeitPositive : 0 < forfeit)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeGame.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (players : Player → app.Policy)
    (bobPolicy : players bob = rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 14 (execution.respond app bob bindingResponse)).support) :
    final.application.config.store (.inr bobRevealEvent) = some (.success answer) := by
  let first := LateOpeningRuntimeBobFinalObservation.serviced execution bindingResponse
  have rawTrace := rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) boundedTrace
  obtain ⟨respondedTrace⟩ := rawMenu.trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 execution bob bindingResponse
      boundedTrace available
  let decoded := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy
  obtain ⟨servedTrace⟩ := rawMenu.trace_round initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) decoded
      (fun who => rawMenu.decode_embedPolicy_covered initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) who (assessment.strategy who))
      13 _ first
        respondedTrace (by
          rw [LateOpeningRuntimeBobFinalObservation.serviced_round weight nonnegative 14
            execution rawTrace bindingResponse decoded]
          exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  have servedRaw := rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) servedTrace
  have cursor : first.environmentRecall.length = 13 := by
    have counted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) servedRaw
    change first.environmentRecall.length + 13 = 26 at counted
    omega
  obtain ⟨revealReady, timer, clock⟩ :=
    LateOpeningRuntimeBobBindingChronology.accepted_chronology
      weight nonnegative execution rawTrace ready bindingResponse answer selected
  have completed : bobBindEvent ∈
      first.application.publicView.observation.completionOrder :=
    (first.application.config.history_exact bobBindEvent).mpr
      (revealReady.2 (by decide))
  have chosen : LateOpeningRuntimeService.scheduler weight nonnegative
      first.environmentRecall
        (first.observeEnvironment app) =
          PMF.pure (.activate bob) := by
    change stageChoice weight nonnegative _ _ = _
    rw [cursor]
    change PMF.pure (if bobBindEvent ∈
      first.application.publicView.observation.completionOrder
        then (.activate bob : app.Command) else .wait) = _
    rw [ite_eq_left completed]
  change final ∈ ((app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
    (execution.respond app bob bindingResponse)).bind
      (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 13)).support
    at reached
  rw [LateOpeningRuntimeBobFinalObservation.serviced_round weight nonnegative 14
            execution rawTrace bindingResponse players,
    PMF.pure_bind] at reached
  obtain ⟨next, activated, suffix⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
  rw [ReactiveApplication.round, chosen, PMF.pure_bind, ReactiveApplication.dispatch] at activated
  obtain ⟨observed, sampled, responded⟩ := (PMF.mem_support_bind_iff _ _ _).mp activated
  obtain ⟨response, supported, rfl⟩ := PMF.support_map .. ▸ responded
  obtain ⟨observedTrace⟩ := rawMenu.trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 12 _ observed (.activate bob)
      servedTrace (by
        rw [chosen]
        exact (PMF.mem_support_pure_iff _ _).mpr rfl) sampled
  have physical : observed.application =
      first.application := by
    obtain ⟨updated, supportedSample, rfl⟩ := PMF.support_map .. ▸ sampled
    obtain ⟨sample, _, rfl⟩ := PMF.support_map .. ▸ supportedSample
    rfl
  have observedBound : observed.application.config.store (.inr bobBindEvent) =
      some (.success answer) := by rw [physical]; exact selected
  have observedReady : observed.application.config.cut.Ready bobRevealEvent := by
    rw [physical]; exact revealReady
  have observedTimer : observed.application.activatedAt bobRevealEvent = some 3 := by
    rw [physical]; exact timer
  have observedClock : observed.application.clock = 3 := by rw [physical]; exact clock
  have observedTimely : observed.application.WithinDeadline LateOpeningRuntimeService.runtime
      bobRevealEvent := by
    unfold State.WithinDeadline
    rw [observedTimer, observedClock]
    decide
  have optionalSupported : response ∈ (decoded bob (observed.recall bob)
      (observed.observe app bob)).support := by
    change response ∈ (players bob _ _).support at supported
    rwa [bobPolicy] at supported
  have servedRejected : ((bob, serial), false) ∈
      first.receipts := by
    have respondedRejected : ((bob, serial), false) ∈
        (execution.respond app bob bindingResponse).receipts := by
      rw [app.respond_receipts]
      exact rejected
    apply (app.receipt_policyInvariant decoded ((bob, serial), false)).runRounds
      (LateOpeningRuntimeService.scheduler weight nonnegative) 1 _ _ respondedRejected
    simp only [ReactiveApplication.runRounds, PMF.bind_pure]
    rw [LateOpeningRuntimeBobFinalObservation.serviced_round weight nonnegative 14 execution
      rawTrace bindingResponse decoded]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have observedRejected := (app.environmentStep_receipts_prefix _ observed (.activate bob)
    sampled).subset servedRejected
  exact optional_response_publication weight nonnegative reward forfeit deposit assessment
    observed answer observedTrace observedBound observedReady observedTimely observedTimer
    observedClock serial observedRejected forfeitPositive rational response optionalSupported
    players
    bobPolicy final suffix

theorem dirty_binding_payoff_floor
    (execution : app.Execution)
    (boundedTrace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (ready : execution.application.config.cut.Ready bobBindEvent)
    (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent)
    (dirty : ¬ LateOpeningRuntimeBobBindingService.SilentRecall execution)
    (bit : Bool)
    (published : execution.application.config.store (.inr aliceEvent) =
      some (.success bit : PublicationResult Bool))
    (labelLow : (originalLabel execution).val < 2)
    (rewardNonnegative : 0 ≤ reward) (forfeitPositive : 0 < forfeit)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeGame.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (response : app.Action)
    (supported : response ∈ (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob
        (execution.recall bob) (execution.observe app bob)).support)
    (players : Player → app.Policy)
    (bobPolicy : players bob = rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 14 (execution.respond app bob response)).support) :
    reward / 2 - GameTheory.Enforcement.TerminalAudit.charge
      (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
        (app.finished final) alice * deposit alice ≤
      LateOpeningRuntimeGame.payoff reward forfeit (fun actual => PMF.pure actual)
        deposit (app.finished final) alice := by
  let history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).History :=
    ⟨some ⟨14, some bob, execution⟩, boundedTrace⟩
  have running : ¬ (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).terminal history.state := by
    change ¬ (14 = 0 ∧ some bob = none)
    simp
  obtain ⟨site, same⟩ := (LateOpeningRuntimeGame.model weight nonnegative)
    |>.exists_informationSite_of_active bob history running rfl
  let representative : (LateOpeningRuntimeGame.model weight nonnegative).InformationHistory
      bob site.1 := ⟨history, same.symm⟩
  have current : representative.1.state = some ⟨14, some bob, execution⟩ := rfl
  have localRational := rational bob site
  dsimp only at localRational
  rw [assessment.continuationContext_eq_truncated_of_bounded
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative))] at localRational
  obtain ⟨answer, bound, shape, _⟩ :=
    LateOpeningRuntimeBobDirtyOptimization.rational_supported_binding weight nonnegative site
      representative execution boundedTrace ready current reward forfeit deposit timely dirty bit
      published forfeitPositive.le assessment localRational response supported
  have serviceEq : LateOpeningRuntimeBobFinalObservation.serviced execution response =
      LateOpeningRuntimeBobBindingTransport.servicedBinding execution response := by
    rcases response with ⟨transmission⟩
    cases transmission <;> rfl
  rw [← serviceEq] at bound
  obtain ⟨traffic, _, owner, receipt⟩ :=
    LateOpeningRuntimeBobDirtyPrefix.dirty_binding_history_has_rejected_traffic weight nonnegative
      execution boundedTrace ready dirty
  change traffic.envelope.id.1 = bob at owner
  have identifier : traffic.envelope.id = (bob, traffic.envelope.id.2) := Prod.ext owner rfl
  rw [identifier] at receipt
  have available := rawMenu.decode_embedPolicy_covered initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) bob (assessment.strategy bob)
      _ _ response supported
  have publication := binding_response_publication weight nonnegative reward forfeit deposit
    assessment execution boundedTrace ready response answer available bound traffic.envelope.id.2
    receipt forfeitPositive rational players bobPolicy final reached
  exact LateOpeningRuntimeAliceSuccessFloor.continuation_payoff_floor weight nonnegative execution
    (rawMenu.toRawTrace _ _ _ boundedTrace) bit published response players final reached answer
    publication shape labelLow reward forfeit rewardNonnegative deposit
    (fun actual => PMF.pure actual)

theorem binding_payoff_floor
    (execution : app.Execution)
    (boundedTrace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (ready : execution.application.config.cut.Ready bobBindEvent)
    (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent)
    (bit : Bool)
    (published : execution.application.config.store (.inr aliceEvent) =
      some (.success bit : PublicationResult Bool))
    (labelLow : (originalLabel execution).val < 2)
    (rewardNonnegative : 0 ≤ reward) (forfeitPositive : 0 < forfeit)
    (bobDepositPositive : 0 < deposit bob)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeGame.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (response : app.Action)
    (supported : response ∈ (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob
        (execution.recall bob) (execution.observe app bob)).support)
    (players : Player → app.Policy)
    (bobPolicy : players bob = rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 14 (execution.respond app bob response)).support) :
    reward / 2 - GameTheory.Enforcement.TerminalAudit.charge
      (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
        (app.finished final) alice * deposit alice ≤
      LateOpeningRuntimeGame.payoff reward forfeit (fun actual => PMF.pure actual)
        deposit (app.finished final) alice := by
  by_cases quiet : LateOpeningRuntimeBobBindingService.SilentRecall execution
  · let decision : LateOpeningRuntimeBobSuccessInformation.DecisionHistory weight nonnegative :=
      ⟨execution, rawMenu.toRawTrace _ _ _ boundedTrace, quiet, bit, published, ready, timely⟩
    let history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).History :=
      ⟨some ⟨14, some bob, execution⟩, boundedTrace⟩
    have running : ¬ (rawMenu.protocol initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).terminal history.state := by
      change ¬ (14 = 0 ∧ some bob = none)
      simp
    obtain ⟨site, same⟩ := (LateOpeningRuntimeGame.model weight nonnegative)
      |>.exists_informationSite_of_active bob history running rfl
    let representative : (LateOpeningRuntimeGame.model weight nonnegative).InformationHistory
        bob site.1 := ⟨history, same.symm⟩
    have current : representative.1.state = some ⟨14, some bob, decision.execution⟩ := rfl
    have valid := LateOpeningRuntimeBobSuccessInformation.decisionOfInformation_spec weight
      nonnegative site representative decision current representative
    have recovered : (LateOpeningRuntimeBobSuccessInformation.decisionOfInformation weight
        nonnegative site representative decision current representative).execution = execution := by
      have states := congrArg (fun state : Option app.Control =>
        state.map (fun control => control.execution)) (current.symm.trans valid.1)
      simpa only [Option.map_some, Option.some.injEq] using states.symm
    apply LateOpeningRuntimeAliceFullFiberFloor.sequentially_rational_supported_payoff_floor
      weight nonnegative site representative decision current reward forfeit deposit
      rewardNonnegative
      forfeitPositive bobDepositPositive assessment rational response supported representative
      (by rwa [recovered]) players bobPolicy final
    rwa [recovered]
  · exact dirty_binding_payoff_floor weight nonnegative reward forfeit deposit assessment execution
      boundedTrace ready timely quiet bit published labelLow rewardNonnegative forfeitPositive
      rational response supported players bobPolicy final reached

end Vegas.Examples.LateOpeningRuntimeBobDirtyDisclosurePublication
