/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingFinishedOwner
import Vegas.Examples.CommitSeedSignallingOwnContinuation
import Vegas.Examples.CommitSeedSignallingOpeningDecision
import Vegas.Pending.EventHandleObservation

/-! # Accepted successful openings on unrestricted native histories -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- Packet admission is determined by the sender's actual application view.
Foreign private catalogues and foreign charged packets need not agree. -/
theorem phase_handle_isSome_of_owner_view
    (left right : PhaseRuntimeState graph) (owner : Player)
    (message : Message Player (CommitAttemptPacket graph))
    (views : left.playerView owner = right.playerView owner)
    (sender : message.sender = owner) :
    (app.handle left message).isSome = (app.handle right message).isSome := by
  have native := handle_playerView_congr_of_sender runtime left.current.native
    right.current.native owner ⟨message.id, message.payload.packet.call⟩
      (congrArg Prod.fst views) sender
  have nativeAccepted := congrArg Option.isSome native
  simp only [Option.isSome_map] at nativeAccepted
  have publicEq : left.publicView = right.publicView := congrArg Prod.snd views
  have attempts : left.attempt = right.attempt :=
    congrArg PhasePublicView.attempt publicEq
  have allowed : left.allows message.payload.packet.call =
      right.allows message.payload.packet.call := by
    rw [← PhaseCount.allows_publicView, ← PhaseCount.allows_publicView, publicEq]
  have excluded : left.current.excludedCall message.payload.packet.call =
      right.current.excludedCall message.payload.packet.call := by
    rw [← PhaseCount.excludedCall_publicView, ← PhaseCount.excludedCall_publicView, publicEq]
  change (left.handle runtime message).isSome = (right.handle runtime message).isSome
  simp only [PhaseRuntimeState.handle, attempts, allowed, excluded]
  split
  · simpa only [Option.isSome_map] using nativeAccepted
  · rfl

/-- The original successful binding value is part of its owner's full native
view. This statement does not equate the opponents' semantic stores. -/
theorem binding_store_eq_of_owner_view
    (left right : EventGraphRuntime.State graph) (owner : Player)
    (views : left.playerView owner = right.playerView owner) :
    left.config.store (.inr (bindingEvent owner)) =
      right.config.store (.inr (bindingEvent owner)) := by
  have stores := congrArg PlayerObservation.store
    (left.playerView_observation_eq right owner views)
  have visible : graph.fieldVisibleTo owner (.inr (bindingEvent owner)) := by
    change (graph.outputLayout (bindingEvent owner)).VisibleTo owner
    rw [bindingEvent_layout]
    simp only [EventField.VisibleTo]
  exact (graph.playerStore_of_visible owner left.config.store _ visible).symm.trans
    ((congrFun stores (.inr (bindingEvent owner))).trans
      (graph.playerStore_of_visible owner right.config.store _ visible))

/-- A counted representative certifies the actual current opening on every
raw history of the same full own input. The emitted envelope and native
acceptance are derived from recall and the sender-view handler theorem. -/
theorem opening_response_accepted_on_same_input
    (source : app.Control) (sourceTrace : countedProtocol.Trace (some source))
    (target : app.Control) (targetTrace : rawProtocol.Trace (some target))
    (owner : Player) (candidate : Handle graph) (value : Bool)
    (active : source.actor = some owner)
    (recalled : target.execution.recall owner = source.execution.recall owner)
    (observed : target.execution.observe app owner = source.execution.observe app owner)
    (allowed : PhaseCount.phaseOpeningResponse runtime leaks (revealEvent owner) candidate
      ⟨.bool, value⟩ ∈ countedMenu.actions owner (source.execution.recall owner)
        (source.execution.observe app owner))
    (request : source.execution.application.SeedRequest owner
      ⟨source.execution.application.attempt, revealEvent owner⟩)
    (timely : source.execution.application.current.native.WithinDeadline runtime
      (revealEvent owner))
    (stored : source.execution.application.current.native.config.store
      (.inr (bindingEvent owner)) = some
        (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
          (PublicationResult.success value))) :
    let material := disclosureSubmission (.opening (revealEvent owner) candidate ⟨.bool, value⟩)
    let responded := target.execution.respond app owner ⟨some material⟩
    let message : Message Player (CommitAttemptPacket graph) :=
      ⟨(owner, target.execution.network.nextSerial owner), app.packet responded.application owner
        (target.execution.network.known owner) material⟩
    ∃ next, app.handle responded.application message = some next := by
  classical
  let material := disclosureSubmission (.opening (revealEvent owner) candidate ⟨.bool, value⟩)
  let left := source.execution.respond app owner ⟨some material⟩
  let right := target.execution.respond app owner ⟨some material⟩
  let leftMessage : Message Player (CommitAttemptPacket graph) :=
    ⟨(owner, source.execution.network.nextSerial owner), app.packet left.application owner
      (source.execution.network.known owner) material⟩
  let rightMessage : Message Player (CommitAttemptPacket graph) :=
    ⟨(owner, target.execution.network.nextSerial owner), app.packet right.application owner
      (target.execution.network.known owner) material⟩
  have leftRecall := PhaseCount.countRecall_history runtime leaks
    (countedMenu.toRawTrace initial horizon scheduler sourceTrace)
  have rightRecall := PhaseCount.countRecall_history runtime leaks
    (rawMenu.toRawTrace initial horizon scheduler targetTrace)
  have leftLocal := PhaseCount.localEnvelope_eq_of_recall runtime leaks source.execution
    leftRecall.1 leftRecall.2.1 owner material
  have rightLocal := PhaseCount.localEnvelope_eq_of_recall runtime leaks target.execution
    rightRecall.1 rightRecall.2.1 owner material
  change PhaseCount.localEnvelope runtime leaks owner (source.execution.recall owner)
    (source.execution.observe app owner) material = leftMessage at leftLocal
  change PhaseCount.localEnvelope runtime leaks owner (target.execution.recall owner)
    (target.execution.observe app owner) material = rightMessage at rightLocal
  have messages : leftMessage = rightMessage := by
    rw [← leftLocal, ← rightLocal, recalled, observed]
  have sourceEq : source = ⟨source.remaining, some owner, source.execution⟩ := by
    cases source
    simp_all only
  have activeTrace : countedProtocol.Trace
      (some ⟨source.remaining, some owner, source.execution⟩) := sourceEq ▸ sourceTrace
  obtain ⟨respondedTrace⟩ := countedMenu.trace_respond initial horizon scheduler source.remaining
    source.execution owner ⟨some material⟩ activeTrace allowed
  have call : leftMessage.payload.packet.call =
      .opening (revealEvent owner) candidate ⟨.bool, value⟩ := by
    dsimp only [leftMessage]
    change (left.application.emit owner (source.execution.network.known owner) material).packet.call
      = _
    simp only [PhaseRuntimeState.emit, RecoveryState.emit]
    split <;> split <;> rfl
  have member : leftMessage ∈ left.network.inputs :=
    List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have requested : left.application.SeedRequest leftMessage.sender
      ⟨leftMessage.payload.attempt, revealEvent owner⟩ := request
  obtain ⟨native, next, _handled, _completed, _output, _normalized, accepted⟩ :=
    counted_successful_opening_accepted ⟨source.remaining, none, left⟩ respondedTrace owner
      leftMessage member candidate ⟨.bool, value⟩ call requested timely value stored
  have views : left.application.playerView owner = right.application.playerView owner :=
    (congrArg (fun view : app.PlayerView => view.application) observed).symm
  have same := phase_handle_isSome_of_owner_view left.application right.application owner
    leftMessage views rfl
  rw [accepted, Option.isSome_some, messages] at same
  exact Option.isSome_iff_exists.mp same.symm

/-- An accepted successful-value opening completes the owner's last event on
an unrestricted raw prefix. Every later raw continuation then preserves that
owner's survival, including continuations with charged foreign traffic. -/
theorem raw_successful_opening_future_survives
    (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control))
    (owner : Player) (message : Message Player (CommitAttemptPacket graph))
    (lookup : control.execution.network.lookup message.id = some message)
    (candidate : Handle graph) (raw : Raw simpleExpr)
    (opening : message.payload.packet.call = .opening (revealEvent owner) candidate raw)
    (request : control.execution.application.SeedRequest message.sender
      ⟨message.payload.attempt, revealEvent owner⟩)
    (value : Bool)
    (stored : control.execution.application.current.native.config.store
      (.inr (bindingEvent owner)) = some
        (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
          (PublicationResult.success value)))
    (nextState : PhaseRuntimeState graph)
    (accepted : app.handle control.execution.application message = some nextState)
    (nextExecution : app.Execution)
    (includedStep : nextExecution ∈
      (control.execution.environmentStep app (.include message.id)).support)
    (selected : app.Scheduler) (players : Player → app.Policy) (count : Nat)
    (after : app.Execution)
    (supported : after ∈ (app.runRounds selected players count nextExecution).support) :
    owner ∉ after.application.current.excluded := by
  classical
  have acceptedActual := accepted
  change control.execution.application.handle runtime message = some nextState at accepted
  unfold PhaseRuntimeState.handle at accepted
  split at accepted
  · obtain ⟨native, handled, normalized⟩ := Option.map_eq_some_iff.mp accepted
    have ready : control.execution.application.current.native.config.cut.Ready
        (revealEvent owner) := request.2.2.1
    have predecessors : graph.order.predecessors (revealEvent owner) =
        {aliceBinding, bobBinding} := by
      unfold revealEvent
      split
      · exact reveal_predecessors.1
      · exact reveal_predecessors.2
    have aliceDone : aliceBinding ∈
        control.execution.application.current.native.config.cut.completed :=
      ready.2 (by rw [predecessors]; exact Finset.mem_insert_self _ _)
    have bobDone : bobBinding ∈
        control.execution.application.current.native.config.cut.completed :=
      ready.2 (by rw [predecessors]
                  exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have tail := completed_bindings_publication_tail scheduler control trace aliceDone bobDone
    change handle runtime control.execution.application.current.native
      ⟨message.id, message.payload.packet.call⟩ = some native at handled
    have nativeOpening : handle runtime control.execution.application.current.native
        ⟨message.id, .opening (revealEvent owner) candidate raw⟩ = some native := by
      rwa [opening] at handled
    have output := handle_successful_binding_opening
      control.execution.application.current.native native message.id owner candidate raw value
        stored nativeOpening
    obtain ⟨event, addressed, _unfinished, completed⟩ :=
      handle_completes runtime _ native _ handled
    have same : event = revealEvent owner := Option.some.inj (addressed.symm.trans (by
      simp only [opening, Payload.event?]))
    rw [same] at completed
    have nativeKeeps : KeepsStore native nextState.current.native := by
      rw [← normalized]
      exact settle_publication_keepsStore control.execution.application.phases
        control.execution.application.generation control.execution.application.entry
        (control.execution.application.current.inclusionResult message.payload.packet.call native)
        control.execution.application.retired tail
    have nextTail : nextState.phases <:+ [publicationPhase] := by
      rw [← normalized]
      exact (PhaseRuntimeState.settle_suffix _ _ _ _ _).trans tail
    have finished : ∀ event, graph.actor? event = some owner →
        event ∈ nextState.current.native.config.cut.completed := by
      intro event acting
      exact completed_of_keepsStore native nextState.current.native nativeKeeps event
        (own_events_completed_of_reveal native.config owner completed event acting)
    have actor : graph.actor? (revealEvent owner) = some owner := by
      fin_cases owner <;> rfl
    have sender : message.sender = owner :=
      Option.some.inj (request.2.2.2.1.symm.trans actor)
    have beforeActive : owner ∉ control.execution.application.current.excluded := by
      simpa only [sender] using request.2.2.2.2
    have noFailure := successful_opening_not_failed native owner value output
    have active : owner ∉ nextState.current.excluded := by
      rw [← normalized]
      change owner ∉ (PhaseRuntimeState.settle _ _ _ _ _).current.excluded
      rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).1]
      simp only [opening, RecoveryState.inclusionResult, noFailure, Bool.false_eq_true,
        ↓reduceIte]
      exact beforeActive
    have included : (control.execution.includePending app message.id).application = nextState := by
      simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        lookup, acceptedActual, Option.getD_some]
    have actualApplication : nextExecution.application = nextState := by
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at includedStep
      cases (PMF.mem_support_pure_iff _ _).mp includedStep
      exact included
    apply finished_owner_run_survives selected players count nextExecution after owner
    · rwa [actualApplication]
    · rwa [actualApplication]
    · rwa [actualApplication]
    · exact supported
  · cases accepted

/-- Native successful acceptance gives a nonnegative actual assessed payoff
from an arbitrary clean-own raw prefix. Future foreign packets are unrestricted;
future focal charge-freedom follows from sequential rationality. -/
theorem raw_accepted_opening_assessed_value_nonnegative
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (remaining : Nat) (execution : app.Execution)
    (trace : rawProtocol.Trace (some ⟨remaining + 1, none, execution⟩))
    (owner : Player) (clean : OwnPermitted owner execution)
    (message : Message Player (CommitAttemptPacket graph))
    (lookup : execution.network.lookup message.id = some message)
    (candidate : Handle graph) (raw : Raw simpleExpr)
    (opening : message.payload.packet.call = .opening (revealEvent owner) candidate raw)
    (request : execution.application.SeedRequest message.sender
      ⟨message.payload.attempt, revealEvent owner⟩)
    (value : Bool)
    (stored : execution.application.current.native.config.store
      (.inr (bindingEvent owner)) = some
        (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
          (PublicationResult.success value)))
    (nextState : PhaseRuntimeState graph)
    (accepted : app.handle execution.application message = some nextState)
    (selected : (.include message.id : app.Command) ∈
      (scheduler execution.environmentRecall (execution.observeEnvironment app)).support)
    (next : app.Execution)
    (included : next ∈ (execution.environmentStep app (.include message.id)).support) :
    0 ≤ expect (app.finish initial horizon scheduler
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
      (some ⟨remaining, none, next⟩)) (fun state => netPayoff state owner) := by
  classical
  obtain ⟨nextTrace⟩ := rawMenu.trace_environment initial horizon scheduler remaining execution
    next (.include message.id) trace selected included
  let history : rawProtocol.History := ⟨some ⟨remaining, none, next⟩, nextTrace⟩
  let players := rawMenu.decodeProfile initial horizon scheduler assessment.strategy
  have cleanNext : OwnPermitted owner next :=
    ownPermitted_environment owner execution next (.include message.id) clean included
  have law := raw_terminal_state_law assessment.strategy history
  change (rawModel.runBehavioralTerminalFrom canonicalCertificate assessment.strategy history).map
    History.state = app.finish initial horizon scheduler players
      (some ⟨remaining, none, next⟩) at law
  rw [← law, expect_map]
  apply expect_nonneg
  intro final supported
  have zero := raw_equilibrium_own_clean_terminal_charge_zero assessment equilibrium owner
    history final cleanNext supported
  have physical : final.state ∈ ((rawModel.runBehavioralTerminalFrom canonicalCertificate
      assessment.strategy history).map History.state).support := by
    rw [PMF.support_map]
    exact ⟨final, supported, rfl⟩
  rw [law] at physical
  change final.state ∈ (((PMF.pure next).bind
    (app.runRounds scheduler players remaining)).map app.finished).support at physical
  rw [PMF.pure_bind] at physical
  obtain ⟨after, rounds, stateEq⟩ := PMF.support_map .. ▸ physical
  have survives := raw_successful_opening_future_survives
    ⟨remaining + 1, none, execution⟩
      (rawMenu.toRawTrace initial horizon scheduler trace) owner message lookup candidate raw
      opening request value stored nextState accepted next included scheduler players remaining
      after rounds
  change 0 ≤ basePayoff final.state owner -
    TerminalAudit.charge app.stateTraffic audit final.state owner * deposit owner
  rw [zero, zero_mul, sub_zero, ← stateEq]
  change 0 ≤ phaseExclusionBase setup .concurrentReveals runtime leaks utility excludedPayoff
    (some ⟨0, none, after⟩) owner
  rw [phaseExclusionBase_eq_readout setup .concurrentReveals runtime leaks utility excludedPayoff
    ⟨0, none, after⟩ owner survives]
  cases phaseSourceReadout setup .concurrentReveals runtime leaks (some ⟨0, none, after⟩) with
  | none => exact le_refl _
  | some source => exact (utility_mem_Icc source owner).1

/-- A truthful opening has nonnegative value throughout the raw own-input
fiber of a counted representative. Its current acceptance, protected next
inclusion, future survival and zero focal charge are all derived. -/
theorem raw_tail_opening_value_on_same_input
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : app.Control) (sourceTrace : countedProtocol.Trace (some source))
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (targetTrace : rawProtocol.Trace (some ⟨remaining + 1, some owner, execution⟩))
    (clean : OwnPermitted owner execution)
    (active : source.actor = some owner)
    (recalled : execution.recall owner = source.execution.recall owner)
    (observed : execution.observe app owner = source.execution.observe app owner)
    (retired : source.execution.application.attempt ≠ originalAttempt)
    (candidate : Handle graph) (value : Bool)
    (allowed : PhaseCount.phaseOpeningResponse runtime leaks (revealEvent owner) candidate
      ⟨.bool, value⟩ ∈ countedMenu.actions owner (source.execution.recall owner)
        (source.execution.observe app owner))
    (request : source.execution.application.SeedRequest owner
      ⟨source.execution.application.attempt, revealEvent owner⟩)
    (timely : source.execution.application.current.native.WithinDeadline runtime
      (revealEvent owner))
    (stored : source.execution.application.current.native.config.store
      (.inr (bindingEvent owner)) = some
        (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
          (PublicationResult.success value))) :
    0 ≤ expect (app.finish initial horizon scheduler
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
      (some ⟨remaining + 1, none, execution.respond app owner
        (PhaseCount.phaseOpeningResponse runtime leaks (revealEvent owner) candidate
          ⟨.bool, value⟩)⟩)) (fun state => netPayoff state owner) := by
  classical
  let material := disclosureSubmission (.opening (revealEvent owner) candidate ⟨.bool, value⟩)
  let responded := execution.respond app owner ⟨some material⟩
  let message : Message Player (CommitAttemptPacket graph) :=
    ⟨(owner, execution.network.nextSerial owner), app.packet responded.application owner
      (execution.network.known owner) material⟩
  have allowedHere : PhaseCount.phaseOpeningResponse runtime leaks (revealEvent owner) candidate
      ⟨.bool, value⟩ ∈ countedMenu.actions owner (execution.recall owner)
        (execution.observe app owner) := by rw [recalled, observed]; exact allowed
  have allowedRaw : (⟨some material⟩ : app.Action) ∈ rawMenu.actions owner
      (execution.recall owner) (execution.observe app owner) :=
    ((PhaseCount.mem_onePacketActions runtime leaks bounds owner _ _ _).mp allowedHere).1
  obtain ⟨respondedTrace⟩ := rawMenu.trace_respond initial horizon scheduler (remaining + 1)
    execution owner ⟨some material⟩ targetTrace allowedRaw
  have cleanAfter : OwnPermitted owner responded :=
    ownPermitted_counted_respond owner execution ⟨some material⟩ clean allowedHere
  obtain ⟨nextState, accepted⟩ := opening_response_accepted_on_same_input source sourceTrace
    ⟨remaining + 1, some owner, execution⟩ targetTrace owner candidate value active recalled
      observed allowed request timely stored
  have nativeViews : execution.application.current.native.playerView owner =
      source.execution.application.current.native.playerView owner :=
    congrArg (fun view : app.PlayerView => view.application.1) observed
  have storedHere := (binding_store_eq_of_owner_view execution.application.current.native
    source.execution.application.current.native owner nativeViews).trans stored
  have attempt : execution.application.attempt = source.execution.application.attempt :=
    congrArg (fun view : app.PlayerView => view.application.2.attempt) observed
  have valid := raw_native_valid scheduler ⟨remaining + 1, some owner, execution⟩
    (rawMenu.toRawTrace initial horizon scheduler targetTrace)
  have sourceValid := raw_native_valid scheduler source
    (countedMenu.toRawTrace initial horizon scheduler sourceTrace)
  have publicRequest := (source.execution.application.requests_publicView sourceValid owner
    ⟨source.execution.application.attempt, revealEvent owner⟩).mpr request
  have publicHere : PhaseRuntimeState.requests execution.application.publicView owner
      ⟨execution.application.attempt, revealEvent owner⟩ := by
    change PhaseRuntimeState.requests (execution.observe app owner).application.2 owner _
    rw [attempt, observed]
    exact publicRequest
  have requested : responded.application.SeedRequest message.sender
      ⟨message.payload.attempt, revealEvent owner⟩ :=
    (execution.application.requests_publicView valid owner
      ⟨execution.application.attempt, revealEvent owner⟩).mp publicHere
  have call : message.payload.packet.call =
      .opening (revealEvent owner) candidate ⟨.bool, value⟩ := by
    dsimp only [message]
    change (responded.application.emit owner (execution.network.known owner) material).packet.call
      = _
    simp only [PhaseRuntimeState.emit, RecoveryState.emit]
    split <;> split <;> rfl
  have serials := app.serialsBeforeNext_history scheduler initial horizon
    (rawMenu.toRawTrace initial horizon scheduler targetTrace)
  have lookup : responded.network.lookup message.id = some message :=
    serials.lookup_submit owner
      (app.packet responded.application owner (execution.network.known owner) material)
  have scheduled : scheduler responded.environmentRecall (responded.observeEnvironment app) =
      PMF.pure (.include message.id) :=
    tail_submission_scheduler (remaining + 1) execution owner material
      (rawMenu.toRawTrace initial horizon scheduler targetTrace) (by rwa [attempt])
  let next : app.Execution :=
    { responded.includePending app message.id with
      environmentRecall := responded.environmentRecall ++
        [⟨responded.observeEnvironment app, .include message.id⟩] }
  have step : responded.environmentStep app (.include message.id) = PMF.pure next := by
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map, next]
  have moved : next ∈ (responded.environmentStep app (.include message.id)).support := by
    rw [step]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have selected : (.include message.id : app.Command) ∈
      (scheduler responded.environmentRecall (responded.observeEnvironment app)).support := by
    rw [scheduled]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have bound := raw_accepted_opening_assessed_value_nonnegative assessment equilibrium remaining
    responded respondedTrace owner cleanAfter message lookup candidate ⟨.bool, value⟩ call
      requested value storedHere nextState accepted selected next moved
  change 0 ≤ expect (app.finish initial horizon scheduler
    (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
    (some ⟨remaining + 1, none, responded⟩)) (fun state => netPayoff state owner)
  simp only [ReactiveApplication.finish, ReactiveApplication.resume, PMF.pure_bind]
  rw [ReactiveApplication.runRounds, ReactiveApplication.round, scheduled, PMF.pure_bind,
    ReactiveApplication.dispatch, step, PMF.pure_bind]
  simpa only [ReactiveApplication.Command.actor?, ReactiveApplication.resume, PMF.pure_bind,
    ReactiveApplication.finish] using bound

end Vegas.Examples.CommitSeedSignalling
