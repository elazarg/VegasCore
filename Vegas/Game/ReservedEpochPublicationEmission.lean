/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochPublicationOldWord
import Vegas.Pending.PhaseRecordedCountedRequest
import Interaction.ReactiveRoundTracePrefix

/-! # Actual proposal suppression after the first old expiry -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The old emission bit stops at the first actual due command, including
the distinction between its command position and any earlier due-cycle SEND. -/
theorem openingFrontierEmission_false_of_due {length : Nat} (tape : Tape Player length)
    (anchor : (app).Execution) (owner : Player) (event : graph.EventId) (entered cursor : Nat)
    (stamp : anchor.application.current.native.activatedAt event = some entered)
    (unsent : ∀ message ∈ (app).outputs (anchor.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨anchor.application.attempt, event⟩)
    (lower : anchor.environmentRecall.length ≤ cursor)
    (expired : ∀ view, command runtime leaks (packetCapacity runtime) tape cursor view =
      .application (.expire event))
    (due : runtime.deadline event ≤ cursor / cycleWidth (graph := graph) (packetCapacity runtime) -
      entered)
    (quiet : ∀ earlier, anchor.environmentRecall.length ≤ earlier → earlier < cursor → ∀ view,
      (command runtime leaks (packetCapacity runtime) tape earlier view).actor? app ≠ some owner) :
    ¬ openingFrontierEmission runtime leaks tape anchor owner event := by
  rintro (⟨message, member, candidate, value, address, call⟩ |
    ⟨otherEntered, otherStamp, offered, offeredLower, _bounded, active, _first, expiryOpen⟩)
  · exact unsent message member (by simp only [PhaseCount.event?, call, Payload.event?, address,
      Option.map_some])
  · have sameEntered : otherEntered = entered := Option.some.inj (otherStamp.symm.trans stamp)
    subst otherEntered
    rcases Nat.lt_trichotomy offered cursor with earlier | equal | later
    · exact quiet offered offeredLower earlier (anchor.observeEnvironment app)
        (active (anchor.observeEnvironment app))
    · subst offered
      have impossible := active (anchor.observeEnvironment app)
      rw [expired] at impossible
      cases impossible
    · have timely := expiryOpen cursor lower later (anchor.observeEnvironment app)
        (expired (anchor.observeEnvironment app))
      omega

/-- Every counted packet at an already resolved idle coordinate was submitted
before that anchor. Earlier callback origins lie in its literal recall; later
origins contradict permanent resolution. -/
theorem resolved_counted_packet_origin (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (before final : (app).Control)
    (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some before))
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some final))
    (kept : TracePrefix prior trace) (idle : before.actor = none)
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (resolved : coordinate.Resolved before.execution.application) :
    ∀ message ∈ final.execution.network.inputs, message.sender = owner →
      PhaseCount.event? message.payload = some coordinate →
        message ∈ before.execution.network.inputs := by
  classical
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let raw := menu.toRawTrace initial horizon scheduler trace
  intro message input sender named
  have origins := (app).history_provenance initial horizon scheduler raw
  obtain ⟨entry, member, material, sent, emitted, _state, _known, _packet⟩ :=
    origins.inputs message input
  rw [sender] at member
  obtain ⟨callback, callbackTrace, callbackKept, acting, viewed, offered, later, recalled⟩ :=
    menu.recorded_response_prefix initial horizon scheduler final trace owner entry member
  have offeredMaterial : (⟨some material⟩ : (app).Action) ∈
      PhaseCount.onePacketActions runtime leaks bounds owner (callback.execution.recall owner)
        (callback.execution.observe app owner) := by
    have actionEq : entry.action = ⟨some material⟩ := by
      cases chosen : entry.action with
      | mk transmission =>
          rw [chosen] at sent
          exact congrArg ReactiveApplication.Action.mk sent
    rwa [actionEq] at offered
  by_cases earlier : callbackTrace.length ≤ prior.length
  · have callbackBefore : TracePrefix callbackTrace prior :=
      (ReachesWithin.ancestor_comparable (E := menu.protocol initial horizon scheduler)
        (first := ⟨some callback, callbackTrace⟩) (second := ⟨some before, prior⟩)
        (target := ⟨some final, trace⟩) callbackKept.reachesWithin kept.reachesWithin
          earlier).tracePrefix
    have strict := phase_active_idle_recall_lt runtime leaks menu initial horizon scheduler
      callback before callbackTrace prior callbackBefore owner acting idle
    have recallPrefix := (app).reaches_recall_prefix initial horizon scheduler
      (menu.reaches_raw initial horizon scheduler kept.reachesWithin) before final rfl rfl owner
    have selected : (final.execution.recall owner)[(callback.execution.recall owner).length]? =
        some entry := by rw [recalled]; simp
    obtain ⟨suffix, appended⟩ := recallPrefix
    rw [← appended, List.getElem?_append_left strict] at selected
    have output : message ∈ (app).outputs (before.execution.recall owner) :=
      List.mem_filterMap.mpr ⟨entry, List.mem_of_getElem? selected, emitted⟩
    rw [← (app).history_inputRecall initial horizon scheduler
      (menu.toRawTrace initial horizon scheduler prior) owner] at output
    exact (List.mem_filter.mp output).1
  · have beforeCallback : TracePrefix prior callbackTrace :=
      (ReachesWithin.ancestor_comparable (E := menu.protocol initial horizon scheduler)
        (first := ⟨some before, prior⟩) (second := ⟨some callback, callbackTrace⟩)
        (target := ⟨some final, trace⟩) kept.reachesWithin callbackKept.reachesWithin
          (by change prior.length ≤ callbackTrace.length; omega)).tracePrefix
    obtain ⟨actual, requested, actualAttempt, materialEvent⟩ :=
      PhaseCount.recorded_material_request runtime leaks bounds plan ordered inputs horizon
        scheduler final trace owner entry member material sent
    obtain ⟨other, otherEmitted, _authored, call⟩ := PhaseCount.recalled_submission_emitted runtime
      leaks initial horizon scheduler raw owner entry member material sent
    have sameMessage : other = message := Option.some.inj (otherEmitted.symm.trans emitted)
    subst other
    have emissionAttempt := phase_recalled_emission_attempt runtime leaks initial horizon scheduler
      raw owner entry member message emitted
    have actualEq : actual = coordinate := by
      have physical : (⟨message.payload.attempt, actual.event⟩ : CommitAttemptEvent graph) =
          coordinate := by
        simpa only [PhaseCount.event?, call, materialEvent, Option.map_some, Option.some.injEq]
          using named
      have address := actualAttempt.trans emissionAttempt.symm
      have identity : actual = ⟨message.payload.attempt, actual.event⟩ := by
        cases actual with
        | mk attempt event => exact congrArg (fun address =>
            (⟨address, event⟩ : CommitAttemptEvent graph)) address
      exact identity.trans physical
    obtain ⟨_draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
      scheduler
      (menu.toRawTrace initial horizon scheduler callbackTrace)
    have request : callback.execution.application.SeedRequest owner coordinate := by
      have actualRequest := requested
      rw [viewed] at actualRequest
      exact actualEq ▸ (callback.execution.application.requests_publicView valid owner actual).mp
        actualRequest
    exact ((phase_resolved_prefix runtime leaks menu plan inputs horizon scheduler before
      callback prior callbackTrace beforeCallback coordinate resolved).not_request _ _ owner
        request).elim

/-- The first old due branch retains actual expiry and continuation support.
Counted callback origins, rather than the FALSE receipt alone, rule out any
later opening proposal at that original address. -/
theorem old_due_counted_packet_absent {length : Nat} (cycles : Nat)
    (tape : Tape Player length) (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs)
    (players : Player → (app).Policy)
    (covered : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ (PhaseCount.onePacketMenu runtime leaks bounds).actions who past view)
    (remaining closedRemaining used tail : Nat) (before due expired closed : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) (horizon (graph := graph) cycles)
      (family runtime leaks (submissionBudget (Player := Player) cycles) tape)).Trace
        (some ⟨remaining, none, before⟩))
    (lengths : used + 1 + tail + closedRemaining = remaining)
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (unsent : ∀ message ∈ (app).outputs (before.recall owner),
      PhaseCount.event? message.payload ≠ some coordinate)
    (quiet : ∀ cursor, before.environmentRecall.length ≤ cursor →
      cursor < before.environmentRecall.length + used → ∀ view,
      (command runtime leaks (submissionBudget (Player := Player) cycles) tape cursor view).actor?
        app ≠ some owner)
    (reached : due ∈ ((app).runRounds (family runtime leaks
      (submissionBudget (Player := Player) cycles) tape) players used before).support)
    (selected : command runtime leaks (submissionBudget (Player := Player) cycles) tape
      due.environmentRecall.length (due.observeEnvironment app) = .application (.expire
        coordinate.event))
    (expiry : expired ∈ (due.environmentStep app (.application (.expire coordinate.event))).support)
    (resolved : coordinate.Resolved expired.application)
    (future : closed ∈ ((app).runRounds (family runtime leaks
      (submissionBudget (Player := Player) cycles) tape) players tail expired).support) :
    ∀ message ∈ closed.network.inputs, message.sender = owner →
      PhaseCount.event? message.payload ≠ some coordinate := by
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let bound := horizon (graph := graph) cycles
  let budget := submissionBudget (Player := Player) cycles
  let scheduler := family runtime leaks budget tape
  obtain ⟨dueTrace, _dueKept⟩ := menu.trace_runRounds_prefix initial bound scheduler players covered
    (remaining - used) used before due (by
      simpa only [Nat.sub_add_cancel (by omega : used ≤ remaining)] using trace) reached
  have moved : expired ∈ ((app).runRounds scheduler players 1 due).support := by
    simp only [ReactiveApplication.runRounds, PMF.bind_pure]
    change expired ∈ (((scheduler due.environmentRecall (due.observeEnvironment app)).bind
      fun command => (due.environmentStep app command).bind
        ((app).resume players (command.actor? app)))).support
    rw [PMF.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨.application (.expire coordinate.event),
      (family_support runtime leaks budget tape _ _ _).mpr selected.symm, ?_⟩
    rw [PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨expired, expiry, (PMF.mem_support_pure_iff _ _).mpr rfl⟩
  obtain ⟨expiryTrace, _expiryKept⟩ := menu.trace_runRounds_prefix initial bound scheduler players
    covered (remaining - used - 1) 1 due expired (by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ remaining - used)] using dueTrace) moved
  have expiryStart : (menu.protocol initial bound scheduler).Trace
      (some ⟨closedRemaining + tail, none, expired⟩) := by
    have rest : remaining - used - 1 = closedRemaining + tail := by omega
    simpa only [rest] using expiryTrace
  obtain ⟨finalTrace, kept⟩ := menu.trace_runRounds_prefix initial bound scheduler players covered
    closedRemaining tail expired closed expiryStart future
  have recalled := recall_before_next_offer runtime leaks budget tape players used before due owner
    quiet reached
  have expiredRecall := congrFun ((app).environmentStep_recall due expired
    (.application (.expire coordinate.event)) expiry) owner
  have stillUnsent : ∀ message ∈ (app).outputs (expired.recall owner),
      PhaseCount.event? message.payload ≠ some coordinate := by
    rw [expiredRecall, recalled]
    exact unsent
  intro message input sender named
  have old := resolved_counted_packet_origin runtime leaks bounds plan ordered inputs bound
    scheduler ⟨closedRemaining + tail, none, expired⟩ ⟨closedRemaining, none, closed⟩
      expiryStart finalTrace kept
      rfl owner coordinate resolved message input sender named
  have output : message ∈ (app).outputs (expired.recall owner) := by
    rw [← (app).history_inputRecall initial bound scheduler
      ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial bound scheduler
        expiryStart)
      owner]
    exact List.mem_filter.mpr ⟨old, by simp only [sender, decide_true]⟩
  exact stillUnsent message output named

end Vegas.EventGraphRuntime.ReservedEpoch
