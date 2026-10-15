/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedSurvivalReply
import Vegas.Pending.PhaseSeedTickExhaustion
import Interaction.ReactiveRecordedRounds
import Interaction.ReactiveAddressedTranscriptAppend

/-! # Earlier tick closures of a surviving coordinate were actual wait queries -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
private theorem retained_bound_runRounds (scheduler : (app).Scheduler)
    (players : Player → (app).Policy) (count : Nat) (execution next : (app).Execution)
    {inputs : graph.Inputs} (valid : execution.application.Invariant inputs)
    (ordered : execution.application.Ordered) (tick entered : Nat)
    (coordinate : CommitAttemptEvent graph)
    (closed : ClosedCoordinateBound runtime tick entered coordinate execution.application)
    (reached : next ∈ ((app).runRounds scheduler players count execution).support) :
    ClosedCoordinateBound runtime tick entered coordinate next.application := by
  let invariant : (app).ServiceInvariant scheduler (fun current =>
      current.application.Invariant inputs ∧ current.application.Ordered ∧
        ClosedCoordinateBound runtime tick entered coordinate current.application) := {
    respond := fun before who action safe =>
      ⟨(phaseApplication_invariant runtime leaks inputs).respond before who action safe.1,
        (phaseApplication_seedOrder runtime leaks).respond before who action safe.2.1,
        ClosedCoordinateBound.respond runtime leaks before who action safe.1 safe.2.1 safe.2.2⟩
    environment := fun before after command safe _ moved =>
      ⟨(phaseApplication_invariant runtime leaks inputs).environmentStep before after command
          safe.1 moved,
        (phaseApplication_seedOrder runtime leaks).environmentStep before after command safe.2.1
          moved,
        ClosedCoordinateBound.environmentStep runtime leaks before after command safe.1 safe.2.1
          moved safe.2.2⟩ }
  exact (invariant.runRounds players count execution next ⟨valid, ordered, closed⟩ reached).2.2

/-- A nonactivation command recorded at any earlier selected query of a still
requested physical coordinate was wait, not a rejected or completed resolution. -/
theorem recorded_wait_of_request (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon remaining : Nat) (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon
      ((controller runtime leaks delay bound priority).family seeds)).Trace
        (some ⟨remaining, none, execution⟩))
    (coordinate : PhaseSeedAddress graph) (owner : Player)
    (request : execution.application.SeedRequest owner coordinate.1)
    (before : List (app).EnvironmentEntry) (entry : (app).EnvironmentEntry)
    (after : List (app).EnvironmentEntry)
    (recorded : execution.environmentRecall = before ++ entry :: after)
    (selected : selectOpen runtime leaks (replayClosed runtime leaks priority seeds.1 before)
      entry.beforeView (priority seeds.1 before entry.beforeView) = some coordinate)
    (idle : (entry.command.actor? app).isNone = true) :
    entry.command = .wait ∧ entry.beforeView.application.native.activatedAt coordinate.1.event =
      execution.application.current.native.activatedAt coordinate.1.event := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let scheduler := (controller runtime leaks delay bound priority).family seeds
  have supported := menu.roundSupported_uniform initial horizon scheduler trace
  have rounds : execution ∈ ((app).roundsFrom initial scheduler menu.uniformResponses
      execution.environmentRecall.length).support := supported.2
  obtain ⟨state, stateSupported, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ rounds)
  have recalled : execution.environmentRecall =
      (ReactiveApplication.Execution.initial app state).environmentRecall ++
        before ++ entry :: after := by
    simpa only [ReactiveApplication.Execution.initial, List.nil_append] using recorded
  obtain ⟨used, suffix, prior, middle, length, prefixReached, priorRecall, viewEq, commandSupported,
    dispatched, future⟩ := (app).runRounds_recorded_entry scheduler menu.uniformResponses
      execution.environmentRecall.length (ReactiveApplication.Execution.initial app state)
      execution reached before entry after recalled
  have prefixSupported : prior ∈ ((app).roundsFrom initial scheduler menu.uniformResponses
      used).support := by
    rw [ReactiveApplication.roundsFrom, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨state, stateSupported, prefixReached⟩
  have within : used ≤ horizon := by
    have total : execution.environmentRecall.length + remaining = horizon := supported.1
    omega
  obtain ⟨priorTrace⟩ := menu.trace_roundsFrom initial horizon scheduler menu.uniformResponses
    (fun who past view action admitted =>
      (menu.uniformResponses_support who past view action).mp admitted)
    used within prior prefixSupported
  have priorRecallEq : prior.environmentRecall = before := by
    simpa only [ReactiveApplication.Execution.initial, List.nil_append] using priorRecall
  have actualSelected : selectedAt runtime leaks priority seeds.1 prior = some coordinate := by
    unfold selectedAt
    rw [priorRecallEq, ← viewEq]
    exact selected
  have noActor : entry.command.actor? app = none := Option.isNone_iff_eq_none.mp idle
  have moved : middle ∈ (prior.environmentStep app entry.command).support := by
    rw [ReactiveApplication.dispatch, noActor] at dispatched
    change middle ∈ ((prior.environmentStep app entry.command).bind
      fun next => PMF.pure next).support
      at dispatched
    simpa only [PMF.bind_pure] using dispatched
  have waited := nonactivation_wait_of_future_request runtime leaks delay bound priority seeds
    bounds plan ordered maximal inputs horizon (horizon - used) prior middle priorTrace coordinate
    actualSelected entry.command commandSupported moved scheduler menu.uniformResponses suffix
    execution future owner request idle
  have rawPrior := menu.toRawTrace initial horizon scheduler priorTrace
  obtain ⟨input, valid, namespaces, _⟩ :=
    currentTokenPrerequisites_history runtime leaks plan inputs horizon scheduler rawPrior
  obtain ⟨principal, selectedRequest⟩ := selected_request runtime leaks priority seeds.1 prior
    valid coordinate actualSelected
  have principalEq : principal = owner := Option.some.inj
    (selectedRequest.2.2.2.1.symm.trans request.2.2.2.1)
  subst principal
  have chosenEq : entry.command = (controller runtime leaks delay bound priority).choose seeds
      prior.environmentRecall (prior.observeEnvironment app) :=
    (PMF.mem_support_pure_iff _ _).mp commandSupported
  have selectedReply := choose_eq_reply runtime leaks delay bound priority seeds prior coordinate
    actualSelected owner request.2.2.2.1
  have waitReply : reply runtime leaks delay bound coordinate (seeds.2 coordinate)
      (queryAt runtime leaks prior coordinate owner) = .wait :=
    selectedReply.symm.trans (chosenEq.symm.trans waited)
  have timely : (queryAt runtime leaks prior coordinate owner).elapsed <
      runtime.deadline coordinate.1.event := by
    by_contra late
    have due := decision_deadline runtime delay bound coordinate (seeds.2 coordinate)
      (queryAt runtime leaks prior coordinate owner) (Nat.le_of_not_gt late)
    simp only [reply, due, reduceCtorEq] at waitReply
  obtain ⟨oldEntered, oldStamp⟩ := valid.active.activatedAt_eq_some_of_ready_actor
    coordinate.1.event selectedRequest.2.2.1 (by
      simp only [request.2.2.2.1, Option.isSome_some])
  have beforeBound : ClosedCoordinateBound runtime prior.application.current.native.clock
      oldEntered coordinate.1 prior.application := by
    refine ⟨le_rfl, valid.active.activated_le coordinate.1.event oldEntered oldStamp,
      ?_, ?_, fun _ => Or.inr ⟨selectedRequest.2.2.1, oldStamp, ?_⟩⟩
    · rw [selectedRequest.1]
    · rw [selectedRequest.1]
    · change prior.application.current.native.clock -
        (prior.application.current.native.activatedAt coordinate.1.event).getD
          prior.application.current.native.clock < runtime.deadline coordinate.1.event at timely
      have exactStamp : prior.application.current.native.activatedAt coordinate.1.event =
          some oldEntered := oldStamp
      rw [exactStamp, Option.getD_some] at timely
      exact timely
  have middleValid := (phaseApplication_invariant runtime leaks input).environmentStep
    prior middle entry.command valid moved
  have middleOrdered := (phaseApplication_seedOrder runtime leaks).environmentStep prior middle
    entry.command namespaces.ordered moved
  have middleBound := ClosedCoordinateBound.environmentStep runtime leaks prior middle entry.command
    valid namespaces.ordered moved beforeBound
  have finalBound := retained_bound_runRounds runtime leaks scheduler menu.uniformResponses suffix
    middle execution middleValid middleOrdered prior.application.current.native.clock oldEntered
    coordinate.1 middleBound future
  rcases finalBound.event request.1 with completed | ⟨_, finalStamp, _⟩
  · exact (request.2.2.1.1 completed).elim
  · refine ⟨waited, ?_⟩
    rw [viewEq]
    change prior.application.current.native.activatedAt coordinate.1.event =
      execution.application.current.native.activatedAt coordinate.1.event
    exact oldStamp.trans finalStamp.symm

/-- Each exhausted earlier absolute clock supplies a concrete actual wait
query for the same surviving address, with its complete actual earlier history. -/
theorem past_wait_query_of_tickExhaustion (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon remaining : Nat) (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon
      ((controller runtime leaks delay bound priority).family seeds)).Trace
        (some ⟨remaining, none, execution⟩))
    (coordinate : PhaseSeedAddress graph) (owner : Player)
    (request : execution.application.SeedRequest owner coordinate.1)
    (entered : Nat)
    (stamp : execution.application.current.native.activatedAt coordinate.1.event = some entered)
    (tick : Nat) (started : entered ≤ tick)
    (earlier : tick < execution.application.current.native.clock) :
    ∃ query, (query, .wait) ∈
      (controller runtime leaks delay bound priority).coordinateTranscriptFrom
        seeds.1 coordinate [] execution.environmentRecall ∧ query.elapsed = tick - entered := by
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    (inputs.map (PhaseRuntimeState.initial plan)) horizon
    ((controller runtime leaks delay bound priority).family seeds) trace
  have exhausted := history_tickExhaustion runtime leaks delay bound priority seeds plan ordered
    maximal inputs horizon raw ⟨remaining, none, execution⟩ rfl coordinate owner request entered
    stamp tick started earlier
  obtain prior | ⟨before, entry, after, recalled, clockEq, selected, idle⟩ :=
    replayClosedFrom_origin runtime leaks priority seeds.1 ∅ [] execution.environmentRecall
      tick coordinate exhausted
  · exact (Finset.notMem_empty _ prior).elim
  · have actualSelected : selectOpen runtime leaks
        (replayClosed runtime leaks priority seeds.1 before) entry.beforeView
        (priority seeds.1 before entry.beforeView) = some coordinate := by
      simpa only [replayClosed, List.nil_append] using selected
    obtain ⟨waited, sameStamp⟩ := recorded_wait_of_request runtime leaks delay bound priority seeds
      bounds plan ordered maximal inputs horizon remaining execution trace coordinate owner request
      before entry after recalled actualSelected idle
    let query := PhaseSeedInput.operational coordinate.1.attempt
      (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner before entry.beforeView)
    have requested : (controller runtime leaks delay bound priority).request seeds.1 before
        entry.beforeView = some (coordinate, query) := by
      simp only [controller, actualSelected, Option.bind_some, request.2.2.2.1, Option.map_some,
        query]
    refine ⟨query, ?_, ?_⟩
    · rw [recalled, ReactiveApplication.AddressedScheduler.coordinateTranscriptFrom_append]
      apply List.mem_append_right
      simp only [List.nil_append, ReactiveApplication.AddressedScheduler.coordinateTranscriptFrom,
        requested, ite_true]
      rw [waited]
      exact List.mem_cons_self
    · change entry.beforeView.application.native.clock -
        (entry.beforeView.application.native.activatedAt coordinate.1.event).getD
          entry.beforeView.application.native.clock = tick - entered
      rw [sameStamp, stamp, Option.getD_some, ← clockEq]

end Vegas.EventGraphRuntime.PhaseSeedCalendar
