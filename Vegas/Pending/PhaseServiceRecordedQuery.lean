/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceUnsentInput
import Vegas.Pending.PhaseServiceRounds
import Interaction.ReactiveRecordedRounds

/-! # Exact activation memory at every original phased service query -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseServiceScheduler

open EventGraph Interaction GameTheory.Math.Probability

variable {Player LocalSeed RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Every recorded query's activation list is exactly the preceding actual
activation transcript. Its length is the actual local activation index, with
repeated same-clock activations and all foreign interleavings retained. -/
theorem recorded_query_activationClocks
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (seeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (ordered : graph.RevealRelaxedOrdered) (plan : RuntimePhasePlan graph)
    (input : graph.Inputs) (players : Player → (app).Policy) (count : Nat)
    (execution : (app).Execution)
    (reached : execution ∈ ((app).runRounds
      ((controller runtime leaks priority decideLocal).family seeds) players count
        (ReactiveApplication.Execution.initial app (PhaseRuntimeState.initial plan input))).support)
    (coordinate : PhaseSeedAddress graph) (owner : Player)
    (actor : graph.actor? coordinate.1.event = some owner)
    (before : List (app).EnvironmentEntry) (entry : (app).EnvironmentEntry)
    (after : List (app).EnvironmentEntry)
    (recorded : execution.environmentRecall = before ++ entry :: after)
    (query : PhaseSeedOperationalInput graph)
    (queried : (controller runtime leaks priority decideLocal).request seeds.1 before
      entry.beforeView = some (coordinate, query)) :
    query.activationClocks = activationTranscript runtime leaks priority decideLocal seeds.1
      coordinate owner before := by
  let initial := ReactiveApplication.Execution.initial app (PhaseRuntimeState.initial plan input)
  let scheduler := (controller runtime leaks priority decideLocal).family seeds
  have recalled : execution.environmentRecall = initial.environmentRecall ++ before ++
      entry :: after := by
    simpa only [initial, ReactiveApplication.Execution.initial, List.nil_append] using recorded
  obtain ⟨used, suffix, prior, middle, _length, prefixReached, priorRecall, viewEq,
    _chosen, _dispatched, _future⟩ := (app).runRounds_recorded_entry scheduler players count
      initial execution reached before entry after recalled
  have priorRecallEq : prior.environmentRecall = before := by
    simpa only [initial, ReactiveApplication.Execution.initial, List.nil_append] using priorRecall
  have requested : (controller runtime leaks priority decideLocal).request seeds.1
      prior.environmentRecall (prior.observeEnvironment app) = some (coordinate, query) := by
    rw [priorRecallEq, ← viewEq]
    exact queried
  have initialWord := PhaseSeedScheduler.initial_wordRecall runtime leaks
    (PhaseRuntimeState.initial plan input)
  have word := PhaseSeedScheduler.runRounds_wordRecall runtime leaks scheduler players used
    initial prior initialWord prefixReached
  have clocks := runRounds_activationTranscript runtime leaks priority decideLocal seeds ordered
    coordinate owner actor players used initial prior
      (PhaseRuntimeState.initial_invariant plan input).1 initialWord (by rfl) prefixReached
  have inputEq := request_query runtime leaks priority decideLocal seeds.1 prior coordinate owner
    actor query requested
  rw [inputEq]
  change (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner prior.environmentRecall
    (prior.observeEnvironment app)).activationClocks = _
  rw [PhaseSeedScheduler.localInput_word, word owner coordinate.1, clocks, priorRecallEq]

/-- A query of a still requested coordinate retains its original readiness
stamp, and its elapsed clock is no later than the current local clock. -/
theorem recorded_query_timing
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (seeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (plan : RuntimePhasePlan graph) (input : graph.Inputs)
    (players : Player → (app).Policy) (count : Nat) (execution : (app).Execution)
    (reached : execution ∈ ((app).runRounds
      ((controller runtime leaks priority decideLocal).family seeds) players count
        (ReactiveApplication.Execution.initial app (PhaseRuntimeState.initial plan input))).support)
    (coordinate : PhaseSeedAddress graph) (owner : Player)
    (request : execution.application.SeedRequest owner coordinate.1)
    (before : List (app).EnvironmentEntry) (entry : (app).EnvironmentEntry)
    (after : List (app).EnvironmentEntry)
    (recorded : execution.environmentRecall = before ++ entry :: after)
    (query : PhaseSeedOperationalInput graph)
    (queried : (controller runtime leaks priority decideLocal).request seeds.1 before
      entry.beforeView = some (coordinate, query)) :
    entry.beforeView.application.native.activatedAt coordinate.1.event =
        execution.application.current.native.activatedAt coordinate.1.event ∧
      query.elapsed ≤ (queryAt runtime leaks execution coordinate owner).elapsed := by
  let initial := ReactiveApplication.Execution.initial app (PhaseRuntimeState.initial plan input)
  let scheduler := (controller runtime leaks priority decideLocal).family seeds
  have recalled : execution.environmentRecall = initial.environmentRecall ++ before ++
      entry :: after := by
    simpa only [initial, ReactiveApplication.Execution.initial, List.nil_append] using recorded
  obtain ⟨used, suffix, prior, middle, _length, prefixReached, priorRecall, viewEq,
    chosen, dispatched, future⟩ := (app).runRounds_recorded_entry scheduler players count
      initial execution reached before entry after recalled
  have priorRecallEq : prior.environmentRecall = before := by
    simpa only [initial, ReactiveApplication.Execution.initial, List.nil_append] using priorRecall
  have requested : (controller runtime leaks priority decideLocal).request seeds.1
      prior.environmentRecall (prior.observeEnvironment app) = some (coordinate, query) := by
    rw [priorRecallEq, ← viewEq]
    exact queried
  have selectedQuery : (PhaseSeedCalendar.selectedAt runtime leaks priority seeds.1 prior).bind
      (fun selected => (graph.actor? selected.1.event).map fun acting =>
        (selected, queryAt runtime leaks prior selected acting)) = some (coordinate, query) :=
    requested
  obtain ⟨selected, selectedEq, queryEq⟩ := Option.bind_eq_some_iff.mp selectedQuery
  obtain ⟨acting, _actor, pair⟩ := Option.map_eq_some_iff.mp queryEq
  have sameCoordinate : selected = coordinate := congrArg Prod.fst pair
  have actualSelected : PhaseSeedCalendar.selectedAt runtime leaks priority seeds.1 prior =
      some coordinate := by simpa only [sameCoordinate] using selectedEq
  have valid := ((phaseApplication_invariant runtime leaks input).policyInvariant
    app players).runRounds scheduler used initial prior
      (PhaseRuntimeState.initial_invariant plan input).1 prefixReached
  have ordered := ((phaseApplication_seedOrder runtime leaks).policyInvariant
    app players).runRounds scheduler used initial prior
      (PhaseRuntimeState.initial_ordered plan input) prefixReached
  obtain ⟨principal, oldRequest⟩ := PhaseSeedCalendar.selected_request runtime leaks priority
    seeds.1 prior valid coordinate actualSelected
  have sameAttempt : prior.application.attempt = execution.application.attempt :=
    oldRequest.1.symm.trans request.1
  have remaining : execution ∈ ((app).runRounds scheduler players (suffix + 1) prior).support := by
    change execution ∈ (((app).round scheduler players prior).bind
      ((app).runRounds scheduler players suffix)).support
    rw [PMF.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨middle, ?_, future⟩
    rw [ReactiveApplication.round, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨entry.command, chosen, dispatched⟩
  obtain ⟨ticks, progress⟩ := phase_runRounds_serviceProgress runtime leaks players scheduler
    (suffix + 1) prior execution valid ordered remaining sameAttempt
  obtain ⟨entered, stamp⟩ := valid.active.activatedAt_eq_some_of_ready_actor coordinate.1.event
    oldRequest.2.2.1 (by simp only [request.2.2.2.1, Option.isSome_some])
  have finalStamp := progress.activated coordinate.1.event entered stamp request.2.2.1.1
  have inputEq := request_query runtime leaks priority decideLocal seeds.1 prior coordinate owner
    request.2.2.2.1 query requested
  refine ⟨?_, ?_⟩
  · rw [viewEq]
    exact stamp.trans finalStamp.symm
  · rw [inputEq]
    change prior.application.current.native.clock -
        (prior.application.current.native.activatedAt coordinate.1.event).getD
          prior.application.current.native.clock ≤
      execution.application.current.native.clock -
        (execution.application.current.native.activatedAt coordinate.1.event).getD
          execution.application.current.native.clock
    rw [stamp, finalStamp]
    simp only [Option.getD_some]
    have clock := progress.clock
    omega

end Vegas.EventGraphRuntime.PhaseServiceScheduler
