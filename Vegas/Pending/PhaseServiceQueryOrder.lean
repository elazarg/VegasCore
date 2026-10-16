/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceQueryCommands

/-! # Clock order and permanent tick closure for original phased queries -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseServiceScheduler

open EventGraph Interaction GameTheory.Math.Probability

variable {Player LocalSeed RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

private theorem selected_of_requested
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (rest : RestSeed) (past : List (app).EnvironmentEntry) (view : (app).EnvironmentView)
    (coordinate : PhaseSeedAddress graph) (query : PhaseSeedOperationalInput graph)
    (queried : (controller runtime leaks priority decideLocal).request rest past view =
      some (coordinate, query)) :
    PhaseSeedCalendar.selectOpen runtime leaks
      (PhaseSeedCalendar.replayClosed runtime leaks priority rest past) view
        (priority rest past view) = some coordinate := by
  have selectedQuery : (PhaseSeedCalendar.selectOpen runtime leaks
      (PhaseSeedCalendar.replayClosed runtime leaks priority rest past) view
      (priority rest past view)).bind
        (fun selected => (graph.actor? selected.1.event).map fun acting =>
          (selected, PhaseSeedInput.operational selected.1.attempt
            (PhaseSeedScheduler.localInput runtime leaks selected.1 acting past view))) =
              some (coordinate, query) := queried
  obtain ⟨selected, selectedEq, queryEq⟩ := Option.bind_eq_some_iff.mp selectedQuery
  obtain ⟨acting, _actor, pair⟩ := Option.map_eq_some_iff.mp queryEq
  have same : selected = coordinate := congrArg Prod.fst pair
  simpa only [same] using selectedEq

/-- A nonactivation closes the coordinate at its absolute clock. No later
query of that address can occur at the same clock, under any local rule. -/
theorem queried_clock_ne_after_nonactivation
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (rest : RestSeed) (before : List (app).EnvironmentEntry) (entry : (app).EnvironmentEntry)
    (later : List (app).EnvironmentEntry) (view : (app).EnvironmentView)
    (coordinate : PhaseSeedAddress graph) (firstQuery nextQuery : PhaseSeedOperationalInput graph)
    (first : (controller runtime leaks priority decideLocal).request rest before entry.beforeView =
      some (coordinate, firstQuery))
    (idle : (entry.command.actor? app).isNone = true)
    (next : (controller runtime leaks priority decideLocal).request rest
      (before ++ entry :: later) view = some (coordinate, nextQuery)) :
    view.application.native.clock ≠ entry.beforeView.application.native.clock := by
  intro sameClock
  have selected := selected_of_requested runtime leaks priority decideLocal rest before
    entry.beforeView coordinate firstQuery first
  have selectedNext := selected_of_requested runtime leaks priority decideLocal rest
    (before ++ entry :: later) view coordinate nextQuery next
  apply PhaseSeedCalendar.not_selected_after_nonactivation runtime leaks priority rest
    before later entry.beforeView view coordinate entry.command selected idle sameClock
  simpa only [List.append_assoc, List.singleton_append] using selectedNext

/-- Actual queries of the same surviving address have nondecreasing elapsed
clocks, despite foreign interleavings and arbitrary private responses. -/
theorem recorded_queries_elapsed_mono
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
    (actor : graph.actor? coordinate.1.event = some owner)
    (before : List (app).EnvironmentEntry) (first : (app).EnvironmentEntry)
    (between : List (app).EnvironmentEntry) (second : (app).EnvironmentEntry)
    (after : List (app).EnvironmentEntry)
    (recorded : execution.environmentRecall =
      (before ++ [first] ++ between) ++ second :: after)
    (firstQuery secondQuery : PhaseSeedOperationalInput graph)
    (firstRequested : (controller runtime leaks priority decideLocal).request seeds.1 before
      first.beforeView = some (coordinate, firstQuery))
    (secondRequested : (controller runtime leaks priority decideLocal).request seeds.1
      (before ++ [first] ++ between) second.beforeView = some (coordinate, secondQuery)) :
    firstQuery.elapsed ≤ secondQuery.elapsed := by
  let initial := ReactiveApplication.Execution.initial app (PhaseRuntimeState.initial plan input)
  let scheduler := (controller runtime leaks priority decideLocal).family seeds
  have recalled : execution.environmentRecall = initial.environmentRecall ++
      (before ++ [first] ++ between) ++ second :: after := by
    simpa only [initial, ReactiveApplication.Execution.initial, List.nil_append] using recorded
  obtain ⟨used, suffix, prior, middle, _length, prefixReached, priorRecall, viewEq,
    _chosen, _dispatched, _future⟩ := (app).runRounds_recorded_entry scheduler players count
      initial execution reached (before ++ [first] ++ between) second after recalled
  have priorRecallEq : prior.environmentRecall = before ++ first :: between := by
    simpa only [initial, ReactiveApplication.Execution.initial, List.nil_append,
      List.append_assoc, List.singleton_append] using priorRecall
  have requested : (controller runtime leaks priority decideLocal).request seeds.1
      prior.environmentRecall (prior.observeEnvironment app) = some (coordinate, secondQuery) := by
    rw [priorRecallEq, ← viewEq]
    simpa only [List.append_assoc, List.singleton_append] using secondRequested
  have valid := ((phaseApplication_invariant runtime leaks input).policyInvariant
    app players).runRounds scheduler used initial prior
      (PhaseRuntimeState.initial_invariant plan input).1 prefixReached
  obtain ⟨principal, request⟩ := request_sound runtime leaks priority decideLocal seeds.1 prior
    valid requested
  have principalEq : principal = owner := Option.some.inj (request.2.2.2.1.symm.trans actor)
  subst principal
  have elapsed := (recorded_query_timing runtime leaks priority decideLocal seeds plan input
    players used prior prefixReached coordinate owner request before first between priorRecallEq
      firstQuery firstRequested).2
  have secondInput := request_query runtime leaks priority decideLocal seeds.1 prior coordinate
    owner actor secondQuery requested
  rw [secondInput]
  exact elapsed

end Vegas.EventGraphRuntime.PhaseServiceScheduler
