/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceQueryOrder

/-! # Strict readiness-relative clock order after an actual wait -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseServiceScheduler

open EventGraph Interaction GameTheory.Math.Probability

variable {Player LocalSeed RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A later actual query of the same coordinate has strictly greater elapsed
time after a nonactivation query. The native invariant rules out truncated
subtraction aliases before readiness. -/
theorem recorded_queries_elapsed_strict_after_nonactivation
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
      (before ++ [first] ++ between) second.beforeView = some (coordinate, secondQuery))
    (idle : (first.command.actor? app).isNone = true) :
    firstQuery.elapsed < secondQuery.elapsed := by
  have clockNe := queried_clock_ne_after_nonactivation runtime leaks priority decideLocal seeds.1
    before first between second.beforeView coordinate firstQuery secondQuery firstRequested idle
      (by simpa only [List.append_assoc, List.singleton_append] using secondRequested)
  have monotone := recorded_queries_elapsed_mono runtime leaks priority decideLocal seeds plan input
    players count execution reached coordinate owner actor before first between second after
      recorded firstQuery secondQuery firstRequested secondRequested
  by_contra notEarlier
  have sameElapsed : firstQuery.elapsed = secondQuery.elapsed := by omega
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
  have sameStamp := (recorded_query_timing runtime leaks priority decideLocal seeds plan input
    players used prior prefixReached coordinate owner request before first between priorRecallEq
      firstQuery firstRequested).1
  have priorRecalled : prior.environmentRecall = initial.environmentRecall ++ before ++
      first :: between := by
    simpa only [initial, ReactiveApplication.Execution.initial, List.nil_append] using priorRecallEq
  obtain ⟨firstUsed, firstSuffix, firstPrior, firstMiddle, _firstLength, firstReached,
    firstRecall, firstView, _firstChosen, _firstDispatched, _firstFuture⟩ :=
      (app).runRounds_recorded_entry scheduler players used initial prior prefixReached before
        first between priorRecalled
  have firstRecallEq : firstPrior.environmentRecall = before := by
    simpa only [initial, ReactiveApplication.Execution.initial, List.nil_append] using firstRecall
  have firstRequestedAt : (controller runtime leaks priority decideLocal).request seeds.1
      firstPrior.environmentRecall (firstPrior.observeEnvironment app) =
        some (coordinate, firstQuery) := by
    rw [firstRecallEq, ← firstView]
    exact firstRequested
  have firstValid := ((phaseApplication_invariant runtime leaks input).policyInvariant
    app players).runRounds scheduler firstUsed initial firstPrior
      (PhaseRuntimeState.initial_invariant plan input).1 firstReached
  obtain ⟨firstPrincipal, firstRequest⟩ := request_sound runtime leaks priority decideLocal seeds.1
    firstPrior firstValid firstRequestedAt
  obtain ⟨entered, stamp⟩ := firstValid.active.activatedAt_eq_some_of_ready_actor
    coordinate.1.event firstRequest.2.2.1 (by simp only [actor, Option.isSome_some])
  have secondStamp : prior.application.current.native.activatedAt coordinate.1.event =
      some entered := by
    rw [firstView] at sameStamp
    exact sameStamp.symm.trans stamp
  have firstInput := request_query runtime leaks priority decideLocal seeds.1 firstPrior coordinate
    owner actor firstQuery firstRequestedAt
  have secondInput := request_query runtime leaks priority decideLocal seeds.1 prior coordinate
    owner actor secondQuery requested
  rw [firstInput, secondInput] at sameElapsed
  change firstPrior.application.current.native.clock -
      (firstPrior.application.current.native.activatedAt coordinate.1.event).getD
        firstPrior.application.current.native.clock =
    prior.application.current.native.clock -
      (prior.application.current.native.activatedAt coordinate.1.event).getD
        prior.application.current.native.clock at sameElapsed
  rw [stamp, secondStamp] at sameElapsed
  simp only [Option.getD_some] at sameElapsed
  have firstStarted := firstValid.active.activated_le coordinate.1.event entered stamp
  have secondStarted := valid.active.activated_le coordinate.1.event entered secondStamp
  apply clockNe
  rw [viewEq, firstView]
  change prior.application.current.native.clock = firstPrior.application.current.native.clock
  omega

end Vegas.EventGraphRuntime.PhaseServiceScheduler
