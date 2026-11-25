module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.PrefixBoundary
public import Vegas.Pending.ConfigDrain
public import Vegas.Pending.ReactiveStateInvariant
public import Vegas.EventGraph.PrefixConfiguration

@[expose] public section

/-! # Actual ledger stops at the successive graph ranks -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- If the event at the prefix rank was completed in the drain, going one rank
further into that drain gives the same eventual configuration. -/
theorem drainConfig_rankPrefix_succ (graph : Vegas.EventGraph Player L)
    {origin : graph.sequentialize.Config} (event : graph.EventId)
    (orderedOrigin : origin.cut.IsPrefix event.val)
    (done : event ∈ (State.drainConfig origin).cut.completed) :
    let next := Config.rankPrefix (event.val + 1) (State.drainConfig origin)
    next.cut.IsPrefix (event.val + 1) ∧
      State.drainConfig next = State.drainConfig origin := by
  let state := State.ofConfig origin
  have configEq : state.drain.config = State.drainConfig origin := state.drain_config_eq
  have started : state.config.cut.IsPrefix event.val := orderedOrigin
  have ready : state.config.cut.Ready event := started.ready event.isLt
  rw [← configEq] at done ⊢
  rcases state.drain_trace.cases_head with same | ⟨middle, moved, path⟩
  · exact (ready.1 (same ▸ done)).elim
  · obtain ⟨other, automatic, rfl⟩ := moved
    have unique (query : graph.EventId) (enabled : state.config.cut.Ready query) : query = event :=
      graph.sequentialize_ready_unique _ enabled ready
    have same := unique other automatic.1
    subst other
    let middle := state.completeAutomatic event automatic
    obtain ⟨action, supported⟩ := state.completeAutomatic_step event automatic
    have ordered : middle.config.cut.IsPrefix (event.val + 1) := by
      rw [state.config.step_cut event automatic.1 action middle.config supported]
      exact started.complete_at event automatic.1 rfl
    have recovered := Config.rankPrefix_of_path ordered (State.automatic_path_graph_steps path)
    refine ⟨recovered ▸ ordered, ?_⟩
    rw [recovered, ← middle.drain_config_eq]
    exact congrArg State.config (state.drain_eq_completeAutomatic_of_unique event automatic
      (fun query enabled => unique query enabled)).symm

variable (timeouts : EventTimeouts graph.sequentialize)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize))

local notation "app" => (reactiveApplication timeouts) leaks

/-- Successively stop the actual ledger at each graph event. Ranks already
completed by automatic service use the same execution, including its recall. -/
def physicalPrefix (scheduler : (app).Scheduler) (players : Player → (app).Policy)
    (inputs : PMF graph.sequentialize.Inputs) (horizon : Nat) : Nat → PMF (app).Execution
  | 0 => inputs.map fun seed => ReactiveApplication.Execution.initial app (State.initial seed)
  | rank + 1 =>
      if inside : rank < graph.order.eventCount then
        (physicalPrefix scheduler players inputs horizon rank).bind fun before =>
          (app).runUntilHorizon scheduler players
            (fun final => (⟨rank, inside⟩ : graph.EventId) ∈
              final.application.config.cut.completed) horizon before
      else physicalPrefix scheduler players inputs horizon rank

/-- Advancing an in-range rank is one actual stopped native phase. -/
theorem physicalPrefix_succ (scheduler : (app).Scheduler) (players : Player → (app).Policy)
    (inputs : PMF graph.sequentialize.Inputs) (horizon : Nat)
    (event : graph.sequentialize.EventId) :
    physicalPrefix timeouts leaks scheduler players inputs horizon (event.val + 1) =
      (physicalPrefix timeouts leaks scheduler players inputs horizon event.val).bind
        (fun before => (app).runUntilHorizon scheduler players
          (fun final => event ∈ final.application.config.cut.completed) horizon before) := by
  have inside : event.val < graph.order.eventCount := event.isLt
  simp only [physicalPrefix, dite_eq_left inside]
  cases event
  rfl

/-- The stop at a rank has the actual initialized history. The graph prefix
at the specified rank drains to the native configuration, even across ranks
already passed by automatic completion. -/
theorem physicalPrefix_supported (scheduler : (app).Scheduler) (players : Player → (app).Policy)
    (inputs : PMF graph.sequentialize.Inputs) (horizon : Nat)
    (completes : CompletesPlay timeouts leaks (inputs.map State.initial) horizon scheduler)
    (rank : Nat) (bounded : rank ≤ graph.order.eventCount) (execution : (app).Execution)
    (member : execution ∈ (physicalPrefix timeouts leaks scheduler players inputs
      horizon rank).support) :
    ∃ actualRank, rank ≤ actualRank ∧
      PrefixBoundary (inputs.map State.initial) scheduler players actualRank execution ∧
      execution.environmentRecall.length ≤ horizon ∧
      (Config.rankPrefix rank execution.application.config).cut.IsPrefix rank ∧
      execution.application.config =
        State.drainConfig (Config.rankPrefix rank execution.application.config) := by
  classical
  induction rank generalizing execution with
  | zero =>
      obtain ⟨seed, present, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      let state : State graph.sequentialize := State.initial seed
      have ordered : state.config.cut.IsPrefix 0 := EventOrder.Cut.empty_isPrefix _
      have before := PrefixBoundary.initial (inputs.map State.initial) scheduler players state
        ((PMF.mem_support_map_iff _ _ _).mpr ⟨seed, present, rfl⟩) ordered
      have recovered : Config.rankPrefix 0 state.config = state.config :=
        Config.rankPrefix_of_path ordered .refl
      have fixed : State.drainConfig state.config = state.config := by
        rw [← state.drain_config_eq]
        exact congrArg State.config (state.drain_eq_of_empty rfl)
      refine ⟨0, le_rfl, before, Nat.zero_le _, ?_, ?_⟩
      · change (Config.rankPrefix 0 state.config).cut.IsPrefix 0
        rwa [recovered]
      · change state.config = State.drainConfig (Config.rankPrefix 0 state.config)
        rw [recovered, fixed]
  | succ rank ih =>
      have inside : rank < graph.order.eventCount := by omega
      let event : graph.sequentialize.EventId := ⟨rank, inside⟩
      let stop := fun final : (app).Execution => event ∈ final.application.config.cut.completed
      change execution ∈ (physicalPrefix timeouts leaks scheduler players inputs horizon
        (event.val + 1)).support at member
      rw [physicalPrefix_succ] at member
      obtain ⟨before, seen, stopped⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
      obtain ⟨actualRank, lower, boundary, within, primary, drained⟩ := ih (by omega) before seen
      by_cases done : stop before
      · unfold ReactiveApplication.runUntilHorizon at stopped
        rw [(app).runUntil_of_stop scheduler players stop _ before done,
          PMF.mem_support_pure_iff] at stopped
        subst execution
        have later : rank < actualRank := (boundary.ordered.2 event).mp done
        have completed : event ∈ (State.drainConfig
            (Config.rankPrefix rank before.application.config)).cut.completed := by
          rw [← drained]
          exact done
        obtain ⟨ordered, fixed⟩ := drainConfig_rankPrefix_succ graph event primary completed
        rw [← drained] at ordered fixed
        exact ⟨actualRank, later, boundary, within, ordered, fixed.symm⟩
      · have atRank : actualRank = rank := by
          have notLater : ¬ rank < actualRank :=
            fun later => done ((boundary.ordered.2 event).mpr later)
          omega
        subst actualRank
        have ready : before.application.config.cut.Ready event := boundary.ordered.ready inside
        have progress := runUntilHorizon_event_progress completes event before execution
          boundary.supported within done stopped
        obtain ⟨within', nextRank, advances, nextBoundary⟩ := PrefixBoundary.stopped timeouts leaks
          event before boundary within execution stopped progress.2.2.1
        obtain ⟨trace⟩ := (app).raw_trace_roundsFrom (inputs.map State.initial) horizon scheduler
          players before.environmentRecall.length within before boundary.supported
        have quiescent := reactive_history_quiescent timeouts leaks inputs horizon scheduler trace
        obtain ⟨action, native, moved, completed⟩ := runUntil_completed_primary_drain timeouts
          leaks scheduler players event (horizon - before.environmentRecall.length) before execution
          ready (fun _ enabled => graph.sequentialize_ready_unique _ enabled ready)
          quiescent stopped progress.2.2.1
        have nativePrefix : native.config.cut.IsPrefix (rank + 1) := by
          rw [before.application.config.step_cut event ready action native.config moved]
          exact boundary.ordered.complete_at event ready rfl
        have recovery := Config.rankPrefix_of_path nativePrefix native.drain_graph_steps
        rw [← completed] at recovery
        refine ⟨nextRank, advances, nextBoundary, within', recovery ▸ nativePrefix, ?_⟩
        rw [recovery, completed, native.drain_config_eq]

/-- Every supported continuation of an actual stop preserves the stop's rank
readout. The equality also holds when automatic service has passed that rank. -/
theorem physicalPrefix_rankPrefix_eq_runToHorizon
    (scheduler : (app).Scheduler) (players : Player → (app).Policy)
    (inputs : PMF graph.sequentialize.Inputs) (horizon : Nat)
    (completes : CompletesPlay timeouts leaks (inputs.map State.initial) horizon scheduler)
    (rank : Nat) (bounded : rank ≤ graph.order.eventCount)
    (stopped : (app).Execution)
    (reached : stopped ∈ (physicalPrefix timeouts leaks scheduler players inputs horizon
      rank).support)
    (final : (app).Execution)
    (continued : final ∈ ((app).runToHorizon scheduler players horizon stopped).support) :
    Config.rankPrefix rank stopped.application.config =
      Config.rankPrefix rank final.application.config := by
  obtain ⟨_, _, _, _, ordered, drained⟩ := physicalPrefix_supported timeouts leaks scheduler
    players inputs horizon completes rank bounded stopped reached
  let checkpoint := Config.rankPrefix rank stopped.application.config
  have toStop : Relation.ReflTransGen Config.Step checkpoint stopped.application.config := by
    rw [drained]
    exact (State.ofConfig checkpoint).drain_graph_steps
  have toFinal := reactive_runRounds_graph_steps timeouts leaks scheduler players _ stopped final
    continued
  exact (Config.rankPrefix_of_path ordered (toStop.trans toFinal)).symm

/-- Completing a stopped prefix through the remaining horizon recovers the
entire physical execution law, for every rank. -/
theorem physicalPrefix_bind_runToHorizon (scheduler : (app).Scheduler)
    (players : Player → (app).Policy) (inputs : PMF graph.sequentialize.Inputs)
    (horizon rank : Nat) :
    (physicalPrefix timeouts leaks scheduler players inputs horizon rank).bind
      ((app).runToHorizon scheduler players horizon) =
      (app).roundsFrom (inputs.map State.initial) scheduler players horizon := by
  induction rank with
  | zero =>
      rw [physicalPrefix, PMF.bind_map, ReactiveApplication.roundsFrom, PMF.bind_map]
      rfl
  | succ rank ih =>
      rw [physicalPrefix]
      split
      · rename_i inside
        rw [PMF.bind_bind, ← ih]
        apply bind_congr_on_support _
        intro before _
        exact ((app).runToHorizon_eq_runUntilHorizon_bind scheduler players _ horizon before).symm
      · exact ih

/-- The last rank stop already has the full terminal configuration law. Any
further native traffic has no effect on the completed graph configuration. -/
theorem roundsFrom_config_eq_physicalPrefix (scheduler : (app).Scheduler)
    (players : Player → (app).Policy) (inputs : PMF graph.sequentialize.Inputs) (horizon : Nat)
    (completes : CompletesPlay timeouts leaks (inputs.map State.initial) horizon scheduler) :
    ((app).roundsFrom (inputs.map State.initial) scheduler players horizon).map
        (fun final => final.application.config) =
      (physicalPrefix timeouts leaks scheduler players inputs horizon graph.order.eventCount).map
        (fun final => final.application.config) := by
  rw [← physicalPrefix_bind_runToHorizon timeouts leaks scheduler players inputs horizon
    graph.order.eventCount,
    PMF.map_bind, ← PMF.bind_pure_comp]
  apply bind_congr_on_support _
  intro before present
  obtain ⟨actual, lower, boundary, _⟩ :=
    physicalPrefix_supported timeouts leaks scheduler players inputs horizon completes
      graph.order.eventCount le_rfl before present
  have equal : actual = graph.order.eventCount := le_antisymm boundary.ordered.1 lower
  have terminal := (equal ▸ boundary.ordered).terminal
  change ((app).runRounds scheduler players _ before).map (fun final => final.application.config) =
    PMF.pure before.application.config
  rw [map_congr_on_support _ (g := fun _ => before.application.config) ?_, pmf_map_fun_const]
  intro final reached
  exact Config.Step.path_eq_of_terminal
    (reactive_runRounds_graph_steps timeouts leaks scheduler players _ before final reached)
    terminal

end Vegas.EventGraphRuntime
