module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.EventCompletionStopping
public import Vegas.EventGraph.CanonicalStep
public import Interaction.ReactiveRecallInvariant

@[expose] public section

/-! # Sequential graph prefixes at native completion boundaries -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

section

variable {timeouts : EventTimeouts graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}

local notation "app" => (reactiveApplication timeouts) leaks

/-- An initialized execution at a completed graph prefix in which no player has seen
an event after the prefix ready. -/
structure PrefixBoundary (initial : PMF (State graph)) (scheduler : (app).Scheduler)
    (players : Player → (app).Policy) (rank : Nat) (execution : (app).Execution) : Prop where
  supported : execution ∈ ((app).roundsFrom initial scheduler players
    execution.environmentRecall.length).support
  ordered : execution.application.config.cut.IsPrefix rank
  untouched : ∀ event : graph.EventId, rank ≤ event.val → ∀ who, ∀ entry ∈ execution.logs who,
    ¬ entry.beforeView.application.publicView.EventReady event

/-- An initialized state with an empty cut is a boundary of rank zero. -/
theorem PrefixBoundary.initial (initial : PMF (State graph)) (scheduler : (app).Scheduler)
    (players : Player → (app).Policy) (state : State graph) (present : state ∈ initial.support)
    (empty : state.config.cut.IsPrefix 0) :
    PrefixBoundary initial scheduler players 0 (ReactiveApplication.Execution.initial (app)
      state) := by
  refine ⟨?_, empty, fun event _ who entry member => nomatch member⟩
  change _ ∈ ((app).roundsFrom initial scheduler players 0).support
  rw [ReactiveApplication.roundsFrom, PMF.support_bind]
  exact Set.mem_iUnion₂.mpr ⟨state, present, by simp [ReactiveApplication.runRounds]⟩

/-- Every recorded callback saw ready events only up through the given rank. -/
def RememberedReadyAtMost (bound : Nat) (execution : (app).Execution) : Prop :=
  ∀ who, ∀ entry ∈ execution.logs who, ∀ event : graph.EventId,
    entry.beforeView.application.publicView.EventReady event → event.val ≤ bound

end

variable (timeouts : EventTimeouts graph.sequentialize)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize))

/-- One scheduler round preserves the starting bound on remembered ready events
and extends the completed prefix through its actual finite graph path. -/
private theorem round_prefix (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy) (rank : Nat)
    (execution next : ((reactiveApplication timeouts) leaks).Execution)
    (ordered : execution.application.config.cut.IsPrefix rank)
    (seen : RememberedReadyAtMost rank execution)
    (reached : next ∈ (((reactiveApplication timeouts) leaks).round scheduler players
      execution).support) :
    RememberedReadyAtMost rank next ∧
      ∃ actualRank, rank ≤ actualRank ∧ next.application.config.cut.IsPrefix actualRank := by
  let app := (reactiveApplication timeouts) leaks
  obtain ⟨command, _, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  have recallEq := app.environmentStep_recall execution middle command moved
  have path := ((reactiveApplication_graphSteps timeouts) leaks).environmentStep
    execution middle command moved
  have middlePrefix := EventGraph.Config.Step.path_isPrefix_sequential graph
    path ordered
  change next ∈ (app.resume players (command.actor? app) middle).support at resumed
  by_cases activation : ∃ who, command = .activate who
  · obtain ⟨who, rfl⟩ := activation
    have sameApp : middle.application = execution.application := by
      unfold ReactiveApplication.Execution.environmentStep at moved
      rw [PMF.support_map] at moved
      obtain ⟨updated, supported, rfl⟩ := moved
      rw [PMF.support_map] at supported
      obtain ⟨_, _, rfl⟩ := supported
      rfl
    change next ∈ (app.invoke players who middle).support at resumed
    rw [ReactiveApplication.invoke, PMF.support_map] at resumed
    obtain ⟨response, _, rfl⟩ := resumed
    obtain ⟨configEq, _⟩ := (reactive_respond_application timeouts) leaks middle who response
    refine ⟨?_, rank, le_rfl, ?_⟩
    swap
    · rw [configEq, sameApp]
      exact ordered
    intro observer entry member event readyView
    rcases app.respond_entry_origin middle who observer response entry member with
      prior | ⟨_, fresh⟩
    · rw [recallEq] at prior
      exact seen observer entry prior event readyView
    · rw [fresh] at readyView
      change middle.application.publicView.EventReady event at readyView
      have readyNow := (State.publicView_eventReady _ event).mp readyView
      rw [sameApp] at readyNow
      have actual : execution.application.config.cut.IsPrefix event.val :=
        ⟨event.isLt.le, fun query =>
          graph.sequentialize_mem_completed_iff_lt_of_ready _ readyNow⟩
      exact (actual.unique ordered).le
  · have idle : command.actor? app = none := by
      cases command with
      | activate who => exact (activation ⟨who, rfl⟩).elim
      | «include» _ => rfl
      | application _ => rfl
      | wait => rfl
    rw [idle] at resumed
    simp only [ReactiveApplication.resume, PMF.mem_support_pure_iff] at resumed
    subst resumed
    refine ⟨?_, middlePrefix⟩
    intro observer entry member
    rw [recallEq] at member
    exact seen observer entry member


/-- Every execution from an empty initial cut ends a round at a prefix, and no
recorded activation has seen an event beyond that prefix ready. -/
theorem roundsFrom_prefix (initial : PMF (State graph.sequentialize))
    (empty : ∀ state ∈ initial.support, state.config.cut.IsPrefix 0)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy) (count : Nat)
    (execution : ((reactiveApplication timeouts) leaks).Execution)
    (supported : execution ∈ (((reactiveApplication timeouts) leaks).roundsFrom initial
      scheduler players count).support) :
    ∃ rank, execution.application.config.cut.IsPrefix rank ∧
      RememberedReadyAtMost rank execution := by
  induction count generalizing execution with
  | zero =>
      obtain ⟨state, present, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨0, empty state present, fun _ _ member => nomatch member⟩
  | succ count ih =>
      rw [ReactiveApplication.roundsFrom_succ] at supported
      obtain ⟨prior, priorMem, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      obtain ⟨rank, ordered, seen⟩ := ih prior priorMem
      obtain ⟨nextSeen, nextRank, lower, nextPrefix⟩ :=
        round_prefix timeouts leaks scheduler players rank prior execution ordered seen moved
      exact ⟨nextRank, nextPrefix, fun who entry member event ready =>
        (nextSeen who entry member event ready).trans lower⟩

/-- Stopping at an event's completion preserves its starting view bound. The
endpoint is its original prefix if unfinished, or an actual strictly later prefix. -/
private theorem runUntil_completion_prefix
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (event : graph.sequentialize.EventId)
    (count : Nat) (execution stopped : ((reactiveApplication timeouts) leaks).Execution)
    (ordered : execution.application.config.cut.IsPrefix event.val)
    (seen : RememberedReadyAtMost event.val execution)
    (reached : stopped ∈ (((reactiveApplication timeouts) leaks).runUntil scheduler players
      (fun final => event ∈ final.application.config.cut.completed) count execution).support) :
    RememberedReadyAtMost event.val stopped ∧
      (stopped.application.config.cut.IsPrefix event.val ∨
        ∃ actualRank, event.val < actualRank ∧
          stopped.application.config.cut.IsPrefix actualRank) := by
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨seen, Or.inl ordered⟩
  | succ count ih =>
      have unfinished : event ∉ execution.application.config.cut.completed :=
        fun done => (Nat.lt_irrefl _ ((ordered.2 event).mp done)).elim
      simp only [ReactiveApplication.runUntil, unfinished, ↓reduceIte] at reached
      obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨middleSeen, actualRank, lower, middlePrefix⟩ :=
        round_prefix timeouts leaks scheduler players event.val execution middle ordered
          seen moved
      by_cases finished : event ∈ middle.application.config.cut.completed
      · rw [ReactiveApplication.runUntil_of_stop _ _ _ _ _ middle finished] at rest
        cases (PMF.mem_support_pure_iff _ _).mp rest
        exact ⟨middleSeen, Or.inr ⟨actualRank, (middlePrefix.2 event).mp finished, middlePrefix⟩⟩
      · have upper : actualRank ≤ event.val := by
          by_contra advanced
          exact finished ((middlePrefix.2 event).mpr (by omega))
        have same : actualRank = event.val := by omega
        rw [same] at middlePrefix
        exact ih middle middlePrefix middleSeen rest

/-- The first completion of the ready head event yields the actual strictly later
initialized boundary, including any simultaneously completed automatic events. -/
theorem PrefixBoundary.stopped {initial : PMF (State graph.sequentialize)}
    {scheduler : ((reactiveApplication timeouts) leaks).Scheduler}
    {players : Player → ((reactiveApplication timeouts) leaks).Policy} {horizon : Nat}
    (event : graph.EventId) (before : ((reactiveApplication timeouts) leaks).Execution)
    (boundary : PrefixBoundary initial scheduler players event.val before)
    (bounded : before.environmentRecall.length ≤ horizon)
    (after : ((reactiveApplication timeouts) leaks).Execution)
    (reached : after ∈ (((reactiveApplication timeouts) leaks).runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon before).support)
    (finished : event ∈ after.application.config.cut.completed) :
    after.environmentRecall.length ≤ horizon ∧ ∃ rank, event.val < rank ∧
      PrefixBoundary initial scheduler players rank after := by
  let app := (reactiveApplication timeouts) leaks
  have seen : RememberedReadyAtMost event.val before := by
    intro who entry member query ready
    by_contra! later
    exact boundary.untouched query later.le who entry member ready
  obtain ⟨used, within, _, length⟩ := app.runUntil_runRounds scheduler players _ _ before
    after reached
  obtain ⟨stoppedSeen, current | ⟨rank, later, ordered⟩⟩ := runUntil_completion_prefix
    timeouts leaks scheduler players event _ before after boundary.ordered seen reached
  · exact (Nat.lt_irrefl _ ((current.2 event).mp finished)).elim
  · refine ⟨by omega, rank, later, app.roundsFrom_runUntil scheduler players initial _ _
      before after boundary.supported reached, ordered, ?_⟩
    intro next rankNext observer entry member ready
    have := stoppedSeen observer entry member next ready
    omega

end Vegas.EventGraphRuntime
