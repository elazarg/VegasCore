/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServicePrefix
import Vegas.Game.SourceServiceReadout
import Vegas.Game.ServiceRosterAsync
import Vegas.Source.SetupProtocolEvaluation
import Interaction.ReactiveHorizonContinuation

/-! # Ranked completion boundaries under arbitrary reactive scheduling

One scheduler command completes at most one graph event. On the sequentialized
graph, initialized play therefore has a completed event prefix; stopping at the
current event's completion retains all own response views below its successor.
These operational facts hold for arbitrary response policies and schedulers.
The source continuation law is stated separately from its proof for a policy.
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

section Ranked

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- No recorded response has seen `event` ready. -/
def Untouched (event : (graph setup).EventId)
    (execution : (application setup leaks).Execution) : Prop :=
  ∀ who, ∀ entry ∈ execution.recall who,
    ¬ entry.beforeView.application.publicView.EventReady event

/-- Every recorded response saw only events of rank at most `bound` ready. -/
def ReadySeen (bound : Nat) (execution : (application setup leaks).Execution) : Prop :=
  ∀ who, ∀ entry ∈ execution.recall who, ∀ event : (graph setup).EventId,
    entry.beforeView.application.publicView.EventReady event → event.val ≤ bound

/-- A configuration step either stutters or completes one ready event. -/
def ConfigStep (before after : (graph setup).Config) : Prop :=
  after = before ∨ ∃ event, ∃ (ready : before.cut.Ready event)
    (action : (graph setup).Action event), after ∈ (before.step event ready action).support

variable {setup}

/-- At a completed prefix a configuration step stutters or extends the prefix
by exactly one event. -/
theorem ConfigStep.prefix {before after : (graph setup).Config}
    (step : ConfigStep setup before after) (rank : Nat) (ordered : before.cut.IsPrefix rank) :
    after = before ∨ after.cut.IsPrefix (rank + 1) := by
  rcases step with same | ⟨event, ready, action, member⟩
  · exact Or.inl same
  · right
    have rankEq := (ready_iff_rank setup before rank ordered event).mp ready
    rw [before.step_cut event ready action after member]
    exact ordered.complete_at event ready rankEq

/-- A cut is a prefix of at most one length. -/
theorem isPrefix_unique {cut : (graph setup).order.Cut} {first second : Nat}
    (left : cut.IsPrefix first) (right : cut.IsPrefix second) : first = second := by
  by_contra different
  rcases Nat.lt_or_gt_of_ne different with lower | upper
  · have inside : first < (graph setup).order.eventCount := by have := right.1; omega
    have completed := (right.2 ⟨first, inside⟩).mpr lower
    exact Nat.lt_irrefl _ ((left.2 ⟨first, inside⟩).mp completed)
  · have inside : second < (graph setup).order.eventCount := by have := left.1; omega
    have completed := (left.2 ⟨second, inside⟩).mpr upper
    exact Nat.lt_irrefl _ ((right.2 ⟨second, inside⟩).mp completed)

variable (setup)

/-- One scheduler command changes the configuration by one step. -/
theorem environmentStep_configStep (execution next : (application setup leaks).Execution)
    (command : (application setup leaks).Command)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support) :
    ConfigStep setup execution.application.config next.application.config := by
  have ofGraph : ∀ {after : EventGraphRuntime.State (graph setup)},
      GraphStep execution.application after →
        ConfigStep setup execution.application.config after.config := by
    intro after step
    rcases step with ⟨same, _, _⟩ | ⟨event, ready, action, member, _, _⟩
    · exact Or.inl same
    · exact Or.inr ⟨event, ready, action, member⟩
  cases command with
  | application command =>
      have member := (applicationStep_facts execution next command reached).1
      cases command with
      | advanceClock =>
          simp only [EventGraphRuntime.environmentStep, PMF.mem_support_pure_iff] at member
          rw [member]
          exact Or.inl rfl
      | executeSample event =>
          exact ofGraph (graphStep_executeSample (runtime setup) _ _ event member)
      | expire event =>
          exact ofGraph (graphStep_expire (runtime setup) _ _ event member)
  | activate who =>
      unfold ReactiveApplication.Execution.environmentStep at reached
      rw [PMF.support_map] at reached
      obtain ⟨updated, supported, rfl⟩ := reached
      rw [PMF.support_map] at supported
      obtain ⟨_, _, rfl⟩ := supported
      exact Or.inl rfl
  | wait =>
      unfold ReactiveApplication.Execution.environmentStep at reached
      rw [PMF.support_map] at reached
      obtain ⟨updated, supported, rfl⟩ := reached
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact Or.inl rfl
  | «include» id =>
      unfold ReactiveApplication.Execution.environmentStep at reached
      rw [PMF.support_map] at reached
      obtain ⟨updated, supported, rfl⟩ := reached
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact ofGraph (graphStep_includePending (runtime setup) leaks execution id)

/-- One scheduler round from a completed prefix: every new response sees only
the current event ready, and the prefix grows by at most one event. -/
theorem round_prefix (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (rank : Nat)
    (execution next : (application setup leaks).Execution)
    (ordered : execution.application.config.cut.IsPrefix rank)
    (seen : ReadySeen setup leaks rank execution)
    (reached : next ∈ ((application setup leaks).round scheduler players execution).support) :
    ReadySeen setup leaks rank next ∧
      (next.application.config = execution.application.config ∨
        next.application.config.cut.IsPrefix (rank + 1)) := by
  let app := application setup leaks
  obtain ⟨command, _, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  have recallEq := app.environmentStep_recall execution middle command moved
  have middleConfig := (environmentStep_configStep setup leaks execution middle command
    moved).prefix rank ordered
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
    obtain ⟨configEq, _⟩ := (runtime setup).reactive_respond_application leaks middle who response
    refine ⟨?_, Or.inl (by rw [configEq, sameApp])⟩
    intro observer entry member event readyView
    rcases app.respond_entry_origin middle who observer response entry member with
      prior | ⟨_, fresh⟩
    · rw [recallEq] at prior
      exact seen observer entry prior event readyView
    · rw [fresh] at readyView
      change middle.application.publicView.EventReady event at readyView
      have readyNow := (State.publicView_eventReady _ event).mp readyView
      rw [sameApp] at readyNow
      exact ((ready_iff_rank setup _ rank ordered event).mp readyNow).le
  · have idle : command.actor? app = none := by
      cases command with
      | activate who => exact (activation ⟨who, rfl⟩).elim
      | «include» _ => rfl
      | application _ => rfl
      | wait => rfl
    rw [idle] at resumed
    simp only [ReactiveApplication.resume, PMF.mem_support_pure_iff] at resumed
    subst resumed
    refine ⟨?_, middleConfig⟩
    intro observer entry member
    rw [recallEq] at member
    exact seen observer entry member

/-- Every execution reached by complete rounds from initialization has a
completed prefix, and its recorded responses saw nothing beyond it. -/
theorem roundsFrom_ranked (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (count : Nat)
    (execution : (application setup leaks).Execution)
    (supported : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support) :
    ∃ rank, execution.application.config.cut.IsPrefix rank ∧
      ReadySeen setup leaks rank execution := by
  induction count generalizing execution with
  | zero =>
      obtain ⟨state, stateMem, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      cases (PMF.mem_support_pure_iff _ _).mp reached
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ stateMem
      refine ⟨0, EventOrder.Cut.empty_isPrefix _, ?_⟩
      intro who entry member
      simp [ReactiveApplication.Execution.initial] at member
  | succ count ih =>
      rw [ReactiveApplication.roundsFrom_succ] at supported
      obtain ⟨prior, priorMem, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      obtain ⟨rank, ordered, seen⟩ := ih prior priorMem
      obtain ⟨nextSeen, nextConfig⟩ :=
        round_prefix setup leaks scheduler players rank prior execution ordered seen moved
      rcases nextConfig with same | advanced
      · exact ⟨rank, by rw [same]; exact ordered, nextSeen⟩
      · exact ⟨rank + 1, advanced, fun who entry member event readyView =>
          (nextSeen who entry member event readyView).trans (Nat.le_succ _)⟩

/-- Rounds stopped at the completion of the current event keep the recorded
views below the next event, and stop at its completion or earlier. -/
theorem runUntil_completion_prefix (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (event : (graph setup).EventId)
    (count : Nat) (execution stopped : (application setup leaks).Execution)
    (ordered : execution.application.config.cut.IsPrefix event.val)
    (seen : ReadySeen setup leaks event.val execution)
    (reached : stopped ∈ ((application setup leaks).runUntil scheduler players
      (fun final => event ∈ final.application.config.cut.completed) count execution).support) :
    ReadySeen setup leaks event.val stopped ∧
      (stopped.application.config.cut.IsPrefix event.val ∨
        stopped.application.config.cut.IsPrefix (event.val + 1)) := by
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨seen, Or.inl ordered⟩
  | succ count ih =>
      by_cases halt : event ∈ execution.application.config.cut.completed
      · rw [ReactiveApplication.runUntil_of_stop _ _ _ _ _ execution halt] at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        exact ⟨seen, Or.inl ordered⟩
      · simp only [ReactiveApplication.runUntil, halt, ↓reduceIte] at reached
        obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
        obtain ⟨middleSeen, middleConfig⟩ :=
          round_prefix setup leaks scheduler players event.val execution middle ordered seen moved
        rcases middleConfig with same | advanced
        · exact ih middle (by rw [same]; exact ordered) middleSeen rest
        · have finished : event ∈ middle.application.config.cut.completed :=
            (advanced.2 event).mpr (Nat.lt_succ_self _)
          rw [ReactiveApplication.runUntil_of_stop _ _ _ _ _ middle finished] at rest
          cases (PMF.mem_support_pure_iff _ _).mp rest
          exact ⟨middleSeen, Or.inr advanced⟩

/-- An execution where the events of rank below `rank` have completed, no
recorded response has seen the event of rank `rank` ready, and which the
players reach by complete rounds from initialization. -/
structure CompletionBoundary (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (rank : Nat)
    (execution : (application setup leaks).Execution) : Prop where
  supported : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
    players execution.environmentRecall.length).support
  ordered : execution.application.config.cut.IsPrefix rank
  untouched : ∀ event : (graph setup).EventId, event.val = rank →
    Untouched setup leaks event execution

/-- From every completion boundary within the horizon, the players' run to the
horizon has the source continuation law of the configuration's typed prefix. -/
def BoundaryContinuationLaw (scheduler : (application setup leaks).Scheduler) (horizon : Nat)
    (players : Player → (application setup leaks).Policy)
    (profile : BehavioralProfile setup.program) : Prop :=
  ∀ rank (execution : (application setup leaks).Execution),
    CompletionBoundary setup leaks scheduler players rank execution →
    execution.environmentRecall.length ≤ horizon →
    ((application setup leaks).runToHorizon scheduler players horizon execution).map
        (fun final => sourceReadout setup leaks ((application setup leaks).finished final)) =
      (setup.continuationLaw profile
        (sourceServicePrefix? setup rank execution.application.config)).map some

end Ranked

end Vegas
