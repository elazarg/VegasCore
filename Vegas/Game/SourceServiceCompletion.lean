/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServicePrefix
import Vegas.Source.SetupProtocolEvaluation
import Vegas.Game.RevealServicePayoffs
import Vegas.Pending.ReactiveGraphSteps
import Vegas.Pending.ReactiveStateInvariant
import Vegas.EventGraph.CanonicalStep
import Interaction.ReactiveRoundReachability
import Interaction.ReactiveStopping
import Interaction.ReactiveRecallInvariant

/-! # Completed prefixes and completion boundaries

On the sequentialized graph one event is ready at a time. A native command
can complete several events through automatic completion. Every complete
round extends the completed prefix while preserving its starting bound on
recorded ready-event views. Stopping at an event's completion retains the
actual later prefix rank.

A completion boundary combines a completed prefix, untouched later events
and actual complete-round reachability. Its continuation law uses the sole
source decoder and evaluator from that current endpoint.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

section Ranked

variable (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- No recorded response has seen `event` ready. -/
def Untouched (event : (serviceGraph setup mode).EventId)
    (execution : (serviceApplication setup mode deadline leaks).Execution) : Prop :=
  ∀ who, ∀ entry ∈ execution.recall who,
    ¬ entry.beforeView.application.publicView.EventReady event

/-- Every recorded response saw only events of rank at most `bound` ready. -/
def ReadySeen (bound : Nat) (execution : (serviceApplication setup mode deadline leaks).Execution) :
    Prop := ∀ who, ∀ entry ∈ execution.recall who, ∀ event : (serviceGraph setup mode).EventId,
    entry.beforeView.application.publicView.EventReady event → event.val ≤ bound

/-- An execution where the events of rank below `rank` have completed, no
recorded response has seen the event of rank `rank` ready, and which the
players reach by complete rounds from initialization. -/
structure CompletionBoundary (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy) (rank : Nat)
    (execution : (serviceApplication setup mode deadline leaks).Execution) : Prop where
  supported : execution ∈
      ((serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
          scheduler players execution.environmentRecall.length).support
  ordered : execution.application.config.cut.IsPrefix rank
  untouched : ∀ event : (serviceGraph setup mode).EventId, rank ≤ event.val →
    Untouched setup leaks event execution

/-- From every completion boundary within the horizon, the players' run to the
horizon has the source continuation law of the configuration's typed prefix. -/
def BoundaryContinuationLaw (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (horizon : Nat) (players : Player → (serviceApplication setup mode deadline leaks).Policy)
    (profile : BehavioralProfile setup.program) : Prop := ∀ rank
    (execution : (serviceApplication setup mode deadline leaks).Execution), CompletionBoundary setup
    leaks scheduler players rank execution → execution.environmentRecall.length ≤ horizon →
    ((serviceApplication setup mode deadline leaks).runToHorizon scheduler players horizon
        execution).map
    (fun final => serviceSourceReadout setup mode deadline leaks
        ((serviceApplication setup mode deadline leaks).finished final)) =
    (setup.continuationLaw profile
        (serviceSourcePrefix? setup mode rank execution.application.config)).map some

end Ranked

section Sequential

variable (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- One scheduler round preserves the starting bound on remembered ready events
and extends the completed prefix through its actual finite graph path. -/
theorem round_prefix (scheduler : (application setup runtime leaks).Scheduler)
    (players : Player → (application setup runtime leaks).Policy) (rank : Nat)
    (execution next : (application setup runtime leaks).Execution)
    (ordered : execution.application.config.cut.IsPrefix rank)
    (seen : ReadySeen setup leaks rank execution)
    (reached : next ∈ ((application setup runtime leaks).round scheduler players
      execution).support) :
    ReadySeen setup leaks rank next ∧
      ∃ actualRank, rank ≤ actualRank ∧ next.application.config.cut.IsPrefix actualRank := by
  let app := application setup runtime leaks
  obtain ⟨command, _, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  have recallEq := app.environmentStep_recall execution middle command moved
  have path := (runtime.reactiveApplication_graphSteps leaks).environmentStep
    execution middle command moved
  have middlePrefix := EventGraph.Config.Step.path_isPrefix_sequential setup.eventGraph
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
    obtain ⟨configEq, _⟩ := runtime.reactive_respond_application leaks middle who response
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
          setup.eventGraph.sequentialize_mem_completed_iff_lt_of_ready _ readyNow⟩
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


/-- Every execution reached by complete rounds from initialization has a
completed prefix, and its recorded responses saw nothing beyond it. -/
theorem roundsFrom_ranked (scheduler : (application setup runtime leaks).Scheduler)
    (players : Player → (application setup runtime leaks).Policy) (count : Nat)
    (execution : (application setup runtime leaks).Execution)
    (supported : execution ∈ ((application setup runtime leaks).roundsFrom (initialLaw setup)
      scheduler
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
      obtain ⟨nextSeen, actualRank, lower, nextPrefix⟩ :=
        round_prefix setup runtime leaks scheduler players rank prior execution ordered seen moved
      exact ⟨actualRank, nextPrefix, fun who entry member event readyView =>
        (nextSeen who entry member event readyView).trans lower⟩


/-- Stopping at an event's completion preserves its starting view bound. The
endpoint is its original prefix if unfinished, or an actual strictly later prefix. -/
theorem runUntil_completion_prefix (scheduler : (application setup runtime leaks).Scheduler)
    (players : Player → (application setup runtime leaks).Policy) (event : (graph setup).EventId)
    (count : Nat) (execution stopped : (application setup runtime leaks).Execution)
    (ordered : execution.application.config.cut.IsPrefix event.val)
    (seen : ReadySeen setup leaks event.val execution)
    (reached : stopped ∈ ((application setup runtime leaks).runUntil scheduler players
      (fun final => event ∈ final.application.config.cut.completed) count execution).support) :
    ReadySeen setup leaks event.val stopped ∧
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
        round_prefix setup runtime leaks scheduler players event.val execution middle ordered
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

end Sequential

end Vegas
