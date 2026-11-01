/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServicePrefix
import Vegas.Game.SourceServiceReachedDecoding
import Vegas.Game.SourceServiceFacts
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

/-- One round: a scheduler command, its environment step, and the response of
the activated player, if any. -/
theorem round_cases {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {players : Player → (serviceApplication setup mode deadline leaks).Policy}
    {execution next : (serviceApplication setup mode deadline leaks).Execution}
    (reached : next ∈
        ((serviceApplication setup mode deadline leaks).round scheduler players
        execution).support) :
    ∃ command ∈ (scheduler execution.environmentRecall
        (execution.observeEnvironment (serviceApplication setup mode deadline leaks))).support,
      ∃ middle ∈
          (execution.environmentStep (serviceApplication setup mode deadline leaks)
              command).support,
          (command.actor? (serviceApplication setup mode deadline leaks) = none ∧ next = middle) ∨ ∃
          who, command.actor? (serviceApplication setup mode deadline leaks) = some who ∧ ∃ response
          ∈ (players who (middle.recall who)
              (middle.observe (serviceApplication setup mode deadline leaks) who)).support,
              next = middle.respond (serviceApplication setup mode deadline leaks) who
                  response := by
  let app := serviceApplication setup mode deadline leaks
  obtain ⟨command, selected, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  refine ⟨command, selected, middle, moved, ?_⟩
  change next ∈ (app.resume players (command.actor? app) middle).support at resumed
  cases actor : command.actor? app with
  | none =>
      rw [actor] at resumed
      simp only [ReactiveApplication.resume, PMF.mem_support_pure_iff] at resumed
      exact Or.inl ⟨rfl, resumed⟩
  | some who =>
      rw [actor] at resumed
      change next ∈ (app.invoke players who middle).support at resumed
      rw [ReactiveApplication.invoke, PMF.support_map] at resumed
      obtain ⟨response, chosen, rfl⟩ := resumed
      exact Or.inr ⟨who, rfl, response, chosen, rfl⟩

/-- An activation leaves the application unchanged. -/
theorem activation_application
    (execution middle : (serviceApplication setup mode deadline leaks).Execution) (who : Player)
    (moved : middle ∈
        (execution.environmentStep (serviceApplication setup mode deadline leaks)
        (.activate who)).support) :
    middle.application = execution.application := by
  unfold ReactiveApplication.Execution.environmentStep at moved
  rw [PMF.support_map] at moved
  obtain ⟨updated, supported, rfl⟩ := moved
  rw [PMF.support_map] at supported
  obtain ⟨_, _, rfl⟩ := supported
  rfl

/-- Every recorded activation was answered by its player at the public view
the scheduler saw. -/
def ActivationsAnswered (execution : (serviceApplication setup mode deadline leaks).Execution) :
    Prop := ∀ entry ∈ execution.environmentRecall, ∀ who, entry.command = .activate who → ∃ answer ∈
    execution.recall who, answer.beforeView.application.publicView = entry.beforeView.application

/-- Every round answers its activation at the scheduler's public view. -/
theorem round_activationsAnswered
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {players : Player → (serviceApplication setup mode deadline leaks).Policy}
    {execution next : (serviceApplication setup mode deadline leaks).Execution}
    (valid : ActivationsAnswered setup leaks execution)
    (reached : next ∈
        ((serviceApplication setup mode deadline leaks).round scheduler players
        execution).support) :
    ActivationsAnswered setup leaks next := by
  let app := serviceApplication setup mode deadline leaks
  obtain ⟨command, selected, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have recorded := app.dispatch_environmentRecall players command execution next dispatched
  obtain ⟨middle', moved', resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  have recallEq := app.environmentStep_recall execution middle' command moved'
  have grows : ∀ who, execution.recall who ⊆ next.recall who := by
    intro who
    change next ∈ (app.resume players (command.actor? app) middle').support at resumed
    cases actor : command.actor? app with
    | none =>
        rw [actor] at resumed
        simp only [ReactiveApplication.resume, PMF.mem_support_pure_iff] at resumed
        subst resumed
        rw [recallEq]
    | some player =>
        rw [actor] at resumed
        change next ∈ (app.invoke players player middle').support at resumed
        rw [ReactiveApplication.invoke, PMF.support_map] at resumed
        obtain ⟨response, _, rfl⟩ := resumed
        rw [← recallEq]
        exact app.respond_recall_mono middle' player who response
  intro entry member who activated
  rw [recorded] at member
  rcases List.mem_append.mp member with prior | fresh
  · obtain ⟨answer, answered, viewEq⟩ := valid entry prior who activated
    exact ⟨answer, grows who answered, viewEq⟩
  · rw [List.mem_singleton] at fresh
    subst fresh
    change command = .activate who at activated
    subst activated
    have sameApp := activation_application setup leaks execution middle' who moved'
    change next ∈ (app.resume players (some who) middle').support at resumed
    change next ∈ (app.invoke players who middle').support at resumed
    rw [ReactiveApplication.invoke, PMF.support_map] at resumed
    obtain ⟨response, _, rfl⟩ := resumed
    obtain ⟨emitted, recalled, _⟩ := respond_recall_self setup leaks middle' who response
    refine ⟨⟨middle'.observe app who, response, emitted⟩, ?_, ?_⟩
    · rw [recalled]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · change middle'.application.publicView = execution.application.publicView
      rw [sameApp]

variable {setup leaks} in
/-- Every activation in completed rounds has an actual response in own recall,
even if that response was silent or sent a packet for a different event. -/
theorem roundsFrom_activationsAnswered
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {players : Player → (serviceApplication setup mode deadline leaks).Policy} (count : Nat)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (supported : execution ∈
        ((serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
        scheduler players count).support) :
    ActivationsAnswered setup leaks execution := by
  let app := serviceApplication setup mode deadline leaks
  induction count generalizing execution with
  | zero =>
      obtain ⟨state, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      cases (PMF.mem_support_pure_iff _ _).mp reached
      intro entry member
      cases member
  | succ count ih =>
      rw [app.roundsFrom_succ (serviceInitialLaw setup mode) scheduler players count] at supported
      obtain ⟨prior, priorMem, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      exact round_activationsAnswered setup leaks (ih prior priorMem) moved

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

variable {setup} in
/-- Every saved ready event lies at or before the current actual sequential prefix. -/
theorem readySeen_of_rawTrace {horizon rank : Nat}
    {scheduler : (application setup runtime leaks).Scheduler}
    {control : (application setup runtime leaks).Control}
    (trace : ((application setup runtime leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (ordered : control.execution.application.config.cut.IsPrefix rank) :
    ReadySeen setup leaks rank control.execution := by
  have facts := legalFacts setup leaks horizon scheduler control trace
  intro owner entry member event readyView
  by_cases completed : event ∈ control.execution.application.config.cut.completed
  · exact Nat.le_of_lt ((ordered.2 event).mp completed)
  · obtain ⟨extra, order, _together, _activated, _accepted⟩ :=
      facts.eventStable owner entry member event readyView completed
    have ready := ready_of_eventReady_extends order readyView completed
    have actual : control.execution.application.config.cut.IsPrefix event.val :=
      ⟨event.isLt.le, fun query =>
        setup.eventGraph.sequentialize_mem_completed_iff_lt_of_ready _ ready⟩
    exact (actual.unique ordered).le

/-- **A reached boundary.** The execution of a legal history at a scheduler
boundary, whose configuration is a prefix at `rank`, with every event from
`rank` on untouched and every own submission made at its author's turn. -/
structure ReachedBoundary (horizon : Nat) (scheduler : (application setup runtime leaks).Scheduler)
    (rank : Nat) (execution : (application setup runtime leaks).Execution) : Prop where
  trace : Nonempty (((application setup runtime leaks).protocol (initialLaw setup) horizon
    scheduler).Trace (some ⟨horizon - execution.environmentRecall.length, none, execution⟩))
  bounded : execution.environmentRecall.length ≤ horizon
  ordered : execution.application.config.cut.IsPrefix rank
  untouched : ∀ event : (graph setup).EventId, rank ≤ event.val →
    Untouched setup leaks event execution
  turns : ∀ who, OwnSubmissionsAtTurn setup leaks execution who


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


variable {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Every initialized raw native history has a residual of the same source evaluator. -/
theorem SourceResidual.of_rawTrace (profile : BehavioralProfile setup.program)
    (horizon : Nat) (scheduler : (application setup runtime leaks).Scheduler) :
    ∀ {state} (_trace : ((application setup runtime leaks).protocol (initialLaw setup)
      horizon scheduler).Trace state) (control : (application setup runtime leaks).Control),
      state = some control →
      ∃ rank,
        Nonempty (SourceResidual setup profile rank control.execution.application.config) := by
  intro state trace
  induction trace with
  | start => intro _ initialized; cases initialized
  | @extend before after prior joint _ realized ih =>
      intro control current
      subst current
      cases before with
      | none =>
          change some control ∈ ((initialLaw setup).map fun state =>
            some ⟨horizon, none, ReactiveApplication.Execution.initial
              (application setup runtime leaks) state⟩).support at realized
          obtain ⟨state, supported, same⟩ := PMF.support_map .. ▸ realized
          cases Option.some.inj same
          obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
          exact ⟨0, ⟨SourceResidual.initial setup profile initial⟩⟩
      | some previous =>
          obtain ⟨rank, ⟨residual⟩⟩ := ih previous rfl
          exact residual.path (reactive_protocol_graph_steps runtime leaks
            (initialLaw setup) horizon scheduler previous control joint realized)

end Vegas
