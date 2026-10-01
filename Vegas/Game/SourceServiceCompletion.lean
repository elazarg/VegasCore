/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceLocalComparison
import Vegas.Game.ServiceRosterAsync

/-! # The completion-stopped phase law

On the sequentialized graph one event is ready at a time. After a response at
a decision, the run is stopped when the decision's event completes
(`TimedApproximant.completionLaw`). At every stopping point the completed
events are exactly those up to and including the decision's event, and no
recorded response has seen the next event ready: its owner has had no turn yet
(`TimedApproximant.completion_boundary`). This holds for every scheduler that
completes play, since only scheduler commands complete events and every
command completes at most one.

The continuation bridge (`TimedApproximant.response_completion_law`) is then
the Markov property of the round evaluator at this stopping time: the readout
after a response is the configuration law at completion, bound with the
continuation from the next boundary. It assumes only that continuations from
such boundaries follow the source (`BoundaryContinuationLaw`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
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

variable [Fintype Player]

namespace TimedApproximant

variable {service : SourceServiceSpec Player L} (approx : TimedApproximant service)

/-- The execution after one current response, stopped when the decision's
event completes or at the horizon. -/
def completionLaw {who : Player}
    {execution : (application service.setup service.leaks).Execution}
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    (response : (application service.setup service.leaks).Action) :
    PMF (application service.setup service.leaks).Execution :=
  (application service.setup service.leaks).runUntilHorizon service.scheduler approx.players
    (fun final => phase.event ∈ final.application.config.cut.completed) service.planLength
    (execution.respond (application service.setup service.leaks) who response)

/-- The configuration law when the decision's event completes. -/
def completionConfigLaw {who : Player}
    {execution : (application service.setup service.leaks).Execution}
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    (response : (application service.setup service.leaks).Action) :
    PMF (graph service.setup).Config :=
  (approx.completionLaw phase response).map (fun final => final.application.config)

/-- **The completion boundary.** Every point where a legal response's run stops
lies within the horizon, has completed exactly the events up to the decision's
event, and no recorded response has seen the next event ready. -/
theorem completion_boundary
    (completes : CompletesPlay (runtime service.setup) service.leaks (initialLaw service.setup)
      service.planLength service.scheduler)
    {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    (response : (application service.setup service.leaks).Action)
    (allowed : response ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who))
    (stopped : (application service.setup service.leaks).Execution)
    (reached : stopped ∈ (approx.completionLaw phase response).support) :
    stopped.environmentRecall.length ≤ service.planLength ∧
      CompletionBoundary service.setup service.leaks service.scheduler approx.players
        (phase.event.val + 1) stopped := by
  let app := application service.setup service.leaks
  let stop := fun final : app.Execution => phase.event ∈ final.application.config.cut.completed
  let responded := execution.respond app who response
  have accounted := (service.menu.roundSupported_uniform (initialLaw service.setup)
    service.planLength service.scheduler trace).1
  change execution.environmentRecall.length + remaining = service.planLength at accounted
  have respondedLength : responded.environmentRecall.length = execution.environmentRecall.length :=
    congrArg List.length (app.respond_environmentRecall execution who response)
  obtain ⟨respondedTrace⟩ := service.menu.trace_respond (initialLaw service.setup)
    service.planLength service.scheduler remaining execution who response trace allowed
  obtain ⟨bounded, ⟨stoppedTrace⟩⟩ := service.menu.trace_runUntilHorizon (initialLaw service.setup)
    service.planLength service.scheduler approx.players approx.covered stop remaining responded
    stopped (by rw [respondedLength]; exact accounted) respondedTrace reached
  have supported := service.menu.fullyMixed_response_stopped_support (initialLaw service.setup)
    service.planLength service.scheduler approx.players approx.covered approx.assessment
    approx.strategy approx.mixed who remaining execution trace response allowed stop _ stopped
    reached
  have respondedSupported := service.menu.fullyMixed_response_rounds_support
    (initialLaw service.setup) service.planLength service.scheduler approx.players approx.covered
    approx.assessment approx.strategy approx.mixed who remaining execution trace response allowed
    0 responded ((PMF.mem_support_pure_iff _ _).mpr rfl)
  obtain ⟨rank, rankOrdered, seen⟩ := roundsFrom_ranked service.setup service.leaks
    service.scheduler approx.players _ responded respondedSupported
  have ordered : responded.application.config.cut.IsPrefix phase.event.val := by
    rw [((runtime service.setup).reactive_respond_application service.leaks execution who
      response).1]
    exact ⟨Nat.le_of_lt phase.event.isLt, fun prior =>
      service.setup.eventGraph.sequentialize_mem_completed_iff_lt_of_ready
        execution.application.config.cut phase.ready⟩
  have rankEq := isPrefix_unique rankOrdered ordered
  subst rankEq
  obtain ⟨stoppedSeen, stoppedConfig⟩ := runUntil_completion_prefix service.setup service.leaks
    service.scheduler approx.players phase.event _ responded stopped ordered seen reached
  have finished : stopped.application.config.cut.IsPrefix (phase.event.val + 1) := by
    rcases stoppedConfig with current | advanced
    · exfalso
      have unfinished : phase.event ∉ stopped.application.config.cut.completed := fun member =>
        Nat.lt_irrefl _ ((current.2 phase.event).mp member)
      rcases app.runUntilHorizon_stopped service.scheduler approx.players stop
          service.planLength remaining responded stopped
          (by rw [respondedLength]; exact accounted) reached with halted | spent
      · exact unfinished halted
      · have terminalTrace := service.menu.toRawTrace (initialLaw service.setup)
          service.planLength service.scheduler stoppedTrace
        have terminal := completes _ terminalTrace (by
          change service.planLength - stopped.environmentRecall.length = 0 ∧ _
          exact ⟨by omega, rfl⟩)
        change stopped.application.config.cut.completed = Finset.univ at terminal
        exact unfinished (terminal ▸ Finset.mem_univ _)
    · exact advanced
  refine ⟨bounded, supported, finished, ?_⟩
  intro next rankNext observer entry member readyView
  have := stoppedSeen observer entry member next readyView
  omega

/-- **Completion-stopped continuation bridge.** After any legal response at an
actual decision, the complete typed source terminal law is the source
continuation from the next event boundary, averaged over the configuration law
when the decision's event completes. It holds for every scheduler that
completes play, given source continuations from completion boundaries. -/
theorem response_completion_law
    (completes : CompletesPlay (runtime service.setup) service.leaks (initialLaw service.setup)
      service.planLength service.scheduler)
    (continuation : BoundaryContinuationLaw service.setup service.leaks service.scheduler
      service.planLength approx.players approx.profile)
    {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    (response : (application service.setup service.leaks).Action)
    (allowed : response ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who)) :
    approx.responseReadout phase response =
      (approx.completionConfigLaw phase response).bind
        (approx.boundaryContinuation (phase.event.val + 1)) := by
  unfold responseReadout completionConfigLaw
  rw [(application service.setup service.leaks).runToHorizon_eq_runUntilHorizon_bind
    service.scheduler approx.players
    (fun final => phase.event ∈ final.application.config.cut.completed) service.planLength _,
    PMF.map_bind, PMF.bind_map]
  apply bind_congr_on_support _
  intro stopped reached
  obtain ⟨bounded, boundary⟩ :=
    approx.completion_boundary completes trace phase response allowed stopped reached
  exact continuation _ stopped boundary bounded

end TimedApproximant

end Vegas
