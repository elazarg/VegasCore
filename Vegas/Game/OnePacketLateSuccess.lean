module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import GameTheoryExtensions.Analysis.Protocol.StoppedTerminalBound
public import Vegas.Game.SourceServiceAsyncStep
public import Vegas.Game.RevealServiceCalendarState
public import Vegas.Game.OnePacketLawApproximation
public import Vegas.Game.OnePacketExclusionPayoff
public import Vegas.Game.OnePacketIntendedProjection
public import Vegas.Game.OnePacketCompletion
public import Vegas.Game.OnePacketPrescribedSupport
public import Vegas.Game.OnePacketEventFailure

@[expose] public section

/-! # The successful part of a late delivery

**Pending steps.** While the event of rank `rank` is pending, every control
step keeps the completed prefix and the recorded views below the event, or
completes the event at scheduler control, with the recorded views unchanged
(`Vegas.pendingTransition`).

The public completion order determines a site's rank, and the pending event
determines its freshness. At its first completion stop, every supported native
continuation consists of one primary graph step and automatic completion
(`Vegas.lateStop_primary_drain`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

variable (setup timeouts leaks) in
/-- The configuration is a prefix of `rank` and the recorded views saw nothing
beyond it. -/
def PendingAt (rank : Nat) (execution : (application setup timeouts leaks).Execution) : Prop :=
  execution.application.config.cut.IsPrefix rank ∧ ReadySeen setup leaks rank execution

/-- **Pending steps.** From a state pending at `rank`, every transition keeps it
pending at `rank`, or completes the event of rank `rank` at scheduler control
with the recorded views still seeing nothing beyond `rank`. -/
theorem pendingTransition {initial : PMF (application setup timeouts leaks).State} {horizon : Nat}
    {scheduler : (application setup timeouts leaks).Scheduler} {rank remaining : Nat}
    {actor : Option Player} {execution : (application setup timeouts leaks).Execution}
    (pending : PendingAt setup timeouts leaks rank execution)
    (joint : Player → Option (application setup timeouts leaks).Action)
    {after : (application setup timeouts leaks).ProtocolState}
    (reached : after ∈ ((application setup timeouts leaks).transition initial horizon scheduler
      (some ⟨remaining, actor, execution⟩) joint).support) :
    ∃ control : (application setup timeouts leaks).Control, after = some control ∧
      (PendingAt setup timeouts leaks rank control.execution ∨
        (control.actor = none ∧ ReadySeen setup leaks rank control.execution ∧
          ∃ actualRank, rank < actualRank ∧
            control.execution.application.config.cut.IsPrefix actualRank)) := by
  let app := application setup timeouts leaks
  obtain ⟨ordered, seen⟩ := pending
  cases actor with
  | some who =>
      change after ∈ (PMF.pure _).support at reached
      rw [PMF.mem_support_pure_iff] at reached
      subst reached
      refine ⟨_, rfl, Or.inl ⟨?_, ?_⟩⟩
      · change (execution.respond app who ((joint who).getD ⟨none⟩)).application.config.cut.IsPrefix
          rank
        rw [((reactive_respond_application timeouts) leaks execution who _).1]
        exact ordered
      · intro observer entry member event readyView
        rcases app.respond_entry_origin execution who observer _ entry member with
          prior | ⟨_, fresh⟩
        · exact seen observer entry prior event readyView
        · rw [fresh] at readyView
          change execution.application.publicView.EventReady event at readyView
          exact ((ready_iff_rank setup _ rank ordered event).mp
            ((State.publicView_eventReady _ event).mp readyView)).le
  | none =>
      cases remaining with
      | zero =>
          change after ∈ (PMF.pure _).support at reached
          rw [PMF.mem_support_pure_iff] at reached
          subst reached
          exact ⟨_, rfl, Or.inl ⟨ordered, seen⟩⟩
      | succ remaining =>
          obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
          obtain ⟨next, stepped, rfl⟩ := PMF.support_map .. ▸ moved
          have recallEq := app.environmentStep_recall execution next command stepped
          have nextSeen : ReadySeen setup leaks rank next := by
            intro observer entry member
            rw [recallEq] at member
            exact seen observer entry member
          refine ⟨_, rfl, ?_⟩
          have path := ((reactiveApplication_graphSteps timeouts) leaks).environmentStep
            execution next command stepped
          obtain ⟨actualRank, lower, advanced⟩ :=
            EventGraph.Config.Step.path_isPrefix_sequential setup.eventGraph path ordered
          by_cases same : actualRank = rank
          · exact Or.inl ⟨same ▸ advanced, nextSeen⟩
          · right
            refine ⟨?_, nextSeen, actualRank, by omega, advanced⟩
            cases command with
            | activate who =>
                exfalso
                have sameApp := activation_application setup leaks execution next who stepped
                have orderedNext : next.application.config.cut.IsPrefix rank := by
                  rw [sameApp]
                  exact ordered
                exact same (advanced.unique orderedNext)
            | wait | «include» _ | application _ => rfl

/-- Every execution of a legal history of the supplied runtime is pending at
some rank: its configuration is a prefix, and its recorded views saw nothing
beyond it. -/
theorem pendingAt_serviceInvariant (scheduler : (application setup timeouts leaks).Scheduler) :
    (application setup timeouts leaks).ServiceInvariant scheduler
      (fun execution => ∃ rank, PendingAt setup timeouts leaks rank execution) where
  respond execution who action valid := by
    obtain ⟨rank, ordered, seen⟩ := valid
    refine ⟨rank, ?_, ?_⟩
    · rw [((reactive_respond_application timeouts) leaks execution who action).1]
      exact ordered
    · intro observer entry member event readyView
      rcases (application setup timeouts leaks).respond_entry_origin execution who observer action
        entry
          member with prior | ⟨_, fresh⟩
      · exact seen observer entry prior event readyView
      · rw [fresh] at readyView
        change execution.application.publicView.EventReady event at readyView
        exact ((ready_iff_rank setup _ rank ordered event).mp
          ((State.publicView_eventReady _ event).mp readyView)).le
  environment execution next command valid _ stepped := by
    obtain ⟨rank, ordered, seen⟩ := valid
    have recallEq := (application setup timeouts leaks).environmentStep_recall execution next
      command
      stepped
    have path := ((reactiveApplication_graphSteps timeouts) leaks).environmentStep
      execution next command stepped
    obtain ⟨actualRank, lower, orderedNext⟩ :=
      EventGraph.Config.Step.path_isPrefix_sequential setup.eventGraph path ordered
    refine ⟨actualRank, orderedNext, fun observer entry member event readyView => ?_⟩
    rw [recallEq] at member
    exact (seen observer entry member event readyView).trans lower

/-- Every execution reached along a legal history of the supplied runtime is
pending at some rank. -/
theorem pendingAt_history {horizon : Nat} {scheduler : (application setup timeouts leaks).Scheduler}
    {control : (application setup timeouts leaks).Control}
    (trace : ((application setup timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace
      (some control)) :
    ∃ rank, PendingAt setup timeouts leaks rank control.execution :=
  (pendingAt_serviceInvariant (timeouts := timeouts) scheduler).history (initialLaw setup) horizon
    (fun state supported => by
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨0, EventOrder.Cut.empty_isPrefix _, fun _ entry member =>
        by simp [ReactiveApplication.Execution.initial] at member⟩) trace

/-- **The rank of a site**: the number of events its public completion order
records. -/
def siteRank : (application setup timeouts leaks).Info → Nat
  | none => 0
  | some (_, view) => view.application.publicView.observation.completionOrder.length

/-- The site's pending event, if any, has not failed. -/
def siteFresh (who : Player) (info : (application setup timeouts leaks).Info)
    (control : (application setup timeouts leaks).Control) : Prop :=
  match pendingEvent setup timeouts leaks who info with
  | some event => ¬ StoreEventFailed control.execution.application.config.store event
  | none => True

section CompletionStops

variable [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

/-- At the first completion stop, the ready event has one primary graph step
followed by the native automatic completion. -/
theorem lateStop_primary_drain
    (certificate : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu timeouts leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    {sent : (graph setup).Config} {rank : Nat} (ordered : sent.cut.IsPrefix rank)
    {event : (graph setup).EventId} (ready : sent.cut.Ready event)
    (terminalCompleted : ∀ (final : (application setup timeouts leaks).Control),
      ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some final) →
      (application setup timeouts leaks).terminal (some final) →
      final.execution.application.config = sent →
      event ∈ final.execution.application.config.cut.completed)
    (start : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).History) {control : (application setup timeouts leaks).Control}
    (current : start.state = some control)
    (atSent : control.execution.application.config = sent) :
    ∀ stop ∈ (((bounds.onePacketMenu timeouts leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil certificate players
        (LateStopped setup timeouts leaks bounds horizon scheduler rank) start).support,
      ∃ final, stop.state = some final ∧
        ∃ (action : (graph setup).Action event) (primary : EventGraphRuntime.State (graph setup)),
          primary.config ∈ (sent.step event ready action).support ∧
            final.execution.application.config = primary.drain.config := by
  intro stop member
  let menu := bounds.onePacketMenu timeouts leaks
  let model := menu.information (initialLaw setup) horizon scheduler
  have rankEq := (ready_iff_rank setup sent rank ordered event).mp ready
  let held := fun reachedState : (application setup timeouts leaks).ProtocolState =>
    ∃ reachedControl, reachedState = some reachedControl ∧
      (reachedControl.execution.application.config = sent ∨
        ∃ (action : (graph setup).Action event) (primary : EventGraphRuntime.State (graph setup)),
          primary.config ∈ (sent.step event ready action).support ∧
            reachedControl.execution.application.config = primary.drain.config)
  have closed := model.runBehavioralUntil_support_closed certificate players
    (LateStopped setup timeouts leaks bounds horizon scheduler rank) held
    (fun history going _ joint legal target holds reached => by
      obtain ⟨before, beforeState, atBefore⟩ := holds
      have reached' : target ∈ ((application setup timeouts leaks).transition (initialLaw setup)
        horizon scheduler history.state joint).support := reached
      rw [beforeState] at reached'
      obtain ⟨next, rfl, _⟩ := (application setup timeouts leaks).transition_recall_prefix
        (initialLaw setup) horizon scheduler before target joint reached'
      refine ⟨next, rfl, ?_⟩
      rcases atBefore with same | ⟨action, primary, inStep, drained⟩
      · have rawTrace := menu.toRawTrace (initialLaw setup) horizon scheduler
          (beforeState ▸ history.trace)
        have facts := legalFacts setup leaks horizon scheduler before rawTrace
        rcases reactive_protocol_primary_or_stutter timeouts leaks (initialLaw setup) horizon
          scheduler before next joint facts.quiescent reached' with
          stays | ⟨completed, completedReady, found, primary, inStep, drained⟩
        · exact Or.inl (stays.trans same)
        · have sameEvent : completed = event :=
            setup.eventGraph.sequentialize_ready_unique _ completedReady (same.symm ▸ ready)
          subst completed
          exact Or.inr ⟨found, primary, by simpa only [same] using inStep, drained⟩
      · have primaryDone : event ∈ primary.config.cut.completed := by
          rw [sent.step_cut event ready action _ inStep, EventOrder.Cut.mem_complete]
          exact Or.inl rfl
        have done : event ∈ before.execution.application.config.cut.completed := by
          rw [drained]
          exact EventGraph.Config.Step.path_completed_mono primary.drain_graph_steps primaryDone
        exact (going ⟨before, beforeState, event, done, rankEq⟩).elim)
    start ⟨control, current, Or.inl atSent⟩ stop member
  have ends := model.mem_support_runBehavioralUntil certificate players _ start stop member
  obtain ⟨final, finalState, atFinal⟩ := closed
  refine ⟨final, finalState, ?_⟩
  rcases atFinal with same | stepped
  · exfalso
    rcases ends with ⟨other, otherState, completed, done, sameRank⟩ | ended
    · rw [finalState] at otherState
      cases Option.some.inj otherState
      have sameEvent : completed = event := Fin.ext (sameRank.trans rankEq.symm)
      subst completed
      rw [same] at done
      exact ready.1 done
    · rw [finalState] at ended
      exact ready.1 (by
        rw [← same]
        exact terminalCompleted final (finalState ▸ stop.trace) ended same)
  · exact stepped

end CompletionStops

section Success

variable [Fintype Player] (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup timeouts leaks).Scheduler)
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)


open Classical in
variable (setup timeouts leaks) in
/-- The intended, fresh source point at the actual endpoint after the target
source event completes. -/
def completionPoint (rank : Nat) (fresh : (application setup timeouts leaks).Control → Prop)
    (history : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup)
      horizon scheduler).History) : Option (ProtocolState setup.program) :=
  match history.state with
  | none => none
  | some control =>
      if LateStopped setup timeouts leaks bounds horizon scheduler rank history then
        match decodedPoint setup control.execution.application.config with
        | some point =>
            if ProtocolState.Intended setup.program point ∧ fresh control then some point
            else none
        | none => none
      else none

open Classical in
variable (setup timeouts leaks) in
/-- The source continuation value at the actual completed endpoint, when the
target event has completed and that endpoint is intended and fresh. -/
def completionValue (profile : BehavioralProfile setup.program) (rank : Nat)
    (fresh : (application setup timeouts leaks).Control → Prop) (who : Player)
    (fallback : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup)
      horizon scheduler).History → ℝ)
    (history : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup)
      horizon scheduler).History) : ℝ :=
  (completionPoint setup timeouts leaks bounds horizon scheduler rank fresh history).elim
    (fallback history) (sourcePointValue setup parameter utility excludedPayoff profile who)

end Success

section Transport

variable [Fintype Player] (bounds : MessageBounds (graph setup)) {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

/-- One step of play in the one-packet game follows a transition of the
runtime. -/
theorem onePacket_step_transition
    (profile : ∀ who,
      (onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
        scheduler).BehavioralPolicy who)
    {history next : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup)
      horizon scheduler).History}
    (running : ¬ ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup)
      horizon scheduler).terminal history.state)
    (member : next ∈ ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler).runBehavioralFrom profile 1 history).support) :
    ∃ joint : Player → Option (application setup timeouts leaks).Action,
      next.state ∈ ((application setup timeouts leaks).transition (initialLaw setup) horizon
        scheduler
        history.state joint).support := by
  obtain ⟨⟨joint, _, realized⟩, _⟩ :=
    (onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler).mem_support_runBehavioralFrom_one profile running member
  exact ⟨joint, realized⟩

end Transport

end Vegas
