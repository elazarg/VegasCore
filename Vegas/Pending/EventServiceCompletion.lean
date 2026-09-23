/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventServiceLaw
import Vegas.Pending.CompletionService

/-! # Completion of bounded event service

This file isolates instructions inside the actual service runner.  These
decomposition laws are the bridge from the local sample and expiry semantics
to the bounded whole-service completion proof.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

theorem runService_facts (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (count : Nat) (execution next : runtime.application.PolicyExecution)
    (invariant : execution.native.application.Invariant inputs)
    (supported : next ∈ (runtime.runService roster reactionRounds players wire
      order count execution).support) :
    State.ServiceProgress inputs count execution.native.application
      next.native.application := by
  induction count generalizing execution with
  | zero =>
      simp only [runService, FinDist.mem_support_pure] at supported
      subst next
      exact State.ServiceProgress.refl invariant
  | succ count ih =>
      simp only [runService, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨middle, middleMem, nextMem⟩ := supported
      have first := runtime.serviceEpoch_facts inputs roster reactionRounds players
        wire order execution middle invariant middleMem
      simpa [Nat.add_comm] using first.trans (ih middle first.invariant nextMem)

theorem runService_add (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (first second : Nat) (execution : runtime.application.PolicyExecution) :
    runtime.runService roster reactionRounds players wire order (first + second) execution =
      (runtime.runService roster reactionRounds players wire order first execution).bind
        (runtime.runService roster reactionRounds players wire order second) := by
  induction first generalizing execution with
  | zero => simp [runService]
  | succ first ih =>
      simp only [Nat.succ_add, runService, FinDist.bind_bind]
      apply FinDist.bind_congr
      intro middle _
      exact ih middle

theorem runServicePlan_support_append (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (first second : List (ServiceInstruction graph))
    (execution final : runtime.application.PolicyExecution)
    (supported : final ∈
      (runtime.runServicePlan players wire (first ++ second) execution).support) :
    ∃ middle ∈ (runtime.runServicePlan players wire first execution).support,
      final ∈ (runtime.runServicePlan players wire second middle).support := by
  rw [runServicePlan_append, FinDist.support_bind] at supported
  simp only [Set.mem_iUnion] at supported
  obtain ⟨middle, middleMem, finalMem⟩ := supported
  exact ⟨middle, middleMem, finalMem⟩

theorem runServicePlan_support_instruction (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (before after : List (ServiceInstruction graph))
    (instruction : ServiceInstruction graph)
    (execution final : runtime.application.PolicyExecution)
    (supported : final ∈
      (runtime.runServicePlan players wire
        (before ++ instruction :: after) execution).support) :
    ∃ prior ∈ (runtime.runServicePlan players wire before execution).support,
      ∃ next ∈ (runtime.serviceStep players wire instruction prior).support,
        final ∈ (runtime.runServicePlan players wire after next).support := by
  obtain ⟨prior, priorMem, finalMem⟩ :=
    runtime.runServicePlan_support_append players wire before
      (instruction :: after) execution final supported
  simp only [runServicePlan, FinDist.support_bind, Set.mem_iUnion] at finalMem
  obtain ⟨next, nextMem, restMem⟩ := finalMem
  exact ⟨prior, priorMem, next, nextMem, restMem⟩

private theorem split_at_member {α : Type} (item : α) :
    ∀ {items : List α}, item ∈ items →
      ∃ before after, items = before ++ item :: after := by
  intro items member
  induction items with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨[], tail, rfl⟩
      · obtain ⟨before, after, rfl⟩ := ih member
        exact ⟨head :: before, after, by simp⟩

omit [DecidableEq Player] in
/-- Every epoch plan contains an addressed expiry instruction after its unique
clock tick.  The returned split is used to transport readiness and activation
to that concrete instruction in the actual service runner. -/
theorem epochPlan_split_expire (order : ServiceOrder graph)
    (roster : List Player) (reactionRounds : Nat) (event : graph.EventId) :
    ∃ before after,
      epochPlan order roster reactionRounds =
        before ++ ServiceInstruction.expire event :: after ∧ serviceTicks before = 1 := by
  have member : event ∈ List.finRange graph.order.eventCount :=
    List.mem_finRange event
  have mapped : ServiceInstruction.expire event ∈
      (List.finRange graph.order.eventCount).map ServiceInstruction.expire :=
    List.mem_map.mpr ⟨event, member, rfl⟩
  obtain ⟨expiryBefore, expiryAfter, expiryEq⟩ :=
    split_at_member (ServiceInstruction.expire event) mapped
  let sweep := order.val.flatMap (eventServicePlan roster reactionRounds)
  refine ⟨sweep ++ [.tick] ++ expiryBefore, expiryAfter, ?_, ?_⟩
  · dsimp only [sweep]
    simp only [epochPlan, expiryEq, List.append_assoc]
  · have expiryTicks : serviceTicks
        ((List.finRange graph.order.eventCount).map ServiceInstruction.expire) = 0 := by
      simp [serviceTicks, ServiceInstruction.ticks, Function.comp_def]
    rw [expiryEq, serviceTicks_append, serviceTicks_cons] at expiryTicks
    have expiryBeforeTicks : serviceTicks expiryBefore = 0 := by omega
    have sweepTicks : serviceTicks sweep = 0 := by
      dsimp only [sweep]
      induction order.val with
      | nil => rfl
      | cons current rest ih =>
          simp [List.flatMap_cons, serviceTicks_append,
            eventServicePlan_ticks, ih]
    rw [serviceTicks_append, serviceTicks_append, sweepTicks, expiryBeforeTicks]
    rfl

omit [DecidableEq Player] in
/-- Every epoch also contains the addressed sample attempt before its clock
tick.  For a ready chance node this is the instruction that must complete it. -/
theorem epochPlan_split_sample (order : ServiceOrder graph)
    (roster : List Player) (reactionRounds : Nat) (event : graph.EventId) :
    ∃ before after,
      epochPlan order roster reactionRounds =
        before ++ ServiceInstruction.sample event :: after ∧ serviceTicks before = 0 := by
  obtain ⟨eventsBefore, eventsAfter, orderEq⟩ :=
    split_at_member event (order.mem event)
  let eventPrefix : List (ServiceInstruction graph) :=
    [.grant event] ++
      (match graph.actor? event with
      | none => []
      | some owner => List.replicate 3 (.player owner) ++
          (List.replicate reactionRounds (.wire :: roster.map .player)).flatten ++
          [.includeLatest event owner])
  have eventEq : eventServicePlan roster reactionRounds event =
      eventPrefix ++ [.sample event] := by
    rfl
  let before := eventsBefore.flatMap (eventServicePlan roster reactionRounds) ++
    eventPrefix
  let afterSweep := eventsAfter.flatMap (eventServicePlan roster reactionRounds)
  refine ⟨before, afterSweep ++ [.tick] ++
    (List.finRange graph.order.eventCount).map .expire, ?_, ?_⟩
  · simp [epochPlan, orderEq, before, afterSweep, eventEq, List.flatMap_append,
      List.append_assoc]
  · dsimp only [before]
    rw [serviceTicks_append]
    have allPriorTicks : ∀ events : List graph.EventId,
        serviceTicks (events.flatMap (eventServicePlan roster reactionRounds)) = 0 := by
      intro events
      induction events with
      | nil => rfl
      | cons current rest ih =>
          rw [List.flatMap_cons, serviceTicks_append,
            eventServicePlan_ticks, ih]
    have priorTicks := allPriorTicks eventsBefore
    have prefixTicks : serviceTicks eventPrefix = 0 := by
      have total := eventServicePlan_ticks (graph := graph) roster reactionRounds event
      rw [eventEq, serviceTicks_append] at total
      simpa [serviceTicks, ServiceInstruction.ticks] using total
    omega

/-- A chance event ready at an epoch boundary completes during that epoch,
independently of the adaptive sweep order. -/
theorem serviceEpoch_chance_complete (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (event : graph.EventId) (execution next : runtime.application.PolicyExecution)
    (invariant : execution.native.application.Invariant inputs)
    (ready : execution.native.application.config.cut.Ready event)
    (chance : graph.actor? event = none)
    (supported : next ∈ (runtime.serviceEpoch roster reactionRounds players wire
      order execution).support) :
    event ∈ next.native.application.config.cut.completed := by
  simp only [serviceEpoch, FinDist.support_bind, Set.mem_iUnion] at supported
  obtain ⟨chosen, _, planMem⟩ := supported
  obtain ⟨before, after, planEq, beforeTicks⟩ :=
    epochPlan_split_sample chosen roster reactionRounds event
  rw [planEq] at planMem
  obtain ⟨prior, priorMem, sampled, sampleMem, afterMem⟩ :=
    runtime.runServicePlan_support_instruction players wire before after
      (.sample event) execution next planMem
  have priorProgress := runtime.runServicePlan_facts inputs players wire before
    execution prior invariant priorMem
  rcases priorProgress.ready_or_completed event ready with completed | priorReady
  · have suffixProgress := runtime.runServicePlan_facts inputs players wire
      (.sample event :: after) prior next priorProgress.invariant (by
        simp only [runServicePlan, FinDist.support_bind, Set.mem_iUnion]
        exact ⟨sampled, sampleMem, afterMem⟩)
    exact suffixProgress.completed completed
  · have sampledDone := runtime.serviceStep_sample_complete players wire event
      prior sampled priorReady chance sampleMem
    have afterInvariant := (runtime.serviceStep_facts inputs players wire (.sample event)
      prior sampled priorProgress.invariant sampleMem).invariant
    have suffixProgress := runtime.runServicePlan_facts inputs players wire after
      sampled next afterInvariant afterMem
    exact suffixProgress.completed sampledDone

/-- A strategic event ready at an epoch boundary completes in that epoch once
its retained activation timestamp is due after the epoch's clock tick. -/
theorem serviceEpoch_strategic_complete_of_due (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (event : graph.EventId) (entered : Nat)
    (execution next : runtime.application.PolicyExecution)
    (invariant : execution.native.application.Invariant inputs)
    (ready : execution.native.application.config.cut.Ready event)
    (strategic : (graph.actor? event).isSome = true)
    (activated : execution.native.application.activatedAt event = some entered)
    (dueAfterTick : runtime.deadline event ≤ execution.native.application.clock + 1 - entered)
    (supported : next ∈ (runtime.serviceEpoch roster reactionRounds players wire
      order execution).support) :
    event ∈ next.native.application.config.cut.completed := by
  simp only [serviceEpoch, FinDist.support_bind, Set.mem_iUnion] at supported
  obtain ⟨chosen, _, planMem⟩ := supported
  obtain ⟨before, after, planEq, beforeTicks⟩ :=
    epochPlan_split_expire chosen roster reactionRounds event
  rw [planEq] at planMem
  obtain ⟨prior, priorMem, expired, expireMem, afterMem⟩ :=
    runtime.runServicePlan_support_instruction players wire before after
      (.expire event) execution next planMem
  have priorProgress := runtime.runServicePlan_facts inputs players wire before
    execution prior invariant priorMem
  rcases priorProgress.ready_or_completed event ready with completed | priorReady
  · have suffixProgress := runtime.runServicePlan_facts inputs players wire
      (.expire event :: after) prior next priorProgress.invariant (by
        simp only [runServicePlan, FinDist.support_bind, Set.mem_iUnion]
        exact ⟨expired, expireMem, afterMem⟩)
    exact suffixProgress.completed completed
  · have priorActivated := priorProgress.activated event entered activated priorReady.1
    have priorClock : prior.native.application.clock =
        execution.native.application.clock + 1 := by
      simpa only [beforeTicks] using priorProgress.clock
    have due : runtime.deadline event ≤
        prior.native.application.clock - entered := by
      rw [priorClock]
      exact dueAfterTick
    have expiredDone := runtime.serviceStep_expire_complete players wire event
      prior expired priorReady strategic entered priorActivated due expireMem
    have afterInvariant := (runtime.serviceStep_facts inputs players wire (.expire event)
      prior expired priorProgress.invariant expireMem).invariant
    have suffixProgress := runtime.runServicePlan_facts inputs players wire after
      expired next afterInvariant afterMem
    exact suffixProgress.completed expiredDone

/-- The command service satisfies the same completion contract as other
message protocols; its particular player and network interfaces are parameters. -/
def commandCompletionService (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    CompletionService runtime runtime.application.PolicyExecution where
  state execution := execution.native.application
  epoch := runtime.serviceEpoch roster reactionRounds players wire order
  progress inputs before after := runtime.serviceEpoch_facts inputs roster reactionRounds
    players wire order before after
  chance inputs event before after := runtime.serviceEpoch_chance_complete inputs
    roster reactionRounds players wire order event before after
  due inputs event entered before after := runtime.serviceEpoch_strategic_complete_of_due inputs
    roster reactionRounds players wire order event entered before after

theorem commandCompletionService_run (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (count : Nat) (execution : runtime.application.PolicyExecution) :
    (runtime.commandCompletionService roster reactionRounds players wire order).run
      count execution =
      runtime.runService roster reactionRounds players wire order count execution := by
  induction count generalizing execution with
  | zero => rfl
  | succ count ih =>
      simp only [CompletionService.run, runService, commandCompletionService]
      exact FinDist.bind_congr fun next _ => ih next

/-- One uniform deadline window completes every event that was ready at its
start. Player and wire policies remain arbitrary. -/
theorem runService_window_completes_ready (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (event : graph.EventId) (execution next : runtime.application.PolicyExecution)
    (invariant : execution.native.application.Invariant inputs)
    (ready : execution.native.application.config.cut.Ready event)
    (supported : next ∈ (runtime.runService roster reactionRounds players wire order
      (runtime.maxDeadline + 1) execution).support) :
    event ∈ next.native.application.config.cut.completed := by
  apply (runtime.commandCompletionService
    roster reactionRounds players wire order).window_completes_ready
    inputs event execution next invariant ready
  rwa [runtime.commandCompletionService_run]

/-- The advertised finite service horizon completes the graph under arbitrary
native player and wire policies and an arbitrary adaptive public sweep order. -/
theorem runService_terminal (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (execution next : runtime.application.PolicyExecution)
    (invariant : execution.native.application.Invariant inputs)
    (supported : next ∈ (runtime.runService roster reactionRounds players wire order
      runtime.serviceEpochs execution).support) :
    next.native.application.config.cut.Terminal := by
  apply (runtime.commandCompletionService roster reactionRounds players wire order).terminal
    inputs execution next invariant
  rwa [runtime.commandCompletionService_run]

/-- Every supported native result follows genuine graph steps from an input
in the setup law. This is operational support refinement, not a strategic or
probability-law backtranslation. -/
theorem servicedEventGame_reachable (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (players : Player → runtime.application.PlayerPolicy)
    (next : runtime.application.PolicyExecution)
    (supported : next ∈
      ((runtime.servicedEventGame inputs roster reactionRounds wire order).play players).support) :
    ∃ input ∈ inputs.support, next.native.application.config.Reachable input := by
  simp only [servicedEventGame, FinDist.support_bind, Set.mem_iUnion] at supported
  obtain ⟨input, inputMem, runMem⟩ := supported
  refine ⟨input, inputMem, ?_⟩
  exact (runtime.runService_facts input roster reactionRounds players wire order
    runtime.serviceEpochs _ next (State.initial_invariant input) runMem).invariant.reachable

/-- Every supported play of the concrete serviced game reaches a terminal
event-graph configuration, for arbitrary native player policies. -/
theorem servicedEventGame_complete (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (players : Player → runtime.application.PlayerPolicy)
    (next : runtime.application.PolicyExecution)
    (supported : next ∈
      ((runtime.servicedEventGame inputs roster reactionRounds wire order).play players).support) :
    next.native.application.config.cut.Terminal := by
  simp only [servicedEventGame, FinDist.support_bind, Set.mem_iUnion] at supported
  obtain ⟨input, _, runMem⟩ := supported
  exact runtime.runService_terminal input roster reactionRounds players wire order
    (MessageApplication.PolicyExecution.initial _
      (MessageApplication.State.initial _ (State.initial input))) next
    (by change (State.initial input).Invariant input
        exact State.initial_invariant input) runMem

/-- Terminal typed readout is total on every supported serviced-game result. -/
theorem servicedEventGame_outcome_total (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (players : Player → runtime.application.PlayerPolicy)
    (next : runtime.application.PolicyExecution)
    (supported : next ∈
      ((runtime.servicedEventGame inputs roster reactionRounds wire order).play players).support) :
    next.native.application.config.outcome?.isSome = true := by
  exact (EventGraph.Config.outcome?_isSome _).2
    (runtime.servicedEventGame_complete inputs roster reactionRounds wire order
      players next supported)

end Vegas.EventGraphRuntime
