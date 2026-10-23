/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveServiceProgress
import Vegas.Pending.CompletionService
import Vegas.Pending.ReactiveStateInvariant
import Vegas.Pending.EventActivationOrigin

/-! # Timely recurring owner opportunities after dependency settlement

The existing reactive epoch visits every event before its one clock tick.
An event newly activated during an arbitrary epoch is at most one tick old
at the boundary. Its next reserved owner activation therefore remains timely
when the configured deadline is at least two, unless another allowed action
has already completed the event. Player omissions, malformed submissions,
passive leaks, and network reactions are unrestricted.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Every operation of the reactive application starts timers exactly: a
timestamp is kept, or a newly activated event is stamped with the clock at the
operation. This covers arbitrary submissions, inclusions and environment
commands. -/
theorem reactiveActivationStart (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
    (runtime.reactiveApplication leaks).StepRelation State.ActivationStart where
  refl _ := State.activationStart_of_activatedEq rfl
  submit state who material := State.activationStart_of_activatedEq
    (congrArg PublicView.activatedAt
      (runtime.reactiveApplication_submit_publicView leaks state who material))
  handle state message next accepted := State.activationStart_of_refreshEq
    (handle_clock_activated runtime state next ⟨message.id, message.payload.call⟩
      (reactiveHandle_call accepted)).2
  environment state command next reached := by
    cases command with
    | advanceClock =>
        simp only [reactiveApplication, environmentStep, PMF.mem_support_pure_iff _ _]
          at reached
        subst next
        exact State.activationStart_of_activatedEq rfl
    | executeSample event =>
        obtain ⟨_, stutter | changed⟩ :=
          runtime.environmentStep_executeSample_config_activated state next event reached
        · exact State.activationStart_of_activatedEq stutter.2
        · obtain ⟨_, _, _, activated⟩ := changed
          exact State.activationStart_of_refreshEq activated
    | expire event =>
        obtain ⟨_, stutter | changed⟩ :=
          runtime.environmentStep_expire_config_activated state next event reached
        · exact State.activationStart_of_activatedEq stutter.2
        · obtain ⟨_, _, _, activated⟩ := changed
          exact State.activationStart_of_refreshEq activated

/-- **Exact timer start over histories.** In every transition of the reactive
protocol, under arbitrary player responses and every scheduler, an event that
had no activation timestamp and has one afterwards is stamped with the clock at
which the transition starts, and a running timestamp is never replaced. -/
theorem reactive_transition_activationStart (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (before after : (runtime.reactiveApplication leaks).Control)
    (joint : Player → Option (runtime.reactiveApplication leaks).Action)
    (reached : some after ∈ ((runtime.reactiveApplication leaks).transition initial horizon
      scheduler (some before) joint).support) :
    State.ActivationStart before.execution.application after.execution.application :=
  (runtime.reactiveActivationStart leaks).transition initial horizon scheduler before after
    joint reached

theorem reactive_respond_activationOrigin (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (action : (runtime.reactiveApplication leaks).Action) :
    State.ActivationOrigin execution.application
      (execution.respond (runtime.reactiveApplication leaks) who action).application :=
  ((runtime.reactiveActivationStart leaks).respond execution who action).activationOrigin

theorem reactive_environment_activationOrigin (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (supported : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support) : State.ActivationOrigin execution.application next.application :=
  ((runtime.reactiveActivationStart leaks).environmentStep execution next command
    supported).activationOrigin

theorem reactive_dispatch_activationOrigin (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (invariant : execution.application.Invariant inputs)
    (supported : next ∈ ((runtime.reactiveApplication leaks).dispatch players command
      execution).support) : State.ActivationOrigin execution.application next.application := by
  obtain ⟨middle, environment, response⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  have first := runtime.reactive_environment_activationOrigin leaks execution middle command
    environment
  have progress := runtime.reactive_environment_progress leaks inputs execution middle command
    invariant environment
  have second : State.ActivationOrigin middle.application next.application := by
    cases actor : command.actor? (runtime.reactiveApplication leaks) with
    | none =>
        rw [actor] at response
        cases (PMF.mem_support_pure_iff _ _).mp response
        exact State.activationOrigin_of_activatedEq rfl
    | some who =>
        rw [actor] at response
        obtain ⟨action, _, rfl⟩ := PMF.support_map .. ▸ response
        exact runtime.reactive_respond_activationOrigin leaks middle who action
  exact first.trans second (by rw [progress.clock]; omega)
    (runtime.reactive_resume_progress leaks inputs players _ middle next
      progress.invariant response).completed

omit [DecidableEq Player] in
theorem interactionEpoch_split_owner (chosen : ServiceOrder graph) (networkTurns : Nat)
    (event : graph.EventId) (owner : Player) (actor : graph.actor? event = some owner) :
    ∃ before after, interactionEpoch chosen networkTurns =
      before ++ ServiceInstruction.player owner :: after ∧ serviceTicks before = 0 := by
  obtain ⟨earlier, later, split⟩ := List.mem_iff_append.mp (chosen.mem event)
  let visits := earlier.flatMap (interactionVisit networkTurns)
  refine ⟨visits,
    List.replicate networkTurns .wire ++ [.includeLatest event owner, .sample event] ++
      later.flatMap (interactionVisit networkTurns) ++ [.tick] ++
      (List.finRange graph.order.eventCount).map .expire, ?_, ?_⟩
  · simp only [interactionEpoch, split, List.flatMap_append, List.flatMap_cons,
      interactionVisit, actor, visits, List.append_assoc, List.cons_append,
      List.nil_append]
  · have allZero : ∀ events : List graph.EventId,
          serviceTicks (events.flatMap (interactionVisit networkTurns)) = 0 := by
      intro events
      induction events with
      | nil => rfl
      | cons current rest ih =>
          rw [List.flatMap_cons, serviceTicks_append, interactionVisit_ticks, ih]
    exact allZero earlier

end Vegas.EventGraphRuntime
