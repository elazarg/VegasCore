/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.NativeProtocolEvaluation
import Vegas.Pending.EventServiceLaw
import Vegas.Pending.EventCommitmentBinding
import Vegas.Pending.EventFreshCandidates
import Vegas.Pending.EventStore

/-! # Native action safety and clocks

Every service transition refines the existing message machine. The expansion
is a safety proof: its internal registration steps are not strategic positions.
The actual game has one action and one recall entry per player invocation.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Protocol GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Sending or waiting consumes no clock ticks and preserves every live
activation timestamp. Private memory has no application effect. -/
theorem nativeStep_progress (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (who : Player) (execution next : NativeExecution runtime)
    (action : PlayerAction graph)
    (invariant : execution.native.application.Invariant inputs)
    (reached : next ∈ (runtime.actionStep who execution action).support) :
    State.ServiceProgress inputs 0 execution.native.application next.native.application := by
  have same := FinDist.mem_support_pure.mp reached
  subst next
  have facts := runtime.transmit_application who execution.native action.transmission
  have configEq := facts.1
  have clockEq := congrArg PublicView.clock facts.2.2
  have activatedEq := congrArg PublicView.activatedAt facts.2.2
  refine ⟨invariant.copy configEq clockEq activatedEq, ?_, ?_, ?_⟩
  · simp only [takeAction, configEq, Finset.Subset.refl]
  · exact clockEq
  · intro event entered value _
    change (runtime.transmit who execution.native action.transmission).application.activatedAt _ = _
    change (runtime.transmit who execution.native action.transmission).application.activatedAt =
      execution.native.application.activatedAt at activatedEq
    rw [activatedEq]
    exact value

theorem nativeInstructionStep_progress (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (execution next : NativeExecution runtime)
    (joint : Player → Option (PlayerAction graph))
    (invariant : execution.native.application.Invariant inputs)
    (reached : next ∈ (runtime.nativeInstructionStep wire instruction execution joint).support) :
    State.ServiceProgress inputs instruction.ticks
      execution.native.application next.native.application := by
  cases instruction with
  | player who => exact runtime.nativeStep_progress inputs who execution next _ invariant reached
  | wire | grant event | includeLatest event who | sample event | tick | expire event =>
      obtain ⟨middle, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      exact runtime.serviceStep_facts inputs (fun _ _ _ => FinDist.pure .wait)
        wire _ (execution.environmentExecution runtime) middle invariant supported

theorem nativeInstructionStep_native (runtime : EventGraphRuntime graph)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (execution next : NativeExecution runtime)
    (joint : Player → Option (PlayerAction graph))
    (reached : next ∈ (runtime.nativeInstructionStep wire instruction execution joint).support) :
    ∃ actions, next.native ∈ (runtime.application.run actions execution.native).support := by
  cases instruction with
  | player who => exact runtime.actionStep_native who execution next _ reached
  | wire | grant event | includeLatest event who | sample event | tick | expire event =>
      obtain ⟨middle, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨actions, _, member⟩ := runtime.serviceStep_native_support
        (fun _ _ _ => FinDist.pure .wait) wire _
          (execution.environmentExecution runtime) middle supported
      exact ⟨actions, member⟩

/-- Every continuation step retains the execution, even at an order-selection
boundary; it never reinitializes private inputs or the native state. -/
theorem nativeTransition_native (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (before : NativeControl runtime) (after : NativeProtocolState runtime)
    (joint : Player → Option (PlayerAction graph))
    (reached : after ∈
      (runtime.nativeTransition inputs roster reactionRounds wire order
        (some before) joint).support) :
    ∃ next : NativeControl runtime, after = some next ∧
      ∃ actions, next.execution.native ∈
        (runtime.application.run actions before.execution.native).support := by
  rcases before with ⟨epochs, plan, execution⟩
  cases plan with
  | nil =>
      cases epochs with
      | zero =>
          have same := FinDist.mem_support_pure.mp reached
          exact ⟨_, same, [], FinDist.mem_support_pure.mpr rfl⟩
      | succ epochs =>
          obtain ⟨chosen, _, rfl⟩ := FinDist.support_map .. ▸ reached
          exact ⟨_, rfl, [], FinDist.mem_support_pure.mpr rfl⟩
  | cons instruction rest =>
      obtain ⟨next, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨actions, native⟩ := runtime.nativeInstructionStep_native wire instruction
        execution next joint supported
      exact ⟨_, rfl, actions, native⟩

/-- Fixed commitment meanings survive every legal service continuation step,
including actions that submit or replay arbitrary other candidates. -/
theorem nativeTransition_candidate_fixed (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (before after : NativeControl runtime)
    (joint : Player → Option (PlayerAction graph))
    (candidate : Handle graph)
    (fixed : before.execution.native.application.candidates.lookup candidate ≠ .fresh)
    (reached : some after ∈
      (runtime.nativeTransition inputs roster reactionRounds wire order
        (some before) joint).support) :
    after.execution.native.application.candidates.lookup candidate =
      before.execution.native.application.candidates.lookup candidate := by
  obtain ⟨next, same, actions, native⟩ := runtime.nativeTransition_native inputs roster
    reactionRounds wire order before (some after) joint reached
  have equal := Option.some.inj same
  subst next
  exact runtime.run_candidate_fixed _ _ actions candidate fixed native

/-- Every finite continuation from an initialized native history expands to
an existing native execution. It cannot return to the setup position. -/
theorem native_reaches_native (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    {fuel : Nat}
    {history final : (runtime.nativeProtocol inputs roster reactionRounds wire order).History}
    (path : (runtime.nativeProtocol inputs roster reactionRounds wire order).ReachesWithin
      fuel history final)
    (before : NativeControl runtime) (initialized : history.state = some before) :
    ∃ after : NativeControl runtime, final.state = some after ∧
      ∃ actions, after.execution.native ∈
        (runtime.application.run actions before.execution.native).support := by
  induction path generalizing before with
  | refl fuel history => exact ⟨before, initialized, [], FinDist.mem_support_pure.mpr rfl⟩
  | @step fuel history final joint legal target realized rest ih =>
      have first : target ∈
          (runtime.nativeTransition inputs roster reactionRounds wire order
            (some before) joint).support := by
        simpa only [nativeProtocol, initialized] using realized
      obtain ⟨middle, middleEq, firstActions, firstRun⟩ := runtime.nativeTransition_native
        inputs roster reactionRounds wire order before target joint first
      obtain ⟨after, afterEq, suffix, suffixRun⟩ := ih middle middleEq
      refine ⟨after, afterEq, firstActions ++ suffix, ?_⟩
      simp only [MessageApplication.run_append, FinDist.support_bind, Set.mem_iUnion]
      exact ⟨middle.execution.native, firstRun, suffixRun⟩

/-- Submission-time binding holds across arbitrary native protocol paths,
independently of the chosen policy and of whether the prefix is a proper root. -/
theorem native_reaches_candidate_fixed (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    {fuel : Nat}
    {history final : (runtime.nativeProtocol inputs roster reactionRounds wire order).History}
    (path : (runtime.nativeProtocol inputs roster reactionRounds wire order).ReachesWithin
      fuel history final)
    (before after : NativeControl runtime)
    (initialState : history.state = some before) (finalState : final.state = some after)
    (candidate : Handle graph)
    (fixed : before.execution.native.application.candidates.lookup candidate ≠ .fresh) :
    after.execution.native.application.candidates.lookup candidate =
      before.execution.native.application.candidates.lookup candidate := by
  obtain ⟨next, nextEq, actions, native⟩ := runtime.native_reaches_native inputs roster
    reactionRounds wire order path before initialState
  have same := Option.some.inj (finalState.symm.trans nextEq)
  subst next
  exact runtime.run_candidate_fixed _ _ actions candidate fixed native

/-- Native continuations preserve every typed value already stored, including
private bindings and public results. Later packets cannot replace a winner. -/
theorem native_reaches_store_of_some (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    {fuel : Nat}
    {history final : (runtime.nativeProtocol inputs roster reactionRounds wire order).History}
    (path : (runtime.nativeProtocol inputs roster reactionRounds wire order).ReachesWithin
      fuel history final)
    (before after : NativeControl runtime)
    (initialState : history.state = some before) (finalState : final.state = some after)
    (field : graph.Field) (value : (graph.layout field).Value)
    (stored : before.execution.native.application.config.store field = some value) :
    after.execution.native.application.config.store field = some value := by
  obtain ⟨next, nextEq, actions, native⟩ := runtime.native_reaches_native inputs roster
    reactionRounds wire order path before initialState
  have same := Option.some.inj (finalState.symm.trans nextEq)
  subst next
  exact runtime.applicationRun_store_of_some _ _ actions native field value stored

/-- Every native history retains one actual initial draw and a graph-reachable
configuration. Setup is not resampled at a continuation. -/
theorem native_history_invariant (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    ∀ {state}
      (_trace : (runtime.nativeProtocol inputs roster reactionRounds wire order).Trace state)
      (control : NativeControl runtime), state = some control →
        ∃ input ∈ inputs.support, control.execution.native.application.Invariant input
  | _, .start, _, initialized => by cases initialized
  | _, .extend (source := before) prior joint _ reached, control, initialized => by
      have priorInvariant := runtime.native_history_invariant inputs roster reactionRounds
        wire order prior
      have step : some control ∈
          (runtime.nativeTransition inputs roster reactionRounds wire order
            before joint).support := by
        simpa only [nativeProtocol, initialized] using reached
      cases before with
      | none =>
          simp only [nativeTransition, FinDist.support_map, Set.mem_image] at step
          obtain ⟨input, supported, same⟩ := step
          cases Option.some.inj same
          exact ⟨input, supported, State.initial_invariant input⟩
      | some before =>
          obtain ⟨input, supported, invariant⟩ := priorInvariant before rfl
          obtain ⟨after, same, actions, native⟩ := runtime.nativeTransition_native
            inputs roster reactionRounds wire order before (some control) joint step
          cases Option.some.inj same
          exact ⟨input, supported, runtime.applicationRun_invariant _ _ actions invariant native⟩

/-- Later invocations retain every earlier own-action record, including
records created by deviations. Environment instructions never edit recall. -/
theorem nativeInstructionStep_history_prefix (runtime : EventGraphRuntime graph)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (execution next : NativeExecution runtime) (joint : Player → Option (PlayerAction graph))
    (reached : next ∈ (runtime.nativeInstructionStep wire instruction execution joint).support)
    (who : Player) :
    execution.principalHistory who <+: next.principalHistory who := by
  cases instruction with
  | player actor =>
      have same := FinDist.mem_support_pure.mp reached
      subst next
      by_cases acts : who = actor
      · subst who
        rw [runtime.takeAction_history_self]
        exact List.prefix_append _ _
      · simp only [takeAction, ite_eq_right acts, List.prefix_refl]
  | wire | grant event | includeLatest event actor | sample event | tick | expire event =>
      obtain ⟨middle, _, rfl⟩ := FinDist.support_map .. ▸ reached
      exact List.prefix_refl _

theorem nativeTransition_history_prefix (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (before after : NativeControl runtime) (joint : Player → Option (PlayerAction graph))
    (reached : some after ∈
      (runtime.nativeTransition inputs roster reactionRounds wire order
        (some before) joint).support) (who : Player) :
    before.execution.principalHistory who <+: after.execution.principalHistory who := by
  rcases before with ⟨epochs, plan, execution⟩
  cases plan with
  | nil =>
      cases epochs with
      | zero => cases Option.some.inj (FinDist.mem_support_pure.mp reached); rfl
      | succ epochs =>
          obtain ⟨chosen, _, equal⟩ := FinDist.support_map .. ▸ reached
          cases Option.some.inj equal
          rfl
  | cons instruction rest =>
      obtain ⟨next, supported, equal⟩ := FinDist.support_map .. ▸ reached
      cases Option.some.inj equal
      exact runtime.nativeInstructionStep_history_prefix wire instruction execution next
        joint supported who

/-- Own recall is monotone along arbitrary canonical continuations. This is a
history law, independent of the compiled policy and of proper-root status. -/
theorem native_reaches_history_prefix (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    {fuel : Nat}
    {history final : (runtime.nativeProtocol inputs roster reactionRounds wire order).History}
    (path : (runtime.nativeProtocol inputs roster reactionRounds wire order).ReachesWithin
      fuel history final)
    (before after : NativeControl runtime)
    (initialState : history.state = some before) (finalState : final.state = some after)
    (who : Player) :
    before.execution.principalHistory who <+: after.execution.principalHistory who := by
  induction path generalizing before with
  | refl fuel history =>
      cases Option.some.inj (initialState.symm.trans finalState)
      rfl
  | @step fuel history target joint legal reached realized rest ih =>
      have first : reached ∈
          (runtime.nativeTransition inputs roster reactionRounds wire order
            (some before) joint).support := by
        simpa only [nativeProtocol, initialState] using realized
      obtain ⟨middle, middleEq, _, _⟩ := runtime.nativeTransition_native
        inputs roster reactionRounds wire order before reached joint first
      have firstPrefix := runtime.nativeTransition_history_prefix inputs roster reactionRounds
        wire order before middle joint (middleEq ▸ first) who
      exact firstPrefix.trans (ih middle middleEq finalState)

/-- Every initialized legal native history has fresh, unused candidates,
including histories produced entirely by deviations. Setup is sampled once;
the proof retains the actual catalogue rather than resetting it at a root. -/
theorem native_history_freshCandidates (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    ∀ {state}
      (_trace : (runtime.nativeProtocol inputs roster reactionRounds wire order).Trace state)
      (control : NativeControl runtime), state = some control →
        control.execution.native.application.FreshCandidates
  | _, .start, _, initialized => by cases initialized
  | _, .extend (source := before) prior joint _ reached, control, initialized => by
      have priorFresh := runtime.native_history_freshCandidates inputs roster reactionRounds
        wire order prior
      have step : some control ∈
          (runtime.nativeTransition inputs roster reactionRounds wire order
            before joint).support := by
        simpa only [nativeProtocol, initialized] using reached
      cases before with
      | none =>
          simp only [nativeTransition, FinDist.support_map, Set.mem_image] at step
          obtain ⟨input, _, same⟩ := step
          cases Option.some.inj same
          exact State.initial_freshCandidates input
      | some before =>
          obtain ⟨after, same, actions, native⟩ := runtime.nativeTransition_native
            inputs roster reactionRounds wire order before (some control) joint step
          cases Option.some.inj same
          exact runtime.run_freshCandidates _ _ actions (priorFresh before rfl) native

/-- Player memory belongs to recall. No direct action or service instruction
can populate the application-level sampled-action cache. -/
theorem nativeInstructionStep_remembered (runtime : EventGraphRuntime graph)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (execution next : NativeExecution runtime) (joint : Player → Option (PlayerAction graph))
    (reached : next ∈ (runtime.nativeInstructionStep wire instruction execution joint).support) :
    next.native.application.remembered = execution.native.application.remembered := by
  cases instruction with
  | player who =>
      have same := FinDist.mem_support_pure.mp reached
      subst next
      exact (runtime.transmit_application who execution.native _).2.1
  | wire =>
      obtain ⟨middle, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      simp only [serviceStep, MessageApplication.invoke, MessageApplication.wireEnvironment,
        FinDist.bind_map, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨command, _, member⟩ := supported
      exact runtime.environmentPolicyStep_remembered _ middle _ member
  | grant event | includeLatest event who | sample event | tick | expire event =>
      obtain ⟨middle, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      exact runtime.environmentPolicyStep_remembered _ middle _ supported

theorem nativeTransition_remembered (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (before after : NativeControl runtime) (joint : Player → Option (PlayerAction graph))
    (reached : some after ∈
      (runtime.nativeTransition inputs roster reactionRounds wire order
        (some before) joint).support) :
    after.execution.native.application.remembered =
      before.execution.native.application.remembered := by
  rcases before with ⟨epochs, plan, execution⟩
  cases plan with
  | nil =>
      cases epochs with
      | zero => cases Option.some.inj (FinDist.mem_support_pure.mp reached); rfl
      | succ epochs =>
          obtain ⟨chosen, _, equal⟩ := FinDist.support_map .. ▸ reached
          cases Option.some.inj equal
          rfl
  | cons instruction rest =>
      obtain ⟨next, supported, equal⟩ := FinDist.support_map .. ▸ reached
      cases Option.some.inj equal
      exact runtime.nativeInstructionStep_remembered wire instruction execution next joint supported

/-- The low-level cache is inert at every legal native history. It is absent
from player actions and observations; even deviating players cannot fill it. -/
theorem native_history_no_cache (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    ∀ {state}
      (_trace : (runtime.nativeProtocol inputs roster reactionRounds wire order).Trace state)
      (control : NativeControl runtime), state = some control →
        control.execution.native.application.remembered = fun _ => none
  | _, .start, _, initialized => by cases initialized
  | _, .extend (source := before) prior joint _ reached, control, initialized => by
      have priorEmpty := runtime.native_history_no_cache inputs roster reactionRounds
        wire order prior
      have step : some control ∈
          (runtime.nativeTransition inputs roster reactionRounds wire order
            before joint).support := by
        simpa only [nativeProtocol, initialized] using reached
      cases before with
      | none =>
          simp only [nativeTransition, FinDist.support_map, Set.mem_image] at step
          obtain ⟨input, _, same⟩ := step
          cases Option.some.inj same
          rfl
      | some before =>
          exact (runtime.nativeTransition_remembered inputs roster reactionRounds wire order
            before control joint step).trans (priorEmpty before rfl)

end Vegas.EventGraphRuntime
