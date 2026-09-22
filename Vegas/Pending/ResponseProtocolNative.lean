/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ResponseProtocolEvaluation
import Vegas.Pending.EventServiceLaw
import Vegas.Pending.EventCommitmentBinding
import Vegas.Pending.EventFreshCandidates

/-! # Native safety and clocks under atomic responses

Every service transition expands to existing native actions. The response
boundary removes scheduling between private commands; it does not change their
application semantics, submission-time binding, or the environmental clock.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Protocol GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem afterPrivateWork_progress (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (who : Player) (work : List runtime.application.PrivateCommand)
    (execution : runtime.application.PolicyExecution)
    (invariant : execution.native.application.Invariant inputs) :
    State.ServiceProgress inputs 0 execution.native.application
      (runtime.application.afterPrivateWork who work execution).native.application := by
  induction work generalizing execution with
  | nil => exact .refl invariant
  | cons command rest ih =>
      have head := privateStep_progress inputs execution.native.application who command invariant
      exact head.trans (ih (runtime.application.afterPrivate execution who command) head.invariant)

/-- Arbitrarily much finite private work within a response consumes zero clock
ticks and preserves activation times of still-live events. -/
theorem responseStep_progress (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (who : Player) (execution next : runtime.application.PolicyExecution)
    (response : runtime.application.PlayerResponse)
    (invariant : execution.native.application.Invariant inputs)
    (reached : next ∈ (runtime.application.responseStep who execution response).support) :
    State.ServiceProgress inputs 0 execution.native.application next.native.application := by
  have work := runtime.afterPrivateWork_progress inputs who response.privateWork execution invariant
  exact work.trans (runtime.playerStep_progress inputs who _ next
    (response.network.toPlayerCommand runtime.application) work.invariant reached)

theorem responseInstructionStep_progress (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (execution next : runtime.application.PolicyExecution)
    (joint : Player → Option runtime.application.PlayerResponse)
    (invariant : execution.native.application.Invariant inputs)
    (reached : next ∈ (runtime.responseInstructionStep wire instruction execution joint).support) :
    State.ServiceProgress inputs instruction.ticks
      execution.native.application next.native.application := by
  cases instruction with
  | player who => exact runtime.responseStep_progress inputs who execution next _ invariant reached
  | wire | grant event | includeLatest event who | sample event | tick | expire event =>
      exact runtime.serviceStep_facts inputs (fun _ _ _ => FinDist.pure .wait)
        wire _ execution next invariant reached

theorem responseInstructionStep_native (runtime : EventGraphRuntime graph)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (execution next : runtime.application.PolicyExecution)
    (joint : Player → Option runtime.application.PlayerResponse)
    (reached : next ∈ (runtime.responseInstructionStep wire instruction execution joint).support) :
    ∃ actions, next.native ∈ (runtime.application.run actions execution.native).support := by
  cases instruction with
  | player who => exact runtime.application.responseStep_native_support who execution next _ reached
  | wire | grant event | includeLatest event who | sample event | tick | expire event =>
      obtain ⟨actions, _, member⟩ := runtime.serviceStep_native_support
        (fun _ _ _ => FinDist.pure .wait) wire _ execution next reached
      exact ⟨actions, member⟩

/-- Every continuation step retains the execution, even at an order-selection
boundary; it never reinitializes private inputs or the native state. -/
theorem responseTransition_native (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (before : ServiceControl runtime) (after : ResponseProtocolState runtime)
    (joint : Player → Option runtime.application.PlayerResponse)
    (reached : after ∈
      (runtime.responseTransition inputs roster reactionRounds wire order
        (some before) joint).support) :
    ∃ next : ServiceControl runtime, after = some next ∧
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
      obtain ⟨actions, native⟩ := runtime.responseInstructionStep_native wire instruction
        execution next joint supported
      exact ⟨_, rfl, actions, native⟩

/-- Fixed commitment meanings survive every legal service continuation step,
including responses that prepare, submit, or replay arbitrary other candidates. -/
theorem responseTransition_candidate_fixed (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (before after : ServiceControl runtime)
    (joint : Player → Option runtime.application.PlayerResponse)
    (candidate : Handle graph)
    (fixed : before.execution.native.application.candidates.lookup candidate ≠ .fresh)
    (reached : some after ∈
      (runtime.responseTransition inputs roster reactionRounds wire order
        (some before) joint).support) :
    after.execution.native.application.candidates.lookup candidate =
      before.execution.native.application.candidates.lookup candidate := by
  obtain ⟨next, same, actions, native⟩ := runtime.responseTransition_native inputs roster
    reactionRounds wire order before (some after) joint reached
  have equal := Option.some.inj same
  subst next
  exact runtime.run_candidate_fixed _ _ actions candidate fixed native

/-- Every finite continuation from an initialized native history expands to
an existing native execution. It cannot return to the setup position. -/
theorem response_reaches_native (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    {fuel : Nat}
    {history final : (runtime.responseProtocol inputs roster reactionRounds wire order).History}
    (path : (runtime.responseProtocol inputs roster reactionRounds wire order).ReachesWithin
      fuel history final)
    (before : ServiceControl runtime) (initialized : history.state = some before) :
    ∃ after : ServiceControl runtime, final.state = some after ∧
      ∃ actions, after.execution.native ∈
        (runtime.application.run actions before.execution.native).support := by
  induction path generalizing before with
  | refl fuel history => exact ⟨before, initialized, [], FinDist.mem_support_pure.mpr rfl⟩
  | @step fuel history final joint legal target realized rest ih =>
      have first : target ∈
          (runtime.responseTransition inputs roster reactionRounds wire order
            (some before) joint).support := by
        simpa only [responseProtocol, initialized] using realized
      obtain ⟨middle, middleEq, firstActions, firstRun⟩ := runtime.responseTransition_native
        inputs roster reactionRounds wire order before target joint first
      obtain ⟨after, afterEq, suffix, suffixRun⟩ := ih middle middleEq
      refine ⟨after, afterEq, firstActions ++ suffix, ?_⟩
      simp only [MessageApplication.run_append, FinDist.support_bind, Set.mem_iUnion]
      exact ⟨middle.execution.native, firstRun, suffixRun⟩

/-- Submission-time binding holds across arbitrary response-protocol paths,
independently of the chosen policy and of whether the prefix is a proper root. -/
theorem response_reaches_candidate_fixed (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    {fuel : Nat}
    {history final : (runtime.responseProtocol inputs roster reactionRounds wire order).History}
    (path : (runtime.responseProtocol inputs roster reactionRounds wire order).ReachesWithin
      fuel history final)
    (before after : ServiceControl runtime)
    (initialState : history.state = some before) (finalState : final.state = some after)
    (candidate : Handle graph)
    (fixed : before.execution.native.application.candidates.lookup candidate ≠ .fresh) :
    after.execution.native.application.candidates.lookup candidate =
      before.execution.native.application.candidates.lookup candidate := by
  obtain ⟨next, nextEq, actions, native⟩ := runtime.response_reaches_native inputs roster
    reactionRounds wire order path before initialState
  have same := Option.some.inj (finalState.symm.trans nextEq)
  subst next
  exact runtime.run_candidate_fixed _ _ actions candidate fixed native

/-- Every initialized legal response history has fresh, unused candidates,
including histories produced entirely by deviations. Setup is sampled once;
the proof retains the actual catalogue rather than resetting it at a root. -/
theorem response_history_freshCandidates (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    ∀ {state}
      (_trace : (runtime.responseProtocol inputs roster reactionRounds wire order).Trace state)
      (control : ServiceControl runtime), state = some control →
        control.execution.native.application.FreshCandidates
  | _, .start, _, initialized => by cases initialized
  | _, .extend (source := before) prior joint _ reached, control, initialized => by
      have priorFresh := runtime.response_history_freshCandidates inputs roster reactionRounds
        wire order prior
      have step : some control ∈
          (runtime.responseTransition inputs roster reactionRounds wire order
            before joint).support := by
        simpa only [responseProtocol, initialized] using reached
      cases before with
      | none =>
          simp only [responseTransition, FinDist.support_map, Set.mem_image] at step
          obtain ⟨input, _, same⟩ := step
          cases Option.some.inj same
          exact State.initial_freshCandidates input
      | some before =>
          obtain ⟨after, same, actions, native⟩ := runtime.responseTransition_native
            inputs roster reactionRounds wire order before (some control) joint step
          cases Option.some.inj same
          exact runtime.run_freshCandidates _ _ actions (priorFresh before rfl) native

end Vegas.EventGraphRuntime
