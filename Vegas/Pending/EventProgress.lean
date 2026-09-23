/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventInvariant

/-! # Application progress independent of the service driver

Completion is monotone, the logical clock has an explicit tick count, and
unfinished events retain their activation time. These facts compose across
command-based and reactive message protocols.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

namespace State

/-- Proved transition facts: completed events persist, time advances by the
specified number of ticks, and a live event never loses its original deadline. -/
structure ServiceProgress (inputs : graph.Inputs) (ticks : Nat)
    (before after : State graph) : Prop where
  invariant : after.Invariant inputs
  completed : before.config.cut.completed ⊆ after.config.cut.completed
  clock : after.clock = before.clock + ticks
  activated : ∀ event entered, before.activatedAt event = some entered →
    event ∉ after.config.cut.completed → after.activatedAt event = some entered

omit [DecidableEq Player] in
theorem ServiceProgress.refl {inputs : graph.Inputs} {state : State graph}
    (invariant : state.Invariant inputs) : ServiceProgress inputs 0 state state :=
  ⟨invariant, Finset.Subset.refl _, by omega, fun _ _ same _ => same⟩

omit [DecidableEq Player] in
theorem ServiceProgress.trans {inputs : graph.Inputs} {first second : Nat}
    {before middle after : State graph}
    (left : ServiceProgress inputs first before middle)
    (right : ServiceProgress inputs second middle after) :
    ServiceProgress inputs (first + second) before after := by
  refine ⟨right.invariant, left.completed.trans right.completed, ?_, ?_⟩
  · rw [right.clock, left.clock, Nat.add_assoc]
  · intro event entered activated unfinished
    exact right.activated event entered
      (left.activated event entered activated (fun done => unfinished (right.completed done)))
      unfinished

omit [DecidableEq Player] in
theorem ServiceProgress.ready_or_completed {inputs : graph.Inputs} {ticks : Nat}
    {before after : State graph} (progress : ServiceProgress inputs ticks before after)
    (event : graph.EventId) (ready : before.config.cut.Ready event) :
    event ∈ after.config.cut.completed ∨ after.config.cut.Ready event := by
  by_cases done : event ∈ after.config.cut.completed
  · exact Or.inl done
  · exact Or.inr ⟨done, ready.2.trans progress.completed⟩

end State

theorem privateStep_progress (inputs : graph.Inputs) (state : State graph)
    (who : Player) (command : PrivateCommand graph) (invariant : state.Invariant inputs) :
    State.ServiceProgress inputs 0 state (privateStep state who command) := by
  obtain ⟨config, clock, activated⟩ := privateStep_facts state who command
  refine ⟨privateStep_invariant state invariant who command, ?_, by simpa using clock, ?_⟩
  · rw [config]
  · intro event entered value _
    rw [activated]
    exact value

theorem handle_progress (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (state next : State graph)
    (message : Message Player (Payload graph)) (invariant : state.Invariant inputs)
    (accepted : handle runtime state message = some next) :
    State.ServiceProgress inputs 0 state next := by
  refine ⟨handle_invariant runtime state next message invariant accepted,
    handle_completed_subset runtime state next message accepted, ?_, ?_⟩
  · simpa using (handle_clock_activated runtime state next message accepted).1
  · exact handle_activatedAt_of_not_completed runtime state next message invariant accepted

omit [DecidableEq Player] in
/-- Sampling completes any ready chance event, independently of the service driver. -/
theorem environmentStep_sample_complete (runtime : EventGraphRuntime graph)
    (state next : State graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (chance : graph.actor? event = none)
    (supported : next ∈ (environmentStep runtime state (.executeSample event)).support) :
    event ∈ next.config.cut.completed := by
  cases view : nodeView graph event with
  | bind owner payload outputEq codeEq | resolve owner payload binding checks outputEq codeEq =>
      have ownerEq := congrArg EventGraph.EventCode.actor codeEq
      rw [EventGraph.EventCode.actor_cast outputEq (graph.nodes event)] at ownerEq
      change graph.actor? event = some owner at ownerEq
      simp only [chance] at ownerEq
      contradiction
  | sample payload law outputEq codeEq =>
      rw [environmentStep_executeSample_eq runtime state event ready
        payload law outputEq codeEq view, FinDist.support_map] at supported
      obtain ⟨config, step, same⟩ := supported
      have configEq := congrArg State.config same
      rw [← configEq, EventGraph.Config.step_cut _ _ _ _ _ step]
      exact Finset.mem_insert_self _ _

omit [DecidableEq Player] in
/-- Expiry completes a ready strategic event once its original deadline is due. -/
theorem environmentStep_expire_complete (runtime : EventGraphRuntime graph)
    (state next : State graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (strategic : (graph.actor? event).isSome = true)
    (entered : Nat) (activated : state.activatedAt event = some entered)
    (due : runtime.deadline event ≤ state.clock - entered)
    (supported : next ∈ (environmentStep runtime state (.expire event)).support) :
    event ∈ next.config.cut.completed := by
  cases view : nodeView graph event with
  | sample payload law outputEq codeEq =>
      have ownerEq := congrArg EventGraph.EventCode.actor codeEq
      rw [EventGraph.EventCode.actor_cast outputEq (graph.nodes event)] at ownerEq
      change graph.actor? event = none at ownerEq
      simp [ownerEq] at strategic
  | bind owner payload outputEq codeEq =>
      rw [environmentStep_expire_bind_eq runtime state event ready
        entered activated due owner payload outputEq codeEq view,
        FinDist.mem_support_pure] at supported
      rw [supported]
      exact Finset.mem_insert_self _ _
  | resolve owner payload binding checks outputEq codeEq =>
      rw [environmentStep_expire_resolve_eq runtime state event ready
        entered activated due owner payload binding checks outputEq codeEq view,
        FinDist.mem_support_pure] at supported
      rw [supported]
      exact Finset.mem_insert_self _ _

end Vegas.EventGraphRuntime
