/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ResponseProtocolRefinement

/-! # A concrete response-capacity certificate

With an empty reaction roster, every player response has exactly three slots.
Wire opportunities, inclusion, grants, sampling, clocks, and expiry remain in
the service. The constant budget is adequate at every legal history, so the
canonical information model uses precisely the original native input.

For a nonempty roster, initial owner responses and later reactions may have
different lengths. Their capacity must be recovered from own recall; this
module makes no certificate claim for that case.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Protocol GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

private inductive ThreeCallPlan : List (ServiceInstruction graph) → Prop
  | nil : ThreeCallPlan []
  | environment {instruction rest} : instruction.isEnvironment = true →
      ThreeCallPlan rest → ThreeCallPlan (instruction :: rest)
  | response (who : Player) {instruction rest} : instruction.isEnvironment = true →
      ThreeCallPlan rest → ThreeCallPlan
        (.player who :: .player who :: .player who :: instruction :: rest)

omit [DecidableEq Player] in
private theorem ThreeCallPlan.append {first second : List (ServiceInstruction graph)}
    (left : ThreeCallPlan first) (right : ThreeCallPlan second) :
    ThreeCallPlan (first ++ second) := by
  induction left with
  | nil => exact right
  | environment allowed _ ih => exact .environment allowed ih
  | response who allowed _ ih => exact .response who allowed ih

omit [DecidableEq Player] in
private theorem ThreeCallPlan.of_environment (plan : List (ServiceInstruction graph))
    (allowed : ∀ instruction ∈ plan, instruction.isEnvironment = true) : ThreeCallPlan plan := by
  induction plan with
  | nil => exact .nil
  | cons instruction rest ih =>
      exact .environment (allowed instruction (List.mem_cons_self ..))
        (ih fun step member => allowed step (List.mem_cons_of_mem _ member))

private theorem ThreeCallPlan.consume {plan : List (ServiceInstruction graph)}
    (valid : ThreeCallPlan plan) :
    match plan with
    | [] => True
    | .player who :: rest => responseLength who (.player who :: rest) = 3 ∧
        ThreeCallPlan ((.player who :: rest).drop 3)
    | _ :: rest => ThreeCallPlan rest := by
  cases valid with
  | nil => trivial
  | @environment instruction rest allowed valid =>
      cases instruction <;> first | exact valid | simp [ServiceInstruction.isEnvironment] at allowed
  | @response who instruction rest allowed valid =>
      have stops : responseLength who (instruction :: rest) = 0 := by
        cases instruction <;> first | rfl | simp [ServiceInstruction.isEnvironment] at allowed
      exact ⟨by simp [responseLength, stops], .environment allowed valid⟩

omit [DecidableEq Player] in
private theorem eventServicePlan_three (rounds : Nat) (event : graph.EventId) :
    ThreeCallPlan (eventServicePlan (graph := graph) [] rounds event) := by
  cases actor : graph.actor? event with
  | none =>
      simp only [eventServicePlan, actor, List.append_nil, List.singleton_append]
      exact .environment rfl (.environment rfl .nil)
  | some who =>
      let tail : List (ServiceInstruction graph) :=
        (List.replicate rounds [.wire]).flatten ++ [.includeLatest event who, .sample event]
      have allEnvironment : ∀ instruction ∈ tail, instruction.isEnvironment = true := by
        intro instruction member
        simp only [tail, List.mem_append, List.mem_flatten, List.mem_replicate,
          List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with ⟨part, ⟨_, rfl⟩, member⟩ | rfl | rfl
        · have same : instruction = .wire := by simpa using member
          rw [same]
          rfl
        · rfl
        · rfl
      have nonempty : tail ≠ [] := by simp [tail]
      have normalized : eventServicePlan (graph := graph) [] rounds event =
          .grant event :: .player who :: .player who :: .player who :: tail := by
        simp [eventServicePlan, actor, tail, List.replicate_succ, List.append_assoc]
      rw [normalized]
      cases tailEq : tail with
      | nil => exact (nonempty tailEq).elim
      | cons instruction rest =>
          rw [tailEq] at allEnvironment
          exact .environment rfl (.response who
            (allEnvironment instruction (List.mem_cons_self ..))
            (ThreeCallPlan.of_environment rest fun step member =>
              allEnvironment step (List.mem_cons_of_mem _ member)))

omit [DecidableEq Player] in
private theorem epochPlan_three (chosen : ServiceOrder graph) (rounds : Nat) :
    ThreeCallPlan (epochPlan chosen [] rounds) := by
  have events : ∀ selected : List graph.EventId,
      ThreeCallPlan (selected.flatMap (eventServicePlan [] rounds)) := by
    intro selected
    induction selected with
    | nil => exact .nil
    | cons event rest ih => exact (eventServicePlan_three rounds event).append ih
  rw [epochPlan, List.append_assoc]
  apply (events chosen.val).append
  apply ThreeCallPlan.of_environment
  intro instruction member
  simp only [List.mem_append, List.mem_singleton, List.mem_map] at member
  rcases member with rfl | ⟨event, _, rfl⟩ <;> rfl

private def responsePlanThree (runtime : EventGraphRuntime graph) :
    NativeProtocolState runtime → Prop
  | none => True
  | some control => ThreeCallPlan control.plan

private theorem responsePlanThree_step (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (rounds : Nat) (wire : runtime.application.WirePolicy)
    (order : runtime.ServiceOrderPolicy) (before after : NativeProtocolState runtime)
    (joint : Player → Option (List (PlayerAction graph))) (valid : responsePlanThree runtime before)
    (reached : after ∈
      (runtime.responseTransition inputs [] rounds wire order before joint).support) :
    responsePlanThree runtime after := by
  cases before with
  | none =>
      obtain ⟨input, _, rfl⟩ := FinDist.support_map .. ▸ reached
      exact .nil
  | some control =>
      rcases control with ⟨epochs, plan, execution⟩
      cases plan with
      | nil =>
          cases epochs with
          | zero => cases FinDist.mem_support_pure.mp reached; exact valid
          | succ epochs =>
              obtain ⟨chosen, _, rfl⟩ := FinDist.support_map .. ▸ reached
              exact epochPlan_three chosen rounds
      | cons instruction rest =>
          have consumed := ThreeCallPlan.consume valid
          cases instruction with
          | player who =>
              cases FinDist.mem_support_pure.mp reached
              change ThreeCallPlan ((ServiceInstruction.player who :: rest).drop _)
              rw [consumed.1]
              exact consumed.2
          | wire | grant event | includeLatest event owner | sample event | tick | expire event =>
              obtain ⟨next, _, rfl⟩ := FinDist.support_map .. ▸ reached
              exact consumed

private theorem response_history_plan_three (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (rounds : Nat) (wire : runtime.application.WirePolicy)
    (order : runtime.ServiceOrderPolicy) :
    ∀ {state} (_trace : (runtime.responseProtocol inputs [] rounds wire order).Trace state),
      responsePlanThree runtime state
  | _, .start => trivial
  | _, .extend prior joint _ reached =>
      responsePlanThree_step runtime inputs rounds wire order _ _ joint
        (response_history_plan_three runtime inputs rounds wire order prior) reached

/-- No arity observation is added: every response in this service class has
the same public constant capacity, independently of all private and wire state. -/
theorem responseBudget_empty_roster (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (rounds : Nat) (wire : runtime.application.WirePolicy)
    (order : runtime.ServiceOrderPolicy) :
    runtime.ResponseBudgetAdequate inputs [] rounds wire order (fun _ _ => 3) := by
  intro history who input observed
  have active : runtime.nativeActor history.state = some who :=
    (runtime.nativeObserve_isSome who history.state).mp (by rw [observed]; rfl)
  have valid := response_history_plan_three runtime inputs rounds wire order history.trace
  cases stateEq : history.state with
  | none => simp [stateEq, nativeActor] at active
  | some control =>
      rcases control with ⟨epochs, plan, execution⟩
      cases plan with
      | nil => simp [stateEq, nativeActor] at active
      | cons instruction rest =>
          cases instruction with
          | player owner =>
              rw [stateEq] at valid
              have count := (ThreeCallPlan.consume valid).1
              simpa only [stateEq, responseCount] using count.symm
          | wire | grant event | includeLatest event owner | sample event | tick | expire event =>
              simp [stateEq, nativeActor] at active

end Vegas.EventGraphRuntime

-- OPEN OBLIGATION: Response budgets for nonempty reaction rosters
-- Recover the initial three owner slots and later roster-run lengths from own
-- recall and the observed grant/clock. Prove adequacy at all legal histories,
-- including repeated roster entries, without exposing the hidden service suffix.
