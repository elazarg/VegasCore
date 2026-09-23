/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.NativeResponseSampling
import Vegas.Pending.ResponseProtocolRefinement

/-! # Uniform native policies at every response history

At every initialized coalesced history each player's recall contains complete
responses. This holds for arbitrary legal actions and supported environment
choices, not just along the translated profile. A playerwise policy map can
therefore reconstruct and sample the right response at every such entry.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def responseBoundaries (runtime : EventGraphRuntime graph)
    (budget : Player → NativeInput graph → Nat) : NativeProtocolState runtime → Prop
  | none => True
  | some control => ∀ who, responseRecall (budget who)
      (control.execution.principalHistory who) = none

/-- A playerwise map into response strategies. The sampler learns the capacity
from the same input supplied to the original native policy. -/
def coalesceNativePolicy (runtime : EventGraphRuntime graph) (who : Player)
    (budget : NativeInput graph → Nat) (policy : NativePolicy graph) : ResponsePolicy budget :=
  fun input => runtime.compileResponse who policy (budget input) input

variable (runtime : EventGraphRuntime graph)
  (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
  (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
  (budget : Player → NativeInput graph → Nat)
  (adequate : runtime.ResponseBudgetAdequate inputs roster reactionRounds wire order budget)

include adequate

private theorem responseBoundaries_step
    (history : (runtime.responseProtocol inputs roster reactionRounds wire order).History)
    (valid : runtime.responseBoundaries budget history.state)
    (joint : Player → Option (List (PlayerAction graph)))
    (legal : (runtime.responseProtocol inputs roster reactionRounds wire order).Legal
      history.state joint)
    (after : NativeProtocolState runtime)
    (reached : after ∈ (runtime.responseTransition inputs roster reactionRounds wire order
      history.state joint).support) : runtime.responseBoundaries budget after := by
  cases stateEq : history.state with
  | none =>
      rw [stateEq] at reached
      obtain ⟨input, _, rfl⟩ := FinDist.support_map .. ▸ reached
      exact fun _ => rfl
  | some control =>
      rcases control with ⟨epochs, plan, execution⟩
      rw [stateEq] at valid reached
      cases plan with
      | nil =>
          cases epochs with
          | zero => cases FinDist.mem_support_pure.mp reached; exact valid
          | succ epochs =>
              obtain ⟨chosen, _, rfl⟩ := FinDist.support_map .. ▸ reached
              exact valid
      | cons instruction rest =>
          cases instruction with
          | player who =>
              have active :
                  (runtime.responseProtocol inputs roster reactionRounds wire order).active
                    history.state who := by rw [stateEq]; rfl
              obtain ⟨actions, selected⟩ := LegalOption.exists_eq_some_of_active (joint who)
                (ExecutionProtocol.legalOption_of_legal legal who) active
              have length : actions.length = responseLength who (.player who :: rest) := by
                have available := legal.2 who
                rw [selected] at available
                simpa only [responseProtocol, Set.mem_ofPred_eq, stateEq, responseCount]
                  using available.2
              have observed : runtime.nativeObserve who history.state =
                  some (runtime.nativeInput who execution) := by
                rw [stateEq]
                simp only [nativeObserve, nativeActor, ↓reduceIte, nativeInput]
              have count := adequate history who (runtime.nativeInput who execution) observed
              rw [stateEq] at count
              change budget who (runtime.nativeInput who execution) =
                responseLength who (.player who :: rest) at count
              simp only [responseTransition, selected, Option.getD_some,
                FinDist.mem_support_pure] at reached
              subst after
              intro observer
              by_cases same : observer = who
              · subst observer
                exact runtime.responseRecall_takeActions who (budget who) execution actions
                  (valid who) (length.trans count.symm)
              · have recall := congrArg Prod.fst
                  (runtime.takeActions_other_input who observer same execution actions)
                change responseRecall (budget observer)
                  ((runtime.takeActions who execution actions).principalHistory observer) = none
                rw [show (runtime.takeActions who execution actions).principalHistory observer =
                  execution.principalHistory observer from recall]
                exact valid observer
          | wire | grant event | includeLatest event owner | sample event | tick | expire event =>
              obtain ⟨next, supported, rfl⟩ := FinDist.support_map .. ▸ reached
              obtain ⟨next, _, rfl⟩ := FinDist.support_map .. ▸ supported
              exact valid

/-- Every legal response history has completed recall batches for every
player. The quantifier covers arbitrary off-path responses and replacements. -/
theorem response_history_boundaries :
    ∀ {state}
      (_trace : (runtime.responseProtocol inputs roster reactionRounds wire order).Trace state),
      runtime.responseBoundaries budget state
  | _, .start => trivial
  | _, .extend prior joint legal reached =>
      runtime.responseBoundaries_step inputs roster reactionRounds wire order budget adequate
        ⟨_, prior⟩ (response_history_boundaries prior) joint legal _ reached

/-- A uniform policy realization at every legal response entry. The policy
depends only on this player's strategy and budget, and works after any deviation. -/
theorem expandResponsePolicy_history_law
    (history : (runtime.responseProtocol inputs roster reactionRounds wire order).History)
    (control : NativeControl runtime) (stateEq : history.state = some control)
    (who : Player) (active : runtime.nativeActor history.state = some who)
    (policy : ResponsePolicy (budget who)) :
    runtime.invokeNativeFor who (expandResponsePolicy (budget who) policy)
        (runtime.responseCount history.state) control.execution =
      (policy (runtime.nativeInput who control.execution)).map
        (fun response => runtime.takeActions who control.execution response.1) := by
  have boundaries := runtime.response_history_boundaries inputs roster reactionRounds wire order
    budget adequate history.trace
  rw [stateEq] at boundaries
  have observed : runtime.nativeObserve who history.state =
      some (runtime.nativeInput who control.execution) := by
    rw [stateEq] at active ⊢
    simp only [nativeObserve, active, ↓reduceIte, nativeInput]
  rw [← adequate history who (runtime.nativeInput who control.execution) observed]
  exact runtime.expandResponsePolicy_law who (budget who) policy control.execution (boundaries who)

/-- Every invocation policy has a response strategy with the same complete
endpoint law at every legal response entry, uniformly over all hidden states. -/
theorem coalesceNativePolicy_history_law
    (history : (runtime.responseProtocol inputs roster reactionRounds wire order).History)
    (control : NativeControl runtime) (stateEq : history.state = some control)
    (who : Player) (active : runtime.nativeActor history.state = some who)
    (policy : NativePolicy graph) :
    (runtime.coalesceNativePolicy who (budget who) policy
      (runtime.nativeInput who control.execution)).map
        (fun response => runtime.takeActions who control.execution response.1) =
      runtime.invokeNativeFor who policy (runtime.responseCount history.state)
        control.execution := by
  have counters := runtime.response_history_counters inputs roster reactionRounds wire order
    history.trace
  rw [stateEq] at counters
  have observed : runtime.nativeObserve who history.state =
      some (runtime.nativeInput who control.execution) := by
    rw [stateEq] at active ⊢
    simp only [nativeObserve, active, ↓reduceIte, nativeInput]
  rw [← adequate history who (runtime.nativeInput who control.execution) observed]
  exact runtime.compileResponse_law who policy _ control.execution counters

end Vegas.EventGraphRuntime
