/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.NativeLocality
import GameTheoryExtensions.Math.Probability.FinDist

/-! # One player response with a fixed number of packet opportunities

A response is a list of actions chosen together. Executing it retains every
constituent action and its before-view in private recall. It invokes no wire,
clock, chance, or other player between those actions.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Protocol GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

abbrev PlayerResponse (graph : Vegas.EventGraph Player L) (count : Nat) :=
  {actions : List (PlayerAction graph) // actions.length = count}

abbrev NativeResponsePolicy (graph : Vegas.EventGraph Player L) (count : Nat) :=
  NativeInput graph → FinDist (PlayerResponse graph count)

def takeActions (runtime : EventGraphRuntime graph) (who : Player)
    (execution : NativeExecution runtime) (actions : List (PlayerAction graph)) :
    NativeExecution runtime := actions.foldl (runtime.takeAction who) execution

theorem takeActions_append (runtime : EventGraphRuntime graph) (who : Player)
    (execution : NativeExecution runtime) (first second : List (PlayerAction graph)) :
    runtime.takeActions who execution (first ++ second) =
      runtime.takeActions who (runtime.takeActions who execution first) second :=
  List.foldl_append

theorem takeActions_counters (runtime : EventGraphRuntime graph) (who : Player)
    (execution : NativeExecution runtime) (actions : List (PlayerAction graph))
    (counters : execution.Counters runtime) :
    (runtime.takeActions who execution actions).Counters runtime := by
  induction actions generalizing execution with
  | nil => exact counters
  | cons action rest ih =>
      exact ih (runtime.takeAction who execution action)
        (runtime.takeAction_counters who execution action counters)

theorem takeActions_other_input (runtime : EventGraphRuntime graph) (actor observer : Player)
    (different : observer ≠ actor) (execution : NativeExecution runtime)
    (actions : List (PlayerAction graph)) :
    runtime.nativeInput observer (runtime.takeActions actor execution actions) =
      runtime.nativeInput observer execution := by
  induction actions generalizing execution with
  | nil => rfl
  | cons action rest ih =>
      exact (ih (runtime.takeAction actor execution action)).trans
        (runtime.takeAction_other_input actor observer different execution action)

theorem takeActions_environmentHistory (runtime : EventGraphRuntime graph) (who : Player)
    (execution : NativeExecution runtime) (actions : List (PlayerAction graph)) :
    (runtime.takeActions who execution actions).environmentHistory =
      execution.environmentHistory := by
  induction actions generalizing execution with
  | nil => rfl
  | cons action rest ih => exact ih (runtime.takeAction who execution action)

theorem takeActions_history_length (runtime : EventGraphRuntime graph) (who : Player)
    (execution : NativeExecution runtime) (actions : List (PlayerAction graph)) :
    ((runtime.takeActions who execution actions).principalHistory who).length =
      (execution.principalHistory who).length + actions.length := by
  induction actions generalizing execution with
  | nil => simp only [takeActions, List.foldl_nil, List.length_nil, Nat.add_zero]
  | cons action rest ih =>
      change ((runtime.takeActions who
        (runtime.takeAction who execution action) rest).principalHistory who).length = _
      rw [ih, runtime.takeAction_history_self]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

/-- The kernel for successive invocations of the same policy. -/
def invokeNativeFor (runtime : EventGraphRuntime graph) (who : Player)
    (policy : NativePolicy graph) :
    Nat → NativeExecution runtime → FinDist (NativeExecution runtime)
  | 0, execution => FinDist.pure execution
  | count + 1, execution => (runtime.invokeNative who policy execution).bind
      (runtime.invokeNativeFor who policy count)

def compileResponse (runtime : EventGraphRuntime graph) (who : Player)
    (policy : NativePolicy graph) (count : Nat) : NativeResponsePolicy graph count := fun input =>
  ((runtime.nativeLocalResponse who).transcript (Function.uncurry policy) count input).toSubtype
    ((runtime.nativeLocalResponse who).transcript_length (Function.uncurry policy) count input)

def invokeResponse (runtime : EventGraphRuntime graph) (who : Player) {count : Nat}
    (policy : NativeResponsePolicy graph count) (execution : NativeExecution runtime) :
    FinDist (NativeExecution runtime) :=
  (policy (runtime.nativeInput who execution)).map
    (fun response => runtime.takeActions who execution response.1)

private theorem nativeTranscript_law (runtime : EventGraphRuntime graph) (who : Player)
    (policy : NativePolicy graph) (count : Nat) (execution : NativeExecution runtime)
    (counters : execution.Counters runtime) :
    ((runtime.nativeLocalResponse who).transcript (Function.uncurry policy) count
      (runtime.nativeInput who execution)).map (runtime.takeActions who execution) =
        runtime.invokeNativeFor who policy count execution := by
  induction count generalizing execution with
  | zero => simp only [LocalResponse.transcript, FinDist.map_pure, takeActions,
      List.foldl_nil, invokeNativeFor]
  | succ count ih =>
      simp only [LocalResponse.transcript, FinDist.map_bind, FinDist.map_comp,
        invokeNativeFor, invokeNative, actionStep, FinDist.bind_bind, FinDist.pure_bind]
      apply FinDist.bind_congr
      intro action _
      change (((runtime.nativeLocalResponse who).transcript (Function.uncurry policy) count
        ((runtime.nativeInput who execution).afterAction action)).map
          (runtime.takeActions who (runtime.takeAction who execution action))) = _
      rw [← runtime.nativeInput_takeAction who execution action counters]
      exact ih _ (runtime.takeAction_counters who execution action counters)

/-- The same complete endpoint law, uniformly over hidden states, arbitrary
policies, and all legal prefixes. The batch sampler receives only own input. -/
theorem compileResponse_law (runtime : EventGraphRuntime graph) (who : Player)
    (policy : NativePolicy graph) (count : Nat) (execution : NativeExecution runtime)
    (counters : execution.Counters runtime) :
    runtime.invokeResponse who (runtime.compileResponse who policy count) execution =
      runtime.invokeNativeFor who policy count execution := by
  rw [invokeResponse, compileResponse, FinDist.map_toSubtype]
  exact runtime.nativeTranscript_law who policy count execution counters

/-- Every subsequent wire, player, or service continuation has the same law. -/
theorem compileResponse_continuation {Result : Type*} (runtime : EventGraphRuntime graph)
    (who : Player) (policy : NativePolicy graph) (count : Nat)
    (execution : NativeExecution runtime) (counters : execution.Counters runtime)
    (continuation : NativeExecution runtime → FinDist Result) :
    (runtime.invokeResponse who (runtime.compileResponse who policy count)
      execution).bind continuation =
      (runtime.invokeNativeFor who policy count execution).bind continuation := by
  rw [runtime.compileResponse_law who policy count execution counters]

end Vegas.EventGraphRuntime
