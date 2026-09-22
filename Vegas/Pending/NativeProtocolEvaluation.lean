/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.NativeProtocolPolicy
import Vegas.Pending.NativeProtocolTermination
import GameTheoryExtensions.Protocol.SingleMover
import GameTheoryExtensions.Protocol.StateKernel

/-! # The native protocol executes native policy invocations

At a player site the protocol's behavioral joint law executes exactly the
native policy on its actual arguments. The same law holds at every
legal prefix. Other steps execute setup or the fixed service policies.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Protocol GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Native policy evaluation for one service opportunity. This is a transition
kernel, not another recursive service evaluator. -/
def nativeControlStep (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → NativePolicy graph)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    NativeProtocolState runtime → FinDist (NativeProtocolState runtime)
  | some ⟨epochs, .player who :: rest, execution⟩ =>
      (runtime.invokeNative who (players who) execution).map fun next =>
        some ⟨epochs, rest, next⟩
  | state =>
      runtime.nativeTransition inputs roster reactionRounds wire order state (fun _ => none)

theorem nativeControlStep_eq_of_marginals (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → NativePolicy graph)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (state : NativeProtocolState runtime)
    (joint : FinDist (Player → Option (PlayerAction graph)))
    (marginal : ∀ who, joint.map (fun actions => actions who) =
      (encodeNativePolicy (players who) (runtime.nativeObserve who state)).map
        Subtype.val) :
    joint.bind (runtime.nativeTransition inputs roster reactionRounds wire order state) =
      runtime.nativeControlStep inputs roster reactionRounds players wire order state := by
  change (joint.bind fun actions =>
    runtime.nativeTransition inputs roster reactionRounds wire order state actions) = _
  cases state with
  | none => simp [nativeControlStep, nativeTransition, FinDist.bind_const]
  | some control =>
      rcases control with ⟨epochs, plan, execution⟩
      cases plan with
      | nil =>
          cases epochs <;> simp [nativeControlStep, nativeTransition, FinDist.bind_const]
      | cons instruction rest =>
          cases instruction with
          | player who =>
              have law := marginal who
              rw [nativeObserve_player, encodeNativePolicy_some] at law
              have selected := congrArg (fun law => law.bind (fun action =>
                (runtime.actionStep who execution
                  (action.getD PlayerAction.wait)).map
                    (fun next => some (NativeControl.mk epochs rest next)))) law
              simpa only [FinDist.bind_map, Option.getD_some, nativeTransition,
                nativeInstructionStep, nativeControlStep, invokeNative,
                FinDist.map_bind] using selected
          | wire | grant event | includeLatest event who | sample event | tick | expire event =>
              simp [nativeControlStep, nativeTransition, nativeInstructionStep,
                FinDist.bind_const]

/-- Exact native transition law under a behavioral profile, at any legal
history. The policies receive no argument derived from the hidden service cursor. -/
theorem native_behavioral_step (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → NativePolicy graph)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (history : (runtime.nativeProtocol inputs roster reactionRounds wire order).History)
    (running : ¬ runtime.nativeTerminal history.state) :
    ((runtime.nativeInformation inputs roster reactionRounds wire order).singleMoverJoint
      (runtime.native_singleMover inputs roster reactionRounds wire order)
      (fun who => encodeNativePolicy (players who)) history running).bind
        ((runtime.nativeProtocol inputs roster reactionRounds wire order).step history.state) =
      runtime.nativeControlStep inputs roster reactionRounds players wire order
        history.state := by
  let law := (runtime.nativeInformation inputs roster reactionRounds wire order).singleMoverJoint
    (runtime.native_singleMover inputs roster reactionRounds wire order)
    (fun who => encodeNativePolicy (players who)) history running
  have marginal (who : Player) :
      (law.map Subtype.val).map (fun actions => actions who) =
        (encodeNativePolicy (players who)
          (runtime.nativeObserve who history.state)).map Subtype.val := by
    rw [FinDist.map_comp]
    change law.map (fun actions => actions.1 who) = _
    rw [InformationModel.singleMoverJoint_marginal]
    change (encodeNativePolicy (players who)
      ((runtime.nativeSignals inputs roster reactionRounds wire order).infoOf who
        history.trace)).map Subtype.val = _
    rw [native_info]
  have lawEq := runtime.nativeControlStep_eq_of_marginals inputs roster reactionRounds
    players wire order history.state (law.map Subtype.val) marginal
  rw [FinDist.bind_map] at lawEq
  exact lawEq

/-- Forgetting the canonical trace gives ordinary iteration of the native
state kernel. The state still retains the actual private and environment
recall consulted by the policies. -/
theorem native_run_map_state (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → NativePolicy graph)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (fuel : Nat)
    (history : (runtime.nativeProtocol inputs roster reactionRounds wire order).History) :
    (InformationModel.runSingleMoverBehavioralFrom
      (runtime.nativeInformation inputs roster reactionRounds wire order)
      (runtime.native_singleMover inputs roster reactionRounds wire order)
      (fun who => encodeNativePolicy (players who)) fuel history).map
        ExecutionProtocol.History.state =
      (fun law => law.bind (runtime.nativeControlStep inputs roster reactionRounds players wire
        order))^[fuel] (FinDist.pure history.state) := by
  apply ExecutionProtocol.runRandomizedFor_map_state
  · intro state stopped
    cases state with
    | none => exact stopped.elim
    | some control =>
        rcases control with ⟨epochs, plan, execution⟩
        rcases stopped with ⟨rfl, rfl⟩
        rfl
  · intro current running
    exact runtime.native_behavioral_step inputs roster reactionRounds players wire order
      current running

/-- The certified fuel always reaches a terminal service control, including
when the supplied history lies outside the profile's support. -/
theorem native_run_terminal (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (profile : ∀ who,
      (runtime.nativeInformation inputs roster reactionRounds wire order).BehavioralPolicy who)
    (history final : (runtime.nativeProtocol inputs roster reactionRounds wire order).History)
    (reached : final ∈
      (InformationModel.runSingleMoverBehavioralFrom
        (runtime.nativeInformation inputs roster reactionRounds wire order)
        (runtime.native_singleMover inputs roster reactionRounds wire order) profile
        (runtime.nativeRemaining roster reactionRounds history.state) history).support) :
    runtime.nativeTerminal final.state := by
  rcases ExecutionProtocol.runRandomizedFor_terminal_or_length
      (E := runtime.nativeProtocol inputs roster reactionRounds wire order)
      _ _ _ _ reached with stopped | consumed
  · exact stopped
  · have before := runtime.native_history_length inputs roster reactionRounds wire order
      history.trace
    have after := runtime.native_history_length inputs roster reactionRounds wire order
      final.trace
    exact (runtime.nativeRemaining_zero roster reactionRounds final.state).mp (by omega)

end Vegas.EventGraphRuntime
