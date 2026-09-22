/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ResponseProtocolPolicy
import Vegas.Pending.ResponseProtocolTermination
import GameTheoryExtensions.Protocol.SingleMover

/-! # The response protocol executes native policy invocations

At a player site the protocol's behavioral joint law executes exactly the
native response policy on its actual arguments. The same law holds at every
legal prefix. Other steps execute setup or the fixed service policies.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Protocol GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Native policy evaluation for one service opportunity. This is a transition
kernel, not another recursive service evaluator. -/
def responseControlStep (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.ResponsePolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    ResponseProtocolState runtime → FinDist (ResponseProtocolState runtime)
  | some ⟨epochs, .player who :: rest, execution⟩ =>
      (runtime.application.invokeResponse who (players who) execution).map fun next =>
        some ⟨epochs, rest, next⟩
  | state =>
      runtime.responseTransition inputs roster reactionRounds wire order state (fun _ => none)

theorem responseControlStep_eq_of_marginals (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.ResponsePolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (state : ResponseProtocolState runtime)
    (joint : FinDist (Player → Option runtime.application.PlayerResponse))
    (marginal : ∀ who, joint.map (fun actions => actions who) =
      (runtime.encodeResponsePolicy (players who) (runtime.responseObserve who state)).map
        Subtype.val) :
    joint.bind (runtime.responseTransition inputs roster reactionRounds wire order state) =
      runtime.responseControlStep inputs roster reactionRounds players wire order state := by
  change (joint.bind fun actions =>
    runtime.responseTransition inputs roster reactionRounds wire order state actions) = _
  cases state with
  | none => simp [responseControlStep, responseTransition, FinDist.bind_const]
  | some control =>
      rcases control with ⟨epochs, plan, execution⟩
      cases plan with
      | nil =>
          cases epochs <;> simp [responseControlStep, responseTransition, FinDist.bind_const]
      | cons instruction rest =>
          cases instruction with
          | player who =>
              have law := marginal who
              rw [responseObserve_player, encodeResponsePolicy_some] at law
              have selected := congrArg (fun law => law.bind (fun action =>
                (runtime.application.responseStep who execution
                  (action.getD runtime.idleResponse)).map
                    (fun next => some (ServiceControl.mk epochs rest next)))) law
              simpa only [FinDist.bind_map, Option.getD_some, responseTransition,
                responseInstructionStep, responseControlStep, MessageApplication.invokeResponse,
                FinDist.map_bind] using selected
          | wire | grant event | includeLatest event who | sample event | tick | expire event =>
              simp [responseControlStep, responseTransition, responseInstructionStep,
                FinDist.bind_const]

/-- Exact native transition law under a behavioral profile, at any legal
history. The policies receive no argument derived from the hidden service cursor. -/
theorem response_behavioral_step (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.ResponsePolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (history : (runtime.responseProtocol inputs roster reactionRounds wire order).History)
    (running : ¬ runtime.responseTerminal history.state) :
    ((runtime.responseInformation inputs roster reactionRounds wire order).singleMoverJoint
      (runtime.response_singleMover inputs roster reactionRounds wire order)
      (fun who => runtime.encodeResponsePolicy (players who)) history running).bind
        ((runtime.responseProtocol inputs roster reactionRounds wire order).step history.state) =
      runtime.responseControlStep inputs roster reactionRounds players wire order
        history.state := by
  let law := (runtime.responseInformation inputs roster reactionRounds wire order).singleMoverJoint
    (runtime.response_singleMover inputs roster reactionRounds wire order)
    (fun who => runtime.encodeResponsePolicy (players who)) history running
  have marginal (who : Player) :
      (law.map Subtype.val).map (fun actions => actions who) =
        (runtime.encodeResponsePolicy (players who)
          (runtime.responseObserve who history.state)).map Subtype.val := by
    rw [FinDist.map_comp]
    change law.map (fun actions => actions.1 who) = _
    rw [InformationModel.singleMoverJoint_marginal]
    change (runtime.encodeResponsePolicy (players who)
      ((runtime.responseSignals inputs roster reactionRounds wire order).infoOf who
        history.trace)).map Subtype.val = _
    rw [response_info]
  have lawEq := runtime.responseControlStep_eq_of_marginals inputs roster reactionRounds
    players wire order history.state (law.map Subtype.val) marginal
  rw [FinDist.bind_map] at lawEq
  exact lawEq

/-- The certified fuel always reaches a terminal service control, including
when the supplied history lies outside the profile's support. -/
theorem response_run_terminal (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (profile : ∀ who,
      (runtime.responseInformation inputs roster reactionRounds wire order).BehavioralPolicy who)
    (history final : (runtime.responseProtocol inputs roster reactionRounds wire order).History)
    (reached : final ∈
      (InformationModel.runSingleMoverBehavioralFrom
        (runtime.responseInformation inputs roster reactionRounds wire order)
        (runtime.response_singleMover inputs roster reactionRounds wire order) profile
        (runtime.responseRemaining roster reactionRounds history.state) history).support) :
    runtime.responseTerminal final.state := by
  rcases ExecutionProtocol.runRandomizedFor_terminal_or_length
      (E := runtime.responseProtocol inputs roster reactionRounds wire order)
      _ _ _ _ reached with stopped | consumed
  · exact stopped
  · have before := runtime.response_history_length inputs roster reactionRounds wire order
      history.trace
    have after := runtime.response_history_length inputs roster reactionRounds wire order
      final.trace
    exact (runtime.responseRemaining_zero roster reactionRounds final.state).mp (by omega)

end Vegas.EventGraphRuntime
