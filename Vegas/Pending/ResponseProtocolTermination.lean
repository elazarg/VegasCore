/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ResponseProtocol
import GameTheory.Protocol.Backward

/-! # Bounded atomic-response service

The rank counts service instructions and order selections. Private commands
inside a response do not consume service instructions or advance the clock.
Every legal protocol transition consumes one unit, independently of its policy.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def responseRemaining (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat) : ResponseProtocolState runtime → Nat
  | none => runtime.serviceEpochs * (runtime.epochInstructionCount roster reactionRounds + 1) + 1
  | some control => control.plan.length +
      control.epochs * (runtime.epochInstructionCount roster reactionRounds + 1)

theorem responseRemaining_zero (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat) (state : ResponseProtocolState runtime) :
    runtime.responseRemaining roster reactionRounds state = 0 ↔ runtime.responseTerminal state := by
  cases state with
  | none => simp [responseRemaining, responseTerminal]
  | some control =>
      simp [responseRemaining, responseTerminal, ServiceControl.Terminal, and_comm]

theorem responseRemaining_step (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (before after : ResponseProtocolState runtime)
    (joint : Player → Option runtime.application.PlayerResponse)
    (running : ¬ runtime.responseTerminal before)
    (reached : after ∈
      (runtime.responseTransition inputs roster reactionRounds wire order before joint).support) :
    runtime.responseRemaining roster reactionRounds after + 1 =
      runtime.responseRemaining roster reactionRounds before := by
  cases before with
  | none =>
      obtain ⟨input, _, rfl⟩ := FinDist.support_map .. ▸ reached
      simp [responseRemaining]
  | some control =>
      rcases control with ⟨epochs, plan, execution⟩
      cases plan with
      | nil =>
          cases epochs with
          | zero => exact (running ⟨rfl, rfl⟩).elim
          | succ epochs =>
              obtain ⟨chosen, _, rfl⟩ := FinDist.support_map .. ▸ reached
              simp only [responseRemaining, runtime.epochPlan_length_eq_epochInstructionCount,
                List.length_nil, zero_add, Nat.succ_mul]
              omega
      | cons instruction rest =>
          obtain ⟨next, _, rfl⟩ := FinDist.support_map .. ▸ reached
          simp [responseRemaining, Nat.add_assoc, Nat.add_comm]

theorem response_terminates (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    (runtime.responseProtocol inputs roster reactionRounds wire order).WellFoundedPlay := by
  apply wellFoundedPlay_of_rank (runtime.responseRemaining roster reactionRounds)
  intro before after transition
  obtain ⟨joint, legal, reached⟩ := transition
  have consumed := runtime.responseRemaining_step inputs roster reactionRounds wire order
    before after joint legal.1 reached
  omega

theorem response_history_length (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    ∀ {state}
      (trace : (runtime.responseProtocol inputs roster reactionRounds wire order).Trace state),
      trace.length + runtime.responseRemaining roster reactionRounds state =
        runtime.responseRemaining roster reactionRounds none
  | _, .start => by simp [Trace.length, responseProtocol]
  | _, .extend (source := before) (target := after) prior joint legal reached => by
      have earlier := runtime.response_history_length inputs roster reactionRounds wire order prior
      have consumed := runtime.responseRemaining_step inputs roster reactionRounds wire order
        before after joint legal.1 reached
      simp only [Trace.length]
      omega

theorem response_bounded (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    (runtime.responseProtocol inputs roster reactionRounds wire order).BoundedHorizon
      (runtime.responseRemaining roster reactionRounds none) := by
  intro state trace enough
  have count := runtime.response_history_length inputs roster reactionRounds wire order trace
  exact (runtime.responseRemaining_zero roster reactionRounds state).mp (by omega)

end Vegas.EventGraphRuntime
