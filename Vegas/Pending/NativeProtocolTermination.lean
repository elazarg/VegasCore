/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.NativeProtocol
import GameTheory.Protocol.Backward

/-! # Bounded native service

The rank counts service instructions and order selections. A player decision
consumes one invocation, regardless of its private memory or optional packet.
Every legal protocol transition consumes one unit, independently of its policy.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def nativeRemaining (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat) : NativeProtocolState runtime → Nat
  | none => runtime.serviceEpochs * (runtime.epochInstructionCount roster reactionRounds + 1) + 1
  | some control => control.plan.length +
      control.epochs * (runtime.epochInstructionCount roster reactionRounds + 1)

theorem nativeRemaining_zero (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat) (state : NativeProtocolState runtime) :
    runtime.nativeRemaining roster reactionRounds state = 0 ↔ runtime.nativeTerminal state := by
  cases state with
  | none => simp [nativeRemaining, nativeTerminal]
  | some control =>
      simp [nativeRemaining, nativeTerminal, NativeControl.Terminal, and_comm]

theorem nativeRemaining_step (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (before after : NativeProtocolState runtime)
    (joint : Player → Option (PlayerAction graph))
    (running : ¬ runtime.nativeTerminal before)
    (reached : after ∈
      (runtime.nativeTransition inputs roster reactionRounds wire order before joint).support) :
    runtime.nativeRemaining roster reactionRounds after + 1 =
      runtime.nativeRemaining roster reactionRounds before := by
  cases before with
  | none =>
      obtain ⟨input, _, rfl⟩ := FinDist.support_map .. ▸ reached
      simp [nativeRemaining]
  | some control =>
      rcases control with ⟨epochs, plan, execution⟩
      cases plan with
      | nil =>
          cases epochs with
          | zero => exact (running ⟨rfl, rfl⟩).elim
          | succ epochs =>
              obtain ⟨chosen, _, rfl⟩ := FinDist.support_map .. ▸ reached
              simp only [nativeRemaining, runtime.epochPlan_length_eq_epochInstructionCount,
                List.length_nil, zero_add, Nat.succ_mul]
              omega
      | cons instruction rest =>
          obtain ⟨next, _, rfl⟩ := FinDist.support_map .. ▸ reached
          simp [nativeRemaining, Nat.add_assoc, Nat.add_comm]

theorem native_terminates (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    (runtime.nativeProtocol inputs roster reactionRounds wire order).WellFoundedPlay := by
  apply wellFoundedPlay_of_rank (runtime.nativeRemaining roster reactionRounds)
  intro before after transition
  obtain ⟨joint, legal, reached⟩ := transition
  have consumed := runtime.nativeRemaining_step inputs roster reactionRounds wire order
    before after joint legal.1 reached
  omega

theorem native_history_length (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    ∀ {state}
      (trace : (runtime.nativeProtocol inputs roster reactionRounds wire order).Trace state),
      trace.length + runtime.nativeRemaining roster reactionRounds state =
        runtime.nativeRemaining roster reactionRounds none
  | _, .start => by simp [Trace.length, nativeProtocol]
  | _, .extend (source := before) (target := after) prior joint legal reached => by
      have earlier := runtime.native_history_length inputs roster reactionRounds wire order prior
      have consumed := runtime.nativeRemaining_step inputs roster reactionRounds wire order
        before after joint legal.1 reached
      simp only [Trace.length]
      omega

theorem native_bounded (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    (runtime.nativeProtocol inputs roster reactionRounds wire order).BoundedHorizon
      (runtime.nativeRemaining roster reactionRounds none) := by
  intro state trace enough
  have count := runtime.native_history_length inputs roster reactionRounds wire order trace
  exact (runtime.nativeRemaining_zero roster reactionRounds state).mp (by omega)

end Vegas.EventGraphRuntime
