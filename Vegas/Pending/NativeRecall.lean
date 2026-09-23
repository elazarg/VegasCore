/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.NativeProtocol
import Interaction.MessageApplicationAuthorship

/-! # Native submission counters are determined by private recall

No sender counter needs to be added to the policy observation. Starting from
an empty pool, it is the number of authored submissions in that sender's
retained action history. Replays, other players, and environment steps cannot
increment it.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Protocol GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def PlayerAction.authors (action : PlayerAction graph) : Bool :=
  match action.transmission with
  | some (.submit _) => true
  | _ => false

def authoredCount (history : List (NativeEntry graph)) : Nat :=
  history.countP (fun entry => entry.action.authors)

def NativeExecution.Counters (runtime : EventGraphRuntime graph)
    (execution : NativeExecution runtime) : Prop :=
  ∀ who, execution.native.pool.nextSerial who = authoredCount (execution.principalHistory who)

theorem native_initial_counters (runtime : EventGraphRuntime graph) (state : State graph) :
    NativeExecution.Counters runtime (NativeExecution.initial runtime
      (MessageApplication.State.initial runtime.application state)) := fun _ => rfl

theorem takeAction_counters (runtime : EventGraphRuntime graph) (who : Player)
    (execution : NativeExecution runtime) (action : PlayerAction graph)
    (counters : execution.Counters runtime) :
    (runtime.takeAction who execution action).Counters runtime := by
  intro observer
  by_cases same : observer = who
  · subst observer
    change (runtime.transmit who execution.native action.transmission).pool.nextSerial who = _
    rw [runtime.takeAction_history_self]
    simp only [authoredCount, List.countP_append, List.countP_cons, List.countP_nil]
    cases chosen : action.transmission with
    | none => simpa [transmit, authoredCount, PlayerAction.authors, chosen] using counters who
    | some transmission =>
        cases transmission with
        | submit submission => simp [transmit, MessagePool.submit, PlayerAction.authors,
            chosen, counters who, authoredCount]
        | replay id =>
            simpa [transmit, authoredCount, PlayerAction.authors, chosen] using counters who
  · change (runtime.transmit who execution.native action.transmission).pool.nextSerial observer = _
    simp only [takeAction, ite_eq_right same]
    cases action.transmission with
    | none => exact counters observer
    | some transmission =>
        cases transmission with
        | submit submission => simpa [transmit, MessagePool.submit, same] using counters observer
        | replay id => simpa [transmit] using counters observer

theorem nativeInstructionStep_counters (runtime : EventGraphRuntime graph)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (execution next : NativeExecution runtime) (joint : Player → Option (PlayerAction graph))
    (counters : execution.Counters runtime)
    (reached : next ∈ (runtime.nativeInstructionStep wire instruction execution joint).support) :
    next.Counters runtime := by
  have environment (command : runtime.application.EnvironmentPolicyCommand)
      (after : runtime.application.PolicyExecution)
      (supported : after ∈ (runtime.application.environmentPolicyStep
        (execution.environmentExecution runtime) command).support) :
      NativeExecution.Counters runtime
        ⟨after.native, execution.principalHistory, after.environmentHistory⟩ := by
    intro who
    exact (runtime.application.environmentStep_nextSerial _ _ command supported who).trans
      (counters who)
  cases instruction with
  | player who =>
      cases FinDist.mem_support_pure.mp reached
      exact runtime.takeAction_counters who execution _ counters
  | wire =>
      obtain ⟨after, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      simp only [serviceStep, MessageApplication.invoke, MessageApplication.wireEnvironment,
        FinDist.bind_map, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨command, _, supported⟩ := supported
      exact environment _ after supported
  | grant event | includeLatest event owner | sample event | tick | expire event =>
      obtain ⟨after, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      exact environment _ after supported

def nativeCounters (runtime : EventGraphRuntime graph) : NativeProtocolState runtime → Prop
  | none => True
  | some control => control.execution.Counters runtime

theorem nativeTransition_counters (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (before after : NativeProtocolState runtime) (joint : Player → Option (PlayerAction graph))
    (counters : runtime.nativeCounters before)
    (reached : after ∈
      (runtime.nativeTransition inputs roster reactionRounds wire order before joint).support) :
    runtime.nativeCounters after := by
  cases before with
  | none =>
      obtain ⟨input, _, rfl⟩ := FinDist.support_map .. ▸ reached
      exact runtime.native_initial_counters _
  | some control =>
      rcases control with ⟨epochs, plan, execution⟩
      cases plan with
      | nil =>
          cases epochs with
          | zero => cases FinDist.mem_support_pure.mp reached; exact counters
          | succ epochs =>
              obtain ⟨chosen, _, rfl⟩ := FinDist.support_map .. ▸ reached
              exact counters
      | cons instruction rest =>
          obtain ⟨next, supported, rfl⟩ := FinDist.support_map .. ▸ reached
          exact runtime.nativeInstructionStep_counters wire instruction execution next joint
            counters supported

/-- The counter invariant holds at every legal history, including off-path
histories under arbitrary player actions and service choices. -/
theorem native_history_counters (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    ∀ {state}
      (_trace : (runtime.nativeProtocol inputs roster reactionRounds wire order).Trace state),
      runtime.nativeCounters state
  | _, .start => trivial
  | _, .extend prior joint _ reached =>
      runtime.nativeTransition_counters inputs roster reactionRounds wire order _ _ joint
        (runtime.native_history_counters inputs roster reactionRounds wire order prior) reached

end Vegas.EventGraphRuntime
