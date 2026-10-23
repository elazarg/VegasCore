/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionLiftTrace
import GameTheoryExtensions.Protocol.StateSymmetry

/-! # Actual history equivalence before public exclusion -/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

@[simp] theorem protocolState_liftProtocolState
    (state : (runtime.reactiveApplication leaks).ProtocolState) :
    protocolState runtime leaks (liftProtocolState runtime leaks state) = state := by
  cases state with
  | none => rfl
  | some current =>
    cases current
    simp only [protocolState, liftProtocolState, Option.map_some, control, liftControl,
      execution_liftExecution]

@[simp] theorem jointActions_liftJointActions
    (joint : Player → Option (runtime.reactiveApplication leaks).Action) :
    jointActions runtime leaks (liftJointActions runtime leaks joint) = joint := by
  funext who
  cases chosen : joint who <;>
    simp only [jointActions, liftJointActions, chosen, Option.map_none, Option.map_some,
      action_liftAction]

@[simp] theorem liftJointActions_jointActions
    (joint : Player → Option (runtime.recoveryApplication leaks).Action) :
    liftJointActions runtime leaks (jointActions runtime leaks joint) = joint := by
  funext who
  cases chosen : joint who <;>
    simp only [jointActions, liftJointActions, chosen, Option.map_none, Option.map_some,
      liftAction_action]

theorem liftProtocolState_clear (state : (runtime.reactiveApplication leaks).ProtocolState) :
    ∀ current, liftProtocolState runtime leaks state = some current →
      current.execution.application.excluded = ∅ := by
  cases state with
  | none => intro current impossible; cases impossible
  | some current =>
    intro found same
    cases Option.some.inj same
    rfl

theorem liftProtocolState_protocolState_of_history_clear
    (initial : PMF (RecoveryState graph)) (horizon : Nat)
    (scheduler : (runtime.recoveryApplication leaks).Scheduler)
    {state : (runtime.recoveryApplication leaks).ProtocolState}
    (trace : ((runtime.recoveryApplication leaks).protocol initial horizon scheduler).Trace state)
    (clear : ∀ current, state = some current → current.execution.application.excluded = ∅) :
    liftProtocolState runtime leaks (protocolState runtime leaks state) = state := by
  cases state with
  | none => rfl
  | some current =>
    change some (⟨current.remaining, current.actor,
      liftExecution runtime leaks (execution runtime leaks current.execution)⟩ :
        (runtime.recoveryApplication leaks).Control) = some current
    rw [liftExecution_execution_of_history_clear runtime leaks initial horizon scheduler
      current trace (clear current rfl)]

private theorem publicRecord_of_history
    (initial : PMF (RecoveryState graph))
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
    (horizon : Nat) (scheduler : (runtime.recoveryApplication leaks).Scheduler)
    {state : (runtime.recoveryApplication leaks).ProtocolState}
    (trace : ((runtime.recoveryApplication leaks).protocol initial horizon scheduler).Trace state) :
    ReactiveApplication.stateInvariant PublicExclusionRecord state := by
  have invariant : (runtime.recoveryApplication leaks).Invariant PublicExclusionRecord :=
    { submit := fun state who material valid => valid.submit who material
      handle := fun state message next valid accepted => valid.handle runtime message next accepted
      environment := fun state command next valid reached =>
        valid.environment runtime command next reached }
  apply invariant.history initial horizon scheduler ?_ trace
  intro state supported
  obtain ⟨inputs, rfl⟩ := initialized state supported
  exact PublicExclusionRecord.initial inputs

/-- Clear actual recovery histories project to native states carrying exact
public absence of exclusion evidence. -/
theorem nativeHistory_record
    (initial : PMF (RecoveryState graph))
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
    (horizon : Nat) (scheduler : (runtime.recoveryApplication leaks).Scheduler)
    {state : (runtime.recoveryApplication leaks).ProtocolState}
    (trace : ((runtime.recoveryApplication leaks).protocol initial horizon scheduler).Trace state)
    (clear : ∀ current, state = some current → current.execution.application.excluded = ∅) :
    ∀ current, protocolState runtime leaks state = some current →
      PublicExclusionRecord (⟨current.execution.application, ∅⟩ : RecoveryState graph) := by
  cases state with
  | none => intro current impossible; cases impossible
  | some current =>
    intro found same
    cases Option.some.inj same
    have valid := publicRecord_of_history runtime leaks initial initialized horizon scheduler trace
    have empty := clear current rfl
    change PublicExclusionRecord (⟨current.execution.application.native, ∅⟩ : RecoveryState graph)
    cases stateEq : current.execution.application with
    | mk native excluded =>
      have flags : excluded = ∅ := by simpa only [stateEq] using empty
      subst excluded
      simpa only [ReactiveApplication.stateInvariant, stateEq] using valid

def recoveryHistory (initial : PMF (RecoveryState graph))
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
    (horizon : Nat) (scheduler : (runtime.recoveryApplication leaks).Scheduler)
    (history : ((runtime.reactiveApplication leaks).protocol (initial.map RecoveryState.native)
      horizon (nativeScheduler runtime leaks scheduler)).History)
    (clear : ∀ current, history.state = some current →
      PublicExclusionRecord (⟨current.execution.application, ∅⟩ : RecoveryState graph)) :
    ((runtime.recoveryApplication leaks).protocol initial horizon scheduler).History :=
  ⟨liftProtocolState runtime leaks history.state,
    recoveryTrace runtime leaks initial initialized horizon scheduler history.trace clear⟩

/-- Projecting a lifted actual native trace recovers every original state and
joint action, and hence the complete original history. -/
theorem nativeHistory_recoveryHistory
    (initial : PMF (RecoveryState graph))
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
    (horizon : Nat) (scheduler : (runtime.recoveryApplication leaks).Scheduler) :
    ∀ {state} (trace : ((runtime.reactiveApplication leaks).protocol
        (initial.map RecoveryState.native) horizon
        (nativeScheduler runtime leaks scheduler)).Trace state)
      (clear : ∀ current, state = some current →
        PublicExclusionRecord (⟨current.execution.application, ∅⟩ : RecoveryState graph)),
      nativeHistory runtime leaks initial horizon scheduler
        (recoveryHistory runtime leaks initial initialized horizon scheduler ⟨state, trace⟩ clear)
        (liftProtocolState_clear runtime leaks state) = ⟨state, trace⟩ := by
  intro state trace
  induction trace with
  | start => intro _clear; rfl
  | extend prior joint legal realized ih =>
    intro clear
    change (⟨_, .extend (nativeTrace runtime leaks initial horizon scheduler
        (recoveryTrace runtime leaks initial initialized horizon scheduler prior _) _)
        (jointActions runtime leaks (liftJointActions runtime leaks joint)) _ _⟩ :
      ((runtime.reactiveApplication leaks).protocol (initial.map RecoveryState.native) horizon
        (nativeScheduler runtime leaks scheduler)).History) = _
    exact StateSymmetry.history_extend_congr (ih _)
      (jointActions_liftJointActions runtime leaks joint)
      (protocolState_liftProtocolState runtime leaks _)

/-- Lifting a projected clear recovery history recovers the original complete
history, rather than merely its endpoint. -/
theorem recoveryHistory_nativeHistory
    (initial : PMF (RecoveryState graph))
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
    (horizon : Nat) (scheduler : (runtime.recoveryApplication leaks).Scheduler) :
    ∀ {state} (trace : ((runtime.recoveryApplication leaks).protocol initial horizon
        scheduler).Trace state)
      (clear : ∀ current, state = some current → current.execution.application.excluded = ∅),
      recoveryHistory runtime leaks initial initialized horizon scheduler
        (nativeHistory runtime leaks initial horizon scheduler ⟨state, trace⟩ clear)
        (nativeHistory_record runtime leaks initial initialized horizon scheduler trace clear) =
          ⟨state, trace⟩ := by
  intro state trace
  induction trace with
  | start => intro _clear; rfl
  | extend prior joint legal realized ih =>
    intro clear
    change (⟨_, .extend (recoveryTrace runtime leaks initial initialized horizon scheduler
        (nativeTrace runtime leaks initial horizon scheduler prior _) _)
        (liftJointActions runtime leaks (jointActions runtime leaks joint)) _ _⟩ :
      ((runtime.recoveryApplication leaks).protocol initial horizon scheduler).History) = _
    exact StateSymmetry.history_extend_congr (ih _)
      (liftJointActions_jointActions runtime leaks joint)
      (liftProtocolState_protocolState_of_history_clear runtime leaks initial horizon scheduler
        (.extend prior joint legal realized) clear)

end Vegas.EventGraphRuntime.RecoveryProjection
