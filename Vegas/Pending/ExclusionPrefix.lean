/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionClearLift
import Vegas.Pending.ExclusionPairedEnvironment

/-! # Actual native prefixes before permanent exclusion

The comparison scheduler evaluates recovery scheduling at clear lifts of native
recall and views. Every actual clear recovery prefix has a native realization
with the same projected control state. This concerns support before exclusion;
it makes no completion claim about the comparison scheduler after exclusion.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

def nativeScheduler (scheduler : (runtime.recoveryApplication leaks).Scheduler) :
    (runtime.reactiveApplication leaks).Scheduler := fun past view =>
  (scheduler (past.map (liftEnvironmentEntry runtime leaks))
    (liftEnvironmentView runtime leaks view)).map (command runtime leaks)

def protocolState : (runtime.recoveryApplication leaks).ProtocolState →
    (runtime.reactiveApplication leaks).ProtocolState := Option.map (control runtime leaks)

def jointActions (joint : Player → Option (runtime.recoveryApplication leaks).Action) :
    Player → Option (runtime.reactiveApplication leaks).Action :=
  fun who => (joint who).map (action runtime leaks)

theorem nativeScheduler_of_history_clear
    (initial : PMF (RecoveryState graph)) (horizon : Nat)
    (scheduler : (runtime.recoveryApplication leaks).Scheduler)
    (current : (runtime.recoveryApplication leaks).Control)
    (trace : ((runtime.recoveryApplication leaks).protocol initial horizon scheduler).Trace
      (some current)) (empty : current.execution.application.excluded = ∅) :
    nativeScheduler runtime leaks scheduler
        (execution runtime leaks current.execution).environmentRecall
        ((execution runtime leaks current.execution).observeEnvironment
          (runtime.reactiveApplication leaks)) =
      (scheduler current.execution.environmentRecall
        (current.execution.observeEnvironment (runtime.recoveryApplication leaks))).map
          (command runtime leaks) := by
  have same := liftExecution_execution_of_history_clear runtime leaks initial horizon scheduler
    current trace empty
  have recallEq := congrArg (fun next => next.environmentRecall) same
  dsimp only [liftExecution, execution] at recallEq
  have viewEq : liftEnvironmentView runtime leaks
      ((execution runtime leaks current.execution).observeEnvironment
        (runtime.reactiveApplication leaks)) =
      current.execution.observeEnvironment (runtime.recoveryApplication leaks) := by
    rw [observeEnvironment runtime leaks current.execution]
    exact liftEnvironmentView_environmentView runtime leaks _ empty
  unfold nativeScheduler
  change (scheduler
    ((current.execution.environmentRecall.map (environmentEntry runtime leaks)).map
      (liftEnvironmentEntry runtime leaks)) _).map _ = _
  rw [recallEq, viewEq]

/-- Every realized environment step with a clear result has a projected
native realization under the projected command. -/
theorem environmentStep_projected_support
    (current next : (runtime.recoveryApplication leaks).Execution)
    (chosen : (runtime.recoveryApplication leaks).Command)
    (empty : current.application.excluded = ∅) (clear : next.application.excluded = ∅)
    (realized : next ∈ (current.environmentStep
      (runtime.recoveryApplication leaks) chosen).support) :
    execution runtime leaks next ∈
      ((execution runtime leaks current).environmentStep (runtime.reactiveApplication leaks)
        (command runtime leaks chosen)).support := by
  obtain ⟨joint, firstMarginal, secondMarginal, paired⟩ :=
    exists_paired_environmentStep runtime leaks current chosen empty
  rw [← secondMarginal, PMF.mem_support_map_iff] at realized
  obtain ⟨pair, supported, same⟩ := realized
  have matched := paired pair supported (same.symm ▸ clear)
  rw [← firstMarginal, PMF.mem_support_map_iff]
  exact ⟨pair, supported, matched.trans (congrArg (execution runtime leaks) same)⟩

/-- Initialized clear transitions project to actual native transitions. -/
theorem transition_projected_support
    (initial : PMF (RecoveryState graph)) (horizon : Nat)
    (scheduler : (runtime.recoveryApplication leaks).Scheduler)
    (before after : (runtime.recoveryApplication leaks).Control)
    (priorTrace : ((runtime.recoveryApplication leaks).protocol initial horizon scheduler).Trace
      (some before))
    (joint : Player → Option (runtime.recoveryApplication leaks).Action)
    (empty : before.execution.application.excluded = ∅)
    (clear : after.execution.application.excluded = ∅)
    (realized : some after ∈ ((runtime.recoveryApplication leaks).transition initial horizon
      scheduler (some before) joint).support) :
    some (control runtime leaks after) ∈
      ((runtime.reactiveApplication leaks).transition (initial.map RecoveryState.native) horizon
        (nativeScheduler runtime leaks scheduler) (some (control runtime leaks before))
        (jointActions runtime leaks joint)).support := by
  rcases before with ⟨remaining, actor, current⟩
  cases actor with
  | some who =>
    cases (PMF.mem_support_pure_iff _ _).mp realized
    have same := respond_of_empty runtime leaks current empty who ((joint who).getD ⟨none⟩)
    cases chosen : joint who with
    | none =>
      simpa only [ReactiveApplication.transition, control, jointActions, chosen,
        Option.getD_none, Option.map_none, action, PMF.mem_support_pure_iff] using
        congrArg (fun next => some (ReactiveApplication.Control.mk remaining none next)) same
    | some response =>
      simpa only [ReactiveApplication.transition, control, jointActions, chosen,
        Option.getD_some, Option.map_some, PMF.mem_support_pure_iff] using
        congrArg (fun next => some (ReactiveApplication.Control.mk remaining none next)) same
  | none =>
    cases remaining with
    | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp realized
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
    | succ remaining =>
      change some after ∈ ((scheduler current.environmentRecall
        (current.observeEnvironment (runtime.recoveryApplication leaks))).bind fun chosen =>
          (current.environmentStep (runtime.recoveryApplication leaks) chosen).map fun next =>
            some (⟨remaining, chosen.actor? (runtime.recoveryApplication leaks), next⟩ :
              (runtime.recoveryApplication leaks).Control)).support at realized
      rw [PMF.mem_support_bind_iff] at realized
      obtain ⟨chosen, selected, moved⟩ := realized
      obtain ⟨next, supported, same⟩ := PMF.support_map .. ▸ moved
      cases Option.some.inj same
      have nativeSelected : command runtime leaks chosen ∈
          (nativeScheduler runtime leaks scheduler
            (execution runtime leaks current).environmentRecall
            ((execution runtime leaks current).observeEnvironment
              (runtime.reactiveApplication leaks))).support := by
        rw [nativeScheduler_of_history_clear runtime leaks initial horizon scheduler
          ⟨remaining + 1, none, current⟩ priorTrace empty, PMF.mem_support_map_iff]
        exact ⟨chosen, selected, rfl⟩
      have nativeMoved := environmentStep_projected_support runtime leaks current next chosen
        empty clear supported
      change some (control runtime leaks
        ⟨remaining, chosen.actor? (runtime.recoveryApplication leaks), next⟩) ∈
        ((nativeScheduler runtime leaks scheduler
          (execution runtime leaks current).environmentRecall
          ((execution runtime leaks current).observeEnvironment
            (runtime.reactiveApplication leaks))).bind fun chosen =>
          ((execution runtime leaks current).environmentStep
            (runtime.reactiveApplication leaks) chosen).map fun next =>
              some (⟨remaining, chosen.actor? (runtime.reactiveApplication leaks), next⟩ :
                (runtime.reactiveApplication leaks).Control)).support
      rw [PMF.mem_support_bind_iff]
      refine ⟨command runtime leaks chosen, nativeSelected, ?_⟩
      rw [PMF.mem_support_map_iff]
      refine ⟨execution runtime leaks next, nativeMoved, ?_⟩
      cases chosen <;> rfl

@[simp] theorem actor_protocolState (before : (runtime.recoveryApplication leaks).ProtocolState) :
    (runtime.reactiveApplication leaks).actor (protocolState runtime leaks before) =
      (runtime.recoveryApplication leaks).actor before := by
  cases before <;> rfl

@[simp] theorem terminal_protocolState
    (before : (runtime.recoveryApplication leaks).ProtocolState) :
    (runtime.reactiveApplication leaks).terminal (protocolState runtime leaks before) ↔
      (runtime.recoveryApplication leaks).terminal before := by
  cases before <;> rfl

theorem jointActions_legal (initial : PMF (RecoveryState graph)) (horizon : Nat)
    (scheduler : (runtime.recoveryApplication leaks).Scheduler)
    (before : (runtime.recoveryApplication leaks).ProtocolState)
    (joint : Player → Option (runtime.recoveryApplication leaks).Action)
    (legal : ((runtime.recoveryApplication leaks).protocol initial horizon scheduler).Legal
      before joint) :
    ((runtime.reactiveApplication leaks).protocol (initial.map RecoveryState.native) horizon
      (nativeScheduler runtime leaks scheduler)).Legal (protocolState runtime leaks before)
        (jointActions runtime leaks joint) := by
  refine ⟨fun ended => legal.1 ((terminal_protocolState runtime leaks before).mp ended), ?_⟩
  intro who
  have permitted := legal.2 who
  cases chosen : joint who with
  | none =>
    simp only [jointActions, chosen, Option.map_none]
    change (runtime.reactiveApplication leaks).actor (protocolState runtime leaks before) ≠
      some who
    rw [actor_protocolState runtime leaks before]
    change ¬ ((runtime.recoveryApplication leaks).protocol initial horizon scheduler).active
      before who
    simpa only [chosen] using permitted
  | some response =>
    simp only [jointActions, chosen, Option.map_some]
    change (runtime.reactiveApplication leaks).actor (protocolState runtime leaks before) =
      some who ∧ _
    refine ⟨?_, Set.mem_univ _⟩
    rw [actor_protocolState runtime leaks before]
    exact (show (runtime.recoveryApplication leaks).actor before = some who ∧ _ from
      chosen ▸ permitted).1

private theorem initial_projected_support
    (initial : PMF (RecoveryState graph)) (horizon : Nat)
    (scheduler : (runtime.recoveryApplication leaks).Scheduler)
    (after : (runtime.recoveryApplication leaks).ProtocolState)
    (joint : Player → Option (runtime.recoveryApplication leaks).Action)
    (realized : after ∈ ((runtime.recoveryApplication leaks).transition initial horizon
      scheduler none joint).support) :
    protocolState runtime leaks after ∈
      ((runtime.reactiveApplication leaks).transition (initial.map RecoveryState.native) horizon
        (nativeScheduler runtime leaks scheduler) none
        (jointActions runtime leaks joint)).support := by
  obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ realized
  change _ ∈ ((initial.map RecoveryState.native).map fun native =>
    some (⟨horizon, none, ReactiveApplication.Execution.initial
      (runtime.reactiveApplication leaks) native⟩ :
      (runtime.reactiveApplication leaks).Control)).support
  rw [PMF.mem_support_map_iff]
  refine ⟨state.native, ?_, ?_⟩
  · rw [PMF.mem_support_map_iff]
    exact ⟨state, supported, rfl⟩
  · simp only [protocolState, Option.map_some, control, RecoveryProjection.initial]

/-- Exclusion monotonicity makes a predecessor clear whenever its realized
successor is clear. -/
theorem clear_before_transition
    (initial : PMF (RecoveryState graph)) (horizon : Nat)
    (scheduler : (runtime.recoveryApplication leaks).Scheduler)
    {before after : (runtime.recoveryApplication leaks).ProtocolState}
    (joint : Player → Option (runtime.recoveryApplication leaks).Action)
    (realized : after ∈ ((runtime.recoveryApplication leaks).transition initial horizon
      scheduler before joint).support)
    (clear : ∀ current, after = some current → current.execution.application.excluded = ∅) :
    ∀ current, before = some current → current.execution.application.excluded = ∅ := by
  cases before with
  | none => intro current impossible; cases impossible
  | some current =>
    intro found same
    cases Option.some.inj same
    obtain ⟨next, nextEq, _recall⟩ :=
      (runtime.recoveryApplication leaks).transition_recall_prefix initial horizon scheduler
        current after joint realized
    have grows := (recoveryApplication_exclusion_monotone runtime leaks).transition initial
      horizon scheduler current next joint (nextEq ▸ realized)
    rw [clear next nextEq] at grows
    exact Finset.subset_empty.mp grows

/-- Actual transitions into clear states have projected native realizations. -/
theorem projected_transition_support
    (initial : PMF (RecoveryState graph)) (horizon : Nat)
    (scheduler : (runtime.recoveryApplication leaks).Scheduler)
    {before after : (runtime.recoveryApplication leaks).ProtocolState}
    (priorTrace : ((runtime.recoveryApplication leaks).protocol initial horizon scheduler).Trace
      before) (joint : Player → Option (runtime.recoveryApplication leaks).Action)
    (realized : after ∈ ((runtime.recoveryApplication leaks).transition initial horizon
      scheduler before joint).support)
    (clear : ∀ current, after = some current → current.execution.application.excluded = ∅) :
    protocolState runtime leaks after ∈
      ((runtime.reactiveApplication leaks).transition (initial.map RecoveryState.native) horizon
        (nativeScheduler runtime leaks scheduler) (protocolState runtime leaks before)
        (jointActions runtime leaks joint)).support := by
  cases before with
  | none =>
    exact initial_projected_support runtime leaks initial horizon scheduler after joint realized
  | some current =>
    obtain ⟨next, nextEq, _recall⟩ :=
      (runtime.recoveryApplication leaks).transition_recall_prefix initial horizon scheduler
        current after joint realized
    subst after
    exact transition_projected_support runtime leaks initial horizon scheduler current next
      priorTrace joint (clear_before_transition runtime leaks initial horizon scheduler joint
        realized clear current rfl) (clear next rfl) realized

/-- Project every state and joint action of an actual clear recovery prefix
into a genuine native prefix under the clear-lift comparison scheduler. -/
def nativeTrace (initial : PMF (RecoveryState graph)) (horizon : Nat)
    (scheduler : (runtime.recoveryApplication leaks).Scheduler) :
    ∀ {state} (_trace : ((runtime.recoveryApplication leaks).protocol initial horizon
        scheduler).Trace state),
      (∀ current, state = some current → current.execution.application.excluded = ∅) →
      ((runtime.reactiveApplication leaks).protocol (initial.map RecoveryState.native) horizon
        (nativeScheduler runtime leaks scheduler)).Trace (protocolState runtime leaks state)
  | _, .start, _ => .start
  | _, .extend prior joint legal realized, clear =>
      .extend (nativeTrace initial horizon scheduler prior
        (clear_before_transition runtime leaks initial horizon scheduler joint realized clear))
        (jointActions runtime leaks joint)
        (jointActions_legal runtime leaks initial horizon scheduler _ joint legal)
        (projected_transition_support runtime leaks initial horizon scheduler prior joint
          realized clear)

/-- Native projection preserves the number of realized transitions. -/
theorem nativeTrace_length (initial : PMF (RecoveryState graph)) (horizon : Nat)
    (scheduler : (runtime.recoveryApplication leaks).Scheduler) :
    ∀ {state} (trace : ((runtime.recoveryApplication leaks).protocol initial horizon
        scheduler).Trace state)
      (clear : ∀ current, state = some current → current.execution.application.excluded = ∅),
      (nativeTrace runtime leaks initial horizon scheduler trace clear).length = trace.length := by
  intro state trace
  induction trace with
  | start => intro _clear; rfl
  | extend prior joint legal realized ih =>
    intro clear
    change (nativeTrace runtime leaks initial horizon scheduler prior _).length + 1 =
      prior.length + 1
    exact congrArg (fun length => length + 1) (ih _)

/-- Projection retains the realized predecessor and the projected joint action. -/
@[simp] theorem nativeTrace_extend
    (initial : PMF (RecoveryState graph)) (horizon : Nat)
    (scheduler : (runtime.recoveryApplication leaks).Scheduler)
    {before after : (runtime.recoveryApplication leaks).ProtocolState}
    (priorTrace : ((runtime.recoveryApplication leaks).protocol initial horizon scheduler).Trace
      before) (joint : Player → Option (runtime.recoveryApplication leaks).Action)
    (legal : ((runtime.recoveryApplication leaks).protocol initial horizon scheduler).Legal
      before joint)
    (realized : after ∈ ((runtime.recoveryApplication leaks).transition initial horizon
      scheduler before joint).support)
    (clear : ∀ current, after = some current → current.execution.application.excluded = ∅) :
    nativeTrace runtime leaks initial horizon scheduler
        (.extend priorTrace joint legal realized) clear =
      .extend (nativeTrace runtime leaks initial horizon scheduler priorTrace
        (clear_before_transition runtime leaks initial horizon scheduler joint realized clear))
        (jointActions runtime leaks joint)
        (jointActions_legal runtime leaks initial horizon scheduler before joint legal)
        (projected_transition_support runtime leaks initial horizon scheduler priorTrace joint
          realized clear) := rfl

/-- The actual native history associated to a clear recovery history. -/
def nativeHistory (initial : PMF (RecoveryState graph)) (horizon : Nat)
    (scheduler : (runtime.recoveryApplication leaks).Scheduler)
    (history : ((runtime.recoveryApplication leaks).protocol initial horizon scheduler).History)
    (clear : ∀ current, history.state = some current →
      current.execution.application.excluded = ∅) :
    ((runtime.reactiveApplication leaks).protocol (initial.map RecoveryState.native) horizon
      (nativeScheduler runtime leaks scheduler)).History :=
  ⟨protocolState runtime leaks history.state,
    nativeTrace runtime leaks initial horizon scheduler history.trace clear⟩

end Vegas.EventGraphRuntime.RecoveryProjection
