/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionNativeFailure
import Vegas.Pending.ExclusionLiftedSteps

/-! # Actual recovery lifts of publicly clear native traces -/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

def liftProtocolState : (runtime.reactiveApplication leaks).ProtocolState →
    (runtime.recoveryApplication leaks).ProtocolState := Option.map (liftControl runtime leaks)

def liftJointActions (joint : Player → Option (runtime.reactiveApplication leaks).Action) :
    Player → Option (runtime.recoveryApplication leaks).Action :=
  fun who => (joint who).map (liftAction runtime leaks)

@[simp] theorem actor_liftProtocolState
    (state : (runtime.reactiveApplication leaks).ProtocolState) :
    (runtime.recoveryApplication leaks).actor (liftProtocolState runtime leaks state) =
      (runtime.reactiveApplication leaks).actor state := by
  cases state <;> rfl

@[simp] theorem terminal_liftProtocolState
    (state : (runtime.reactiveApplication leaks).ProtocolState) :
    (runtime.recoveryApplication leaks).terminal (liftProtocolState runtime leaks state) ↔
      (runtime.reactiveApplication leaks).terminal state := by
  cases state <;> rfl

theorem liftJointActions_legal (initial : PMF (RecoveryState graph)) (horizon : Nat)
    (scheduler : (runtime.recoveryApplication leaks).Scheduler)
    (state : (runtime.reactiveApplication leaks).ProtocolState)
    (joint : Player → Option (runtime.reactiveApplication leaks).Action)
    (legal : ((runtime.reactiveApplication leaks).protocol
      (initial.map RecoveryState.native) horizon
      (nativeScheduler runtime leaks scheduler)).Legal state joint) :
    ((runtime.recoveryApplication leaks).protocol
      initial horizon scheduler).Legal
      (liftProtocolState runtime leaks state) (liftJointActions runtime leaks joint) := by
  refine ⟨fun ended => legal.1 ((terminal_liftProtocolState runtime leaks state).mp ended), ?_⟩
  intro who
  have permitted := legal.2 who
  cases chosen : joint who with
  | none =>
    simp only [liftJointActions, chosen, Option.map_none]
    change (runtime.recoveryApplication leaks).actor (liftProtocolState runtime leaks state) ≠
      some who
    rw [actor_liftProtocolState runtime leaks state]
    change ¬ ((runtime.reactiveApplication leaks).protocol
      (initial.map RecoveryState.native) horizon
      (nativeScheduler runtime leaks scheduler)).active state who
    simpa only [chosen] using permitted
  | some response =>
    simp only [liftJointActions, chosen, Option.map_some]
    change (runtime.recoveryApplication leaks).actor (liftProtocolState runtime leaks state) =
      some who ∧ _
    refine ⟨?_, Set.mem_univ _⟩
    rw [actor_liftProtocolState runtime leaks state]
    exact (show (runtime.reactiveApplication leaks).actor state = some who ∧ _ from
      chosen ▸ permitted).1

theorem transition_lift_support (initial : PMF (RecoveryState graph))
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph)) (horizon : Nat)
    (scheduler : (runtime.recoveryApplication leaks).Scheduler)
    {before after : (runtime.reactiveApplication leaks).ProtocolState}
    (joint : Player → Option (runtime.reactiveApplication leaks).Action)
    (valid : ∀ current, before = some current →
      PublicExclusionRecord (⟨current.execution.application, ∅⟩ : RecoveryState graph))
    (clear : ∀ current, after = some current →
      PublicExclusionRecord (⟨current.execution.application, ∅⟩ : RecoveryState graph))
    (realized : after ∈ ((runtime.reactiveApplication leaks).transition
      (initial.map RecoveryState.native) horizon
      (nativeScheduler runtime leaks scheduler) before joint).support) :
    liftProtocolState runtime leaks after ∈
      ((runtime.recoveryApplication leaks).transition
        initial horizon scheduler
        (liftProtocolState runtime leaks before)
        (liftJointActions runtime leaks joint)).support := by
  cases before with
  | none =>
    obtain ⟨native, supported, rfl⟩ := PMF.support_map .. ▸ realized
    rw [PMF.mem_support_map_iff] at supported
    obtain ⟨source, sourceSupported, same⟩ := supported
    subst native
    obtain ⟨inputs, same⟩ := initialized source sourceSupported
    subst source
    change _ ∈ (initial.map fun state => some (⟨horizon, none,
      ReactiveApplication.Execution.initial (runtime.recoveryApplication leaks) state⟩ :
        (runtime.recoveryApplication leaks).Control)).support
    rw [PMF.mem_support_map_iff]
    exact ⟨⟨State.initial inputs, ∅⟩, sourceSupported, rfl⟩
  | some current =>
    rcases current with ⟨remaining, actor, current⟩
    cases actor with
    | some who =>
      cases (PMF.mem_support_pure_iff _ _).mp realized
      have same := respond_lift runtime leaks current who ((joint who).getD ⟨none⟩)
      cases chosen : joint who with
      | none =>
        simpa only [ReactiveApplication.transition, liftProtocolState, liftControl,
          liftJointActions, chosen, Option.getD_none, Option.map_none, Option.map_some, liftAction,
          PMF.mem_support_pure_iff] using
          congrArg (fun next => some (ReactiveApplication.Control.mk remaining none next)) same.symm
      | some response =>
        simpa only [ReactiveApplication.transition, liftProtocolState, liftControl,
          liftJointActions, chosen, Option.getD_some, Option.map_some,
          PMF.mem_support_pure_iff] using
          congrArg (fun next => some (ReactiveApplication.Control.mk remaining none next)) same.symm
    | none =>
      cases remaining with
      | zero =>
        cases (PMF.mem_support_pure_iff _ _).mp realized
        exact (PMF.mem_support_pure_iff _ _).mpr rfl
      | succ remaining =>
        change after ∈ ((nativeScheduler runtime leaks scheduler current.environmentRecall
          (current.observeEnvironment (runtime.reactiveApplication leaks))).bind fun chosen =>
            (current.environmentStep (runtime.reactiveApplication leaks) chosen).map fun next =>
              some (⟨remaining, chosen.actor? (runtime.reactiveApplication leaks), next⟩ :
                (runtime.reactiveApplication leaks).Control)).support at realized
        rw [PMF.mem_support_bind_iff] at realized
        obtain ⟨chosen, selected, moved⟩ := realized
        obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
        change chosen ∈ ((scheduler
          (current.environmentRecall.map (liftEnvironmentEntry runtime leaks))
          (liftEnvironmentView runtime leaks
            (current.observeEnvironment (runtime.reactiveApplication leaks)))).map
              (command runtime leaks)).support at selected
        rw [PMF.mem_support_map_iff] at selected
        obtain ⟨recoveryChosen, selected, same⟩ := selected
        have chosenEq : liftCommand runtime leaks chosen = recoveryChosen := by
          rw [← same, liftCommand_command]
        have lifted := environmentStep_lift_support runtime leaks current next
          (valid _ rfl) chosen (clear _ rfl) supported
        change some (liftControl runtime leaks
          ⟨remaining, chosen.actor? (runtime.reactiveApplication leaks), next⟩) ∈
          ((scheduler
            (liftExecution runtime leaks current).environmentRecall
            ((liftExecution runtime leaks current).observeEnvironment
              (runtime.recoveryApplication leaks))).bind fun chosen =>
            ((liftExecution runtime leaks current).environmentStep
              (runtime.recoveryApplication leaks) chosen).map fun next =>
                some (⟨remaining, chosen.actor? (runtime.recoveryApplication leaks), next⟩ :
                  (runtime.recoveryApplication leaks).Control)).support
        rw [PMF.mem_support_bind_iff]
        refine ⟨recoveryChosen, selected, ?_⟩
        rw [PMF.mem_support_map_iff]
        refine ⟨liftExecution runtime leaks next, chosenEq ▸ lifted, ?_⟩
        rw [← chosenEq]
        cases chosen <;> rfl


private theorem native_initial_inputs (initial : PMF (RecoveryState graph))
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph)) :
    ∀ native ∈ (initial.map RecoveryState.native).support, ∃ inputs,
      native = State.initial inputs := by
  intro native supported
  rw [PMF.mem_support_map_iff] at supported
  obtain ⟨state, sourceSupported, rfl⟩ := supported
  obtain ⟨inputs, rfl⟩ := initialized state sourceSupported
  exact ⟨inputs, rfl⟩

/-- Lift every state and action of a genuinely public-clear native prefix into
an actual recovery prefix. Public failure persistence makes every predecessor
clear as well. -/
def recoveryTrace (initial : PMF (RecoveryState graph))
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
    (horizon : Nat) (scheduler : (runtime.recoveryApplication leaks).Scheduler) :
    ∀ {state} (_trace : ((runtime.reactiveApplication leaks).protocol
        (initial.map RecoveryState.native) horizon
        (nativeScheduler runtime leaks scheduler)).Trace state),
      (∀ current, state = some current →
        PublicExclusionRecord (⟨current.execution.application, ∅⟩ : RecoveryState graph)) →
      ((runtime.recoveryApplication leaks).protocol
        initial horizon scheduler).Trace
        (liftProtocolState runtime leaks state)
  | _, .start, _ => .start
  | _, .extend prior joint legal realized, clear =>
      .extend (recoveryTrace initial initialized horizon scheduler prior
        (native_clear_before_transition runtime leaks (initial.map RecoveryState.native)
          (native_initial_inputs initial initialized) horizon
          (nativeScheduler runtime leaks scheduler) prior joint realized clear))
        (liftJointActions runtime leaks joint)
        (liftJointActions_legal runtime leaks initial horizon scheduler _ joint legal)
        (transition_lift_support runtime leaks initial initialized horizon scheduler joint
          (native_clear_before_transition runtime leaks (initial.map RecoveryState.native)
            (native_initial_inputs initial initialized) horizon
            (nativeScheduler runtime leaks scheduler) prior joint realized clear) clear realized)

end Vegas.EventGraphRuntime.RecoveryProjection
