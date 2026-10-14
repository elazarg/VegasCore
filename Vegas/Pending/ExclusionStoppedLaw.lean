/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionPairedBehavior
import Vegas.Pending.ExclusionFailureOwners
import GameTheoryExtensions.Analysis.Protocol.StoppedKernelComparison

/-! # Actual continuation laws stopped at the first permanent exclusion

The complete surviving native history and exact first excluded-owner set are
retained. Collapsing the failure labels gives the single exit atom used by
coarser continuation estimates.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (initial : PMF (RecoveryState graph)) (horizon : Nat)
  (scheduler : (runtime.recoveryApplication leaks).Scheduler)

local notation "NativeModel" => ReactiveApplication.information (reactiveApplication runtime leaks)
  (initial.map RecoveryState.native) horizon (nativeScheduler runtime leaks scheduler)
local notation "RecoveryModel" => ReactiveApplication.information
  (recoveryApplication runtime leaks) initial horizon scheduler
local notation "NativeProtocol" => ReactiveApplication.protocol (reactiveApplication runtime leaks)
  (initial.map RecoveryState.native) horizon (nativeScheduler runtime leaks scheduler)
local notation "RecoveryProtocol" => ReactiveApplication.protocol
  (recoveryApplication runtime leaks) initial horizon scheduler

/-- Every realized native endpoint has a publicly clear failure record. -/
def NativeClear (history : (NativeProtocol).History) : Prop :=
  ∀ current, history.state = some current →
    PublicExclusionRecord (⟨current.execution.application, ∅⟩ : RecoveryState graph)

/-- The actual recovery endpoint has no permanently excluded players. -/
def RecoveryClear (history : (RecoveryProtocol).History) : Prop :=
  ∀ current, history.state = some current → current.execution.application.excluded = ∅

/-- Retain a clear native history, or record departure from the clear region. -/
def nativeStoppedReadout (history : (NativeProtocol).History) :
    Option (NativeProtocol).History := by
  classical
  exact if NativeClear runtime leaks initial horizon scheduler history then some history else none

/-- Retain the entire projected clear recovery history, or record exclusion. -/
def recoveryStoppedReadout (history : (RecoveryProtocol).History) :
    Option (NativeProtocol).History := by
  classical
  exact if clear : RecoveryClear runtime leaks initial horizon scheduler history then
    some (nativeHistory runtime leaks initial horizon scheduler history clear) else none

/-- Retain a clear native history, or label its first public failure by all
failed owners. -/
def nativeClassifiedReadout (history : (NativeProtocol).History) :
    Finset Player ⊕ (NativeProtocol).History := by
  classical
  exact if NativeClear runtime leaks initial horizon scheduler history then .inr history
    else .inl (nativeFailureOwners runtime leaks history.state)

/-- Retain a clear recovery history, or label its first permanent exclusions. -/
def recoveryClassifiedReadout (history : (RecoveryProtocol).History) :
    Finset Player ⊕ (NativeProtocol).History := by
  classical
  exact if clear : RecoveryClear runtime leaks initial horizon scheduler history then
    .inr (nativeHistory runtime leaks initial horizon scheduler history clear)
  else .inl (recoveryFailureOwners runtime leaks history.state)

/-- Actual continuations have the same law of full surviving histories and the
exact first failed-owner set, despite automatic recovery completion at that boundary. -/
theorem runBehavioralUntil_exclusion_classified_eq
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
    (profile : ∀ who, (RecoveryModel).BehavioralPolicy who)
    (nativeCertificate : (NativeProtocol).WellFoundedHistories)
    (recoveryCertificate : (RecoveryProtocol).WellFoundedHistories)
    (history : (RecoveryProtocol).History)
    (current : (runtime.recoveryApplication leaks).Control)
    (state : history.state = some current) (empty : current.execution.application.excluded = ∅) :
    let clear := fun next (same : history.state = some next) =>
      (Option.some.inj (state.symm.trans same)) ▸ empty
    ((NativeModel).runBehavioralUntil nativeCertificate
      (nativeProfile runtime leaks initial horizon scheduler profile)
      (fun history => ¬ NativeClear runtime leaks initial horizon scheduler history)
      (nativeHistory runtime leaks initial horizon scheduler history clear)).map
        (nativeClassifiedReadout runtime leaks initial horizon scheduler) =
    ((RecoveryModel).runBehavioralUntil recoveryCertificate profile
      (fun history => ¬ RecoveryClear runtime leaks initial horizon scheduler history)
      history).map (recoveryClassifiedReadout runtime leaks initial horizon scheduler) := by
  classical
  intro clear
  let related := fun (first : (NativeProtocol).History) (second : (RecoveryProtocol).History) =>
    (∃ current, second.state = some current) ∧
      ((¬ NativeClear runtime leaks initial horizon scheduler first ∧
          ¬ RecoveryClear runtime leaks initial horizon scheduler second ∧
          PairedExclusionRecord runtime leaks first.state second.state) ∨
        ∃ clear : RecoveryClear runtime leaks initial horizon scheduler second,
          first = nativeHistory runtime leaks initial horizon scheduler second clear)
  have clearRecord (second : (RecoveryProtocol).History)
      (clear : RecoveryClear runtime leaks initial horizon scheduler second) :
      NativeClear runtime leaks initial horizon scheduler
        (nativeHistory runtime leaks initial horizon scheduler second clear) :=
    nativeHistory_record runtime leaks initial initialized horizon scheduler second.trace clear
  refine (NativeModel).runBehavioralUntil_map_eq_of_paired_steps (RecoveryModel)
    nativeCertificate recoveryCertificate
    (nativeProfile runtime leaks initial horizon scheduler profile) profile
    (fun history => ¬ NativeClear runtime leaks initial horizon scheduler history)
    (fun history => ¬ RecoveryClear runtime leaks initial horizon scheduler history)
    (nativeClassifiedReadout runtime leaks initial horizon scheduler)
    (recoveryClassifiedReadout runtime leaks initial horizon scheduler) related ?_ ?_ ?_
    _ history ⟨⟨current, state⟩, Or.inr ⟨clear, rfl⟩⟩
  · intro first second linked
    rcases linked.2 with ⟨firstExit, secondExit, _record⟩ | ⟨clear, rfl⟩
    · exact ⟨fun _ => Or.inl secondExit, fun _ => Or.inl firstExit⟩
    · have firstClear := clearRecord second clear
      constructor
      · rintro (bad | ended)
        · exact (bad firstClear).elim
        · exact Or.inr ((terminal_protocolState runtime leaks second.state).mp ended)
      · rintro (bad | ended)
        · exact (bad clear).elim
        · exact Or.inr ((terminal_protocolState runtime leaks second.state).mpr ended)
  · intro first second linked _stopped
    rcases linked.2 with ⟨firstExit, secondExit, record⟩ | ⟨clear, rfl⟩
    · simp only [nativeClassifiedReadout, recoveryClassifiedReadout, firstExit, secondExit,
        ↓reduceIte, ↓reduceDIte]
      exact congrArg Sum.inl (record.failureOwners_eq runtime leaks)
    · simp only [nativeClassifiedReadout, recoveryClassifiedReadout, clearRecord second clear,
        clear, ↓reduceIte, ↓reduceDIte]
  · intro first second linked going running
    obtain ⟨current, currentState⟩ := linked.1
    rcases linked.2 with ⟨firstExit, _secondExit, _record⟩ | ⟨clear, rfl⟩
    · exact (going firstExit).elim
    have secondRunning : ¬ (RecoveryProtocol).terminal second.state :=
      fun ended => running ((terminal_protocolState runtime leaks second.state).mpr ended)
    obtain ⟨paired, firstLaw, secondLaw, preserved⟩ := exists_paired_behavioralStep runtime leaks
      initial horizon scheduler initialized profile second current currentState
      (clear current currentState) secondRunning
    refine ⟨paired, firstLaw, secondLaw, ?_⟩
    intro next supported
    have secondSupported : next.2 ∈
        ((RecoveryModel).runBehavioralFrom profile 1 second).support := by
      rw [← secondLaw, PMF.mem_support_map_iff]
      exact ⟨next, supported, rfl⟩
    obtain ⟨⟨joint, legal, realized⟩, _⟩ := (RecoveryModel).mem_support_runBehavioralFrom_one
      profile secondRunning secondSupported
    change next.2.state ∈ ((runtime.recoveryApplication leaks).transition initial horizon
      scheduler second.state joint).support at realized
    have moved := currentState ▸ realized
    obtain ⟨control, nextState, _recall⟩ :=
      (runtime.recoveryApplication leaks).transition_recall_prefix
      initial horizon scheduler current next.2.state joint moved
    refine ⟨⟨control, nextState⟩, ?_⟩
    by_cases nextClear : RecoveryClear runtime leaks initial horizon scheduler next.2
    · exact Or.inr ⟨nextClear, (preserved next supported).1 nextClear⟩
    · exact Or.inl ⟨fun nativeClear => nextClear ((preserved next supported).2.1 nativeClear),
        nextClear, (preserved next supported).2.2⟩

/-- Collapsing the exact failed-owner labels preserves the law of complete
surviving histories and the single first-exclusion exit atom. -/
theorem runBehavioralUntil_exclusion_map_eq
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
    (profile : ∀ who, (RecoveryModel).BehavioralPolicy who)
    (nativeCertificate : (NativeProtocol).WellFoundedHistories)
    (recoveryCertificate : (RecoveryProtocol).WellFoundedHistories)
    (history : (RecoveryProtocol).History)
    (current : (runtime.recoveryApplication leaks).Control)
    (state : history.state = some current) (empty : current.execution.application.excluded = ∅) :
    let clear := fun next (same : history.state = some next) =>
      (Option.some.inj (state.symm.trans same)) ▸ empty
    ((NativeModel).runBehavioralUntil nativeCertificate
      (nativeProfile runtime leaks initial horizon scheduler profile)
      (fun history => ¬ NativeClear runtime leaks initial horizon scheduler history)
      (nativeHistory runtime leaks initial horizon scheduler history clear)).map
        (nativeStoppedReadout runtime leaks initial horizon scheduler) =
    ((RecoveryModel).runBehavioralUntil recoveryCertificate profile
      (fun history => ¬ RecoveryClear runtime leaks initial horizon scheduler history)
      history).map (recoveryStoppedReadout runtime leaks initial horizon scheduler) := by
  classical
  let collapse : Finset Player ⊕ (NativeProtocol).History → Option (NativeProtocol).History :=
    Sum.elim (fun _ => none) some
  have first : collapse ∘ nativeClassifiedReadout runtime leaks initial horizon scheduler =
      nativeStoppedReadout runtime leaks initial horizon scheduler := by
    funext history
    dsimp only [Function.comp_def, nativeClassifiedReadout, nativeStoppedReadout]
    split_ifs <;> rfl
  have second : collapse ∘ recoveryClassifiedReadout runtime leaks initial horizon scheduler =
      recoveryStoppedReadout runtime leaks initial horizon scheduler := by
    funext history
    dsimp only [Function.comp_def, recoveryClassifiedReadout, recoveryStoppedReadout]
    split_ifs <;> rfl
  have mapped := congrArg (fun law => law.map collapse)
    (runBehavioralUntil_exclusion_classified_eq runtime leaks initial horizon scheduler initialized
      profile nativeCertificate recoveryCertificate history current state empty)
  simpa only [PMF.map_comp, first, second] using mapped

end Vegas.EventGraphRuntime.RecoveryProjection
