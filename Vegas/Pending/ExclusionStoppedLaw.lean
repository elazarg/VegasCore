/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

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
    ExclusionEvidence 0 ∅ (⟨current.execution.application, ∅⟩ : RecoveryState graph)

omit [Fintype Player] in
/-- Native public clearance depends only on the complete endpoint state. -/
theorem nativeClear_iff_stateInvariant (history : (NativeProtocol).History) :
    NativeClear runtime leaks initial horizon scheduler history ↔
      ReactiveApplication.stateInvariant (app := runtime.reactiveApplication leaks)
        (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅)) history.state := by
  cases state : history.state with
  | none => simp [NativeClear, state, ReactiveApplication.stateInvariant]
  | some current =>
    constructor
    · intro clear
      exact clear current state
    · intro clear found same
      cases Option.some.inj (state.symm.trans same)
      exact clear

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

/-- Corresponding clear stopping conditions preserve the full surviving history
and exact first failed-owner set, including automatic recovery completion at exit. -/
theorem runBehavioralUntil_exclusion_or_classified_eq
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
    (profile : ∀ who, (RecoveryModel).BehavioralPolicy who)
    (nativeCertificate : (NativeProtocol).WellFoundedHistories)
    (recoveryCertificate : (RecoveryProtocol).WellFoundedHistories)
    (nativeStop : (NativeProtocol).History → Prop)
    (recoveryStop : (RecoveryProtocol).History → Prop)
    (stopAgrees : ∀ history (clear : RecoveryClear runtime leaks initial horizon scheduler history),
      nativeStop (nativeHistory runtime leaks initial horizon scheduler history clear) ↔
        recoveryStop history)
    (history : (RecoveryProtocol).History)
    (clear : RecoveryClear runtime leaks initial horizon scheduler history) :
    ((NativeModel).runBehavioralUntil nativeCertificate
      (nativeProfile runtime leaks initial horizon scheduler profile)
      (fun history => ¬ NativeClear runtime leaks initial horizon scheduler history ∨
        nativeStop history)
      (nativeHistory runtime leaks initial horizon scheduler history clear)).map
        (nativeClassifiedReadout runtime leaks initial horizon scheduler) =
    ((RecoveryModel).runBehavioralUntil recoveryCertificate profile
      (fun history => ¬ RecoveryClear runtime leaks initial horizon scheduler history ∨
        recoveryStop history)
      history).map (recoveryClassifiedReadout runtime leaks initial horizon scheduler) := by
  classical
  let related := fun (first : (NativeProtocol).History) (second : (RecoveryProtocol).History) =>
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
    (fun history => ¬ NativeClear runtime leaks initial horizon scheduler history ∨
      nativeStop history)
    (fun history => ¬ RecoveryClear runtime leaks initial horizon scheduler history ∨
      recoveryStop history)
    (nativeClassifiedReadout runtime leaks initial horizon scheduler)
    (recoveryClassifiedReadout runtime leaks initial horizon scheduler) related ?_ ?_ ?_
    _ history (Or.inr ⟨clear, rfl⟩)
  · intro first second linked
    rcases linked with ⟨firstExit, secondExit, _record⟩ | ⟨clear, rfl⟩
    · exact ⟨fun _ => Or.inl (Or.inl secondExit), fun _ => Or.inl (Or.inl firstExit)⟩
    · have firstClear := clearRecord second clear
      constructor
      · rintro ((bad | stopped) | ended)
        · exact (bad firstClear).elim
        · exact Or.inl (Or.inr ((stopAgrees second clear).mp stopped))
        · exact Or.inr ((terminal_protocolState runtime leaks second.state).mp ended)
      · rintro ((bad | stopped) | ended)
        · exact (bad clear).elim
        · exact Or.inl (Or.inr ((stopAgrees second clear).mpr stopped))
        · exact Or.inr ((terminal_protocolState runtime leaks second.state).mpr ended)
  · intro first second linked _stopped
    rcases linked with ⟨firstExit, secondExit, record⟩ | ⟨clear, rfl⟩
    · simp only [nativeClassifiedReadout, recoveryClassifiedReadout, firstExit, secondExit,
        ↓reduceIte, ↓reduceDIte]
      exact congrArg Sum.inl (record.failureOwners_eq runtime leaks)
    · simp only [nativeClassifiedReadout, recoveryClassifiedReadout, clearRecord second clear,
        clear, ↓reduceIte, ↓reduceDIte]
  · intro first second linked going running
    rcases linked with ⟨firstExit, _secondExit, _record⟩ | ⟨clear, rfl⟩
    · exact (going (Or.inl firstExit)).elim
    have secondRunning : ¬ (RecoveryProtocol).terminal second.state :=
      fun ended => running ((terminal_protocolState runtime leaks second.state).mpr ended)
    obtain ⟨paired, firstLaw, secondLaw, preserved⟩ := exists_paired_behavioralStep runtime leaks
      initial horizon scheduler initialized profile second clear secondRunning
    refine ⟨paired, firstLaw, secondLaw, ?_⟩
    intro next supported
    by_cases nextClear : RecoveryClear runtime leaks initial horizon scheduler next.2
    · exact Or.inr ⟨nextClear, (preserved next supported).1 nextClear⟩
    · exact Or.inl ⟨fun nativeClear => nextClear ((preserved next supported).2.1 nativeClear),
        nextClear, (preserved next supported).2.2⟩

/-- Actual continuations have the same law of full surviving histories and the
exact first failed-owner set, despite automatic recovery completion at that boundary. -/
theorem runBehavioralUntil_exclusion_classified_eq
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
    (profile : ∀ who, (RecoveryModel).BehavioralPolicy who)
    (nativeCertificate : (NativeProtocol).WellFoundedHistories)
    (recoveryCertificate : (RecoveryProtocol).WellFoundedHistories)
    (history : (RecoveryProtocol).History)
    (clear : RecoveryClear runtime leaks initial horizon scheduler history) :
    ((NativeModel).runBehavioralUntil nativeCertificate
      (nativeProfile runtime leaks initial horizon scheduler profile)
      (fun history => ¬ NativeClear runtime leaks initial horizon scheduler history)
      (nativeHistory runtime leaks initial horizon scheduler history clear)).map
        (nativeClassifiedReadout runtime leaks initial horizon scheduler) =
    ((RecoveryModel).runBehavioralUntil recoveryCertificate profile
      (fun history => ¬ RecoveryClear runtime leaks initial horizon scheduler history)
      history).map (recoveryClassifiedReadout runtime leaks initial horizon scheduler) := by
  classical
  simpa only [or_false] using
    runBehavioralUntil_exclusion_or_classified_eq runtime leaks initial horizon scheduler
      initialized profile nativeCertificate recoveryCertificate (fun _ => False) (fun _ => False)
      (fun _ _ => Iff.rfl) history clear

/-- Collapsing the exact failed-owner labels preserves the law of complete
surviving histories and the single first-exclusion exit atom. -/
theorem runBehavioralUntil_exclusion_map_eq
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
    (profile : ∀ who, (RecoveryModel).BehavioralPolicy who)
    (nativeCertificate : (NativeProtocol).WellFoundedHistories)
    (recoveryCertificate : (RecoveryProtocol).WellFoundedHistories)
    (history : (RecoveryProtocol).History)
    (clear : RecoveryClear runtime leaks initial horizon scheduler history) :
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
      profile nativeCertificate recoveryCertificate history clear)
  simpa only [PMF.map_comp, first, second] using mapped

end Vegas.EventGraphRuntime.RecoveryProjection
