/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionClearHistory

/-! # Complete information fibers before public exclusion -/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

def information : (runtime.recoveryApplication leaks).Info →
    (runtime.reactiveApplication leaks).Info :=
  Option.map fun input =>
    (input.1.map (playerEntry runtime leaks), playerView runtime leaks input.2)

def liftInformation : (runtime.reactiveApplication leaks).Info →
    (runtime.recoveryApplication leaks).Info :=
  Option.map fun input =>
    (input.1.map (liftPlayerEntry runtime leaks), liftPlayerView runtime leaks input.2)

@[simp] theorem information_liftInformation
    (input : (runtime.reactiveApplication leaks).Info) :
    information runtime leaks (liftInformation runtime leaks input) = input := by
  cases input with
  | none => rfl
  | some input =>
    rcases input with ⟨past, view⟩
    simp only [information, liftInformation, Option.map_some, List.map_map, Function.comp_def,
      playerEntry_liftPlayerEntry, playerView_liftPlayerView, List.map_id_fun', id_eq]

theorem observe_projection (who : Player)
    (state : (runtime.recoveryApplication leaks).ProtocolState) :
    (runtime.reactiveApplication leaks).observe who (protocolState runtime leaks state) =
      information runtime leaks ((runtime.recoveryApplication leaks).observe who state) := by
  cases state with
  | none => rfl
  | some current =>
    by_cases active : current.actor = some who <;>
      simp only [ReactiveApplication.observe, protocolState, Option.map_some, control,
        active, ↓reduceIte, information, Option.map_none, execution]
    rfl

theorem observe_lift (who : Player)
    (state : (runtime.reactiveApplication leaks).ProtocolState) :
    (runtime.recoveryApplication leaks).observe who (liftProtocolState runtime leaks state) =
      liftInformation runtime leaks ((runtime.reactiveApplication leaks).observe who state) := by
  cases state with
  | none => rfl
  | some current =>
    by_cases active : current.actor = some who <;>
      simp only [ReactiveApplication.observe, liftProtocolState, Option.map_some, liftControl,
        active, ↓reduceIte, liftInformation, Option.map_none, liftExecution]
    rfl

theorem infoOf_nativeHistory (initial : PMF (RecoveryState graph)) (horizon : Nat)
    (scheduler : (runtime.recoveryApplication leaks).Scheduler)
    (history : ((runtime.recoveryApplication leaks).protocol initial horizon scheduler).History)
    (clear : ∀ current, history.state = some current →
      current.execution.application.excluded = ∅) (who : Player) :
    ((runtime.reactiveApplication leaks).information (initial.map RecoveryState.native) horizon
        (nativeScheduler runtime leaks scheduler)).infoOf who
        (nativeHistory runtime leaks initial horizon scheduler history clear).trace =
      information runtime leaks (((runtime.recoveryApplication leaks).information initial horizon
        scheduler).infoOf who history.trace) := by
  simp only [ReactiveApplication.information, ReactiveApplication.info]
  exact observe_projection runtime leaks who history.state

theorem infoOf_recoveryHistory (initial : PMF (RecoveryState graph))
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
    (horizon : Nat) (scheduler : (runtime.recoveryApplication leaks).Scheduler)
    (history : ((runtime.reactiveApplication leaks).protocol (initial.map RecoveryState.native)
      horizon (nativeScheduler runtime leaks scheduler)).History)
    (clear : ∀ current, history.state = some current →
      PublicExclusionRecord (⟨current.execution.application, ∅⟩ : RecoveryState graph))
    (who : Player) :
    ((runtime.recoveryApplication leaks).information initial horizon scheduler).infoOf who
        (recoveryHistory runtime leaks initial initialized horizon scheduler history clear).trace =
      liftInformation runtime leaks (((runtime.reactiveApplication leaks).information
        (initial.map RecoveryState.native) horizon (nativeScheduler runtime leaks scheduler)).infoOf
          who history.trace) := by
  simp only [ReactiveApplication.information, ReactiveApplication.info]
  exact observe_lift runtime leaks who history.state

theorem informationFiber_clear (who : Player)
    (reference : (runtime.reactiveApplication leaks).Control)
    (active : reference.actor = some who)
    (state : (runtime.recoveryApplication leaks).ProtocolState)
    (same : (runtime.recoveryApplication leaks).observe who state =
      liftInformation runtime leaks ((runtime.reactiveApplication leaks).observe who
        (some reference))) :
    ∀ current, state = some current → current.execution.application.excluded = ∅ := by
  intro current currentEq
  subst state
  simp only [ReactiveApplication.observe, active, ↓reduceIte, liftInformation, Option.map_some]
    at same
  split at same
  · have viewEq := congrArg (fun input => input.2.application.2) (Option.some.inj same)
    exact viewEq
  · cases same

theorem informationFiber_record (initial : PMF (RecoveryState graph))
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
    (horizon : Nat) (scheduler : (runtime.recoveryApplication leaks).Scheduler)
    (who : Player) (reference : (runtime.reactiveApplication leaks).Control)
    (active : reference.actor = some who)
    (valid : PublicExclusionRecord (⟨reference.execution.application, ∅⟩ : RecoveryState graph))
    (history : ((runtime.reactiveApplication leaks).protocol (initial.map RecoveryState.native)
      horizon (nativeScheduler runtime leaks scheduler)).History)
    (same : (runtime.reactiveApplication leaks).observe who history.state =
      (runtime.reactiveApplication leaks).observe who (some reference)) :
    ∀ current, history.state = some current →
      PublicExclusionRecord (⟨current.execution.application, ∅⟩ : RecoveryState graph) := by
  intro current currentEq
  have receipts := native_receiptsComplete_history runtime leaks
    (initial.map RecoveryState.native) (by
      intro native supported
      rw [PMF.mem_support_map_iff] at supported
      obtain ⟨state, sourceSupported, rfl⟩ := supported
      obtain ⟨inputs, rfl⟩ := initialized state sourceSupported
      exact ⟨inputs, rfl⟩) horizon (nativeScheduler runtime leaks scheduler) history.trace
  rw [currentEq] at receipts same
  simp only [ReactiveApplication.observe, active, ↓reduceIte] at same
  split at same
  · have samePublic := congrArg (fun input => input.2.application.publicView)
      (Option.some.inj same)
    change current.execution.application.publicView = reference.execution.application.publicView
      at samePublic
    refine ⟨receipts, fun owner => ⟨?_, ?_⟩⟩
    · intro member
      exact (Finset.notMem_empty owner member).elim
    · rintro ⟨event, acting, failed⟩
      exact (valid.excluded owner).mpr ⟨event, acting,
        (State.PublicFailure.of_publicView_eq samePublic event).mp failed⟩
  · cases same

/-- Every history in either complete information fiber lies before public
exclusion. Native projection and clear lifting therefore give a bijection of
the full fibers, including histories with zero strategy probability. -/
def informationHistoryEquiv (initial : PMF (RecoveryState graph))
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
    (horizon : Nat) (scheduler : (runtime.recoveryApplication leaks).Scheduler)
    (who : Player) (reference : (runtime.reactiveApplication leaks).Control)
    (active : reference.actor = some who)
    (valid : PublicExclusionRecord (⟨reference.execution.application, ∅⟩ : RecoveryState graph)) :
    (((runtime.recoveryApplication leaks).information initial horizon scheduler).InformationHistory
      who (liftInformation runtime leaks
        ((runtime.reactiveApplication leaks).observe who (some reference)))) ≃
    (((runtime.reactiveApplication leaks).information (initial.map RecoveryState.native) horizon
      (nativeScheduler runtime leaks scheduler)).InformationHistory who
        ((runtime.reactiveApplication leaks).observe who (some reference))) where
  toFun history := by
    have same := history.2
    simp only [ReactiveApplication.information, ReactiveApplication.info] at same
    have clear := informationFiber_clear runtime leaks who reference active history.1.state same
    refine ⟨nativeHistory runtime leaks initial horizon scheduler history.1 clear, ?_⟩
    rw [infoOf_nativeHistory, history.2, information_liftInformation]
  invFun history := by
    have same := history.2
    simp only [ReactiveApplication.information, ReactiveApplication.info] at same
    have clear := informationFiber_record runtime leaks initial initialized horizon scheduler who
      reference active valid history.1 same
    refine ⟨recoveryHistory runtime leaks initial initialized horizon scheduler history.1 clear, ?_⟩
    rw [infoOf_recoveryHistory, history.2]
  left_inv history := by
    apply Subtype.ext
    exact recoveryHistory_nativeHistory runtime leaks initial initialized horizon scheduler
      history.1.trace (informationFiber_clear runtime leaks who reference active history.1.state
        (by simpa only [ReactiveApplication.information, ReactiveApplication.info] using history.2))
  right_inv history := by
    apply Subtype.ext
    exact nativeHistory_recoveryHistory runtime leaks initial initialized horizon scheduler
      history.1.trace (informationFiber_record runtime leaks initial initialized horizon scheduler
        who
        reference active valid history.1
        (by simpa only [ReactiveApplication.information, ReactiveApplication.info] using history.2))

end Vegas.EventGraphRuntime.RecoveryProjection
