/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryPendingCompletion

/-! # Primitive failure at the current recovery completion boundary -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

local notation "menu" => bounds.onePacketMenu runtime leaks
local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol menu (initialLaw setup) horizon
  scheduler

open Classical in
/-- Once the decided event has completed, its primitive failure indicator is
constant under arbitrary terminal continuations. No graph-completion contract
or source terminal readout is used. -/
theorem completed_decisionFailure_terminal_expect
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (start : (E).History) {control : (application setup runtime leaks).Control}
    (current : start.state = some control) (key : LateKey setup runtime leaks)
    (event : (graph setup).EventId) (decided : decidedEvent (runtime := runtime) key = some event)
    (completed : event ∈ control.execution.application.config.cut.completed) :
    expect ((N).runBehavioralTerminalFrom certificate players start)
      (fun final => if DecisionFailed (runtime := runtime) key final.state then (1 : ℝ) else 0) =
        if DecisionFailed (runtime := runtime) key start.state then 1 else 0 := by
  obtain ⟨value, read⟩ := Option.isSome_iff_exists.mp
    ((control.execution.application.config.output_available event).mpr completed)
  have stored : control.execution.application.config.store (.inr event) = some value := read
  let property : (application setup runtime leaks).ProtocolState → Prop := fun state =>
    ∃ next : (application setup runtime leaks).Control, state = some next ∧
      next.execution.application.config.store (.inr event) = some value
  have closed : ∀ before joint (legal : (E).Legal before joint) after,
      property before → after ∈ ((E).step before ⟨joint, legal⟩).support → property after := by
    rintro before joint legal after ⟨next, rfl, present⟩ reached
    change after ∈ ((application setup runtime leaks).transition (initialLaw setup) horizon
      scheduler
      (some next) joint).support at reached
    obtain ⟨last, rfl, _⟩ := (application setup runtime leaks).transition_recall_prefix
      (initialLaw setup)
      horizon scheduler next after joint reached
    refine ⟨last, rfl, ?_⟩
    rcases transition_configStep (initialLaw setup) horizon scheduler next
      last joint reached with
      same | ⟨completedEvent, ready, action, sampled⟩
    · rw [same]
      exact present
    · exact next.execution.application.config.step_store_of_some last.execution.application.config
        completedEvent ready action sampled (.inr event) value present
  have remains := (N).runBehavioralTerminalFrom_support_closed certificate players property closed
    start ⟨control, current, stored⟩
  calc _ = expect ((N).runBehavioralTerminalFrom certificate players start)
        (fun _ => if DecisionFailed (runtime := runtime) key start.state then (1 : ℝ) else 0) := by
        apply expect_congr_on_support
        intro final member
        obtain ⟨last, state, output⟩ := remains final member
        have lastCompleted : event ∈ last.execution.application.config.cut.completed := by
          apply (last.execution.application.config.output_available event).mp
          change (last.execution.application.config.store (.inr event)).isSome
          rw [output]
          rfl
        have storeEq : last.execution.application.config.store (.inr event) =
            control.execution.application.config.store (.inr event) := output.trans stored.symm
        have failed : StoreEventFailed last.execution.application.config.store event ↔
            StoreEventFailed control.execution.application.config.store event := by
          simp only [StoreEventFailed, storeEq]
        have agrees : DecisionFailed (runtime := runtime) key final.state ↔ DecisionFailed
          (runtime := runtime) key start.state := by
          rw [state, current]
          simp only [DecisionFailed, decided, lastCompleted, completed, true_and, failed]
        rw [agrees]
    _ = _ := expect_constant _ _

local notation "ClearState" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk
    native ∅))

open Classical in
/-- Under counted clear terminal completeness, the pending event's terminal
failure probability is its probability at the first completion or public failure. -/
theorem pending_failure_terminal_eq_stopped [Finite (E).History]
    (terminalCompletes : ∀ (final : (application setup runtime leaks).Control),
      ((menu).protocol (initialLaw setup) horizon scheduler).Trace (some final) →
      ExclusionEvidence 0 ∅ (⟨final.execution.application, ∅⟩ : RecoveryState (graph setup)) →
      (application setup runtime leaks).terminal (some final) →
      final.execution.application.config.cut.Terminal)
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (start : (E).History) {control : (application setup runtime leaks).Control}
    (current : start.state = some control) {rank : Nat}
    (ordered : control.execution.application.config.cut.IsPrefix rank)
    (clear : ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅))
    (key : LateKey setup runtime leaks) (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event)
    (decided : decidedEvent (runtime := runtime) key = some event) :
    expect ((N).runBehavioralTerminalFrom certificate players start)
      (fun final => if DecisionFailed (runtime := runtime) key final.state then (1 : ℝ) else 0) =
      expect ((N).runBehavioralUntil certificate players
        (fun stop => LateStopped setup runtime leaks bounds horizon scheduler rank stop ∨
          ¬ ClearState stop.state) start)
        (fun final => if DecisionFailed (runtime := runtime) key final.state then (1 : ℝ) else 0)
          := by
  rw [(N).runBehavioralTerminalFrom_eq_bind_runBehavioralUntil certificate players
    (fun stop => LateStopped setup runtime leaks bounds horizon scheduler rank stop ∨
      ¬ ClearState stop.state) start, expect_bind_of_finite]
  apply expect_congr_on_support
  intro final supported
  obtain ⟨anchor, state, completed, _ordered, _seen⟩ := pending_stop_completed (runtime :=
    runtime) terminalCompletes
    true certificate players start current ordered clear event ready final supported
  exact completed_decisionFailure_terminal_expect (runtime := runtime) certificate players final
    state key event decided
    completed

section Recovery

variable {initial : PMF (RecoveryState (graph setup))}
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (RecoveryState.mk (State.initial inputs) ∅ : RecoveryState (graph setup)))
  (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
  {recoveryScheduler : (recoveryApplication runtime leaks).Scheduler}
  (completes : Recovery.CompletesPlay runtime leaks initial horizon recoveryScheduler)

local notation "nativeScheduler" => RecoveryProjection.nativeScheduler runtime leaks
  recoveryScheduler
local notation "Native" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
  nativeScheduler
local notation "Protocol" => ReactiveApplication.ResponseMenu.protocol menu (initialLaw setup)
  horizon nativeScheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk
    native ∅))

include initialized nativeLaw completes in
open Classical in
/-- The primitive failure probability of the pending event can be evaluated at
its next completion boundary instead of at the end of native play. The only
completion premise concerns the actual recovery runtime. -/
theorem recovery_pending_failure_terminal_eq_stopped [Finite (Protocol).History]
    (certificate : (Protocol).WellFoundedHistories)
    (players : ∀ player, (Native).BehavioralPolicy player)
    (start : (Protocol).History) {control : (application setup runtime leaks).Control}
    (current : start.state = some control) {rank : Nat}
    (ordered : control.execution.application.config.cut.IsPrefix rank)
    (clear : ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅))
    (key : LateKey setup runtime leaks) (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event)
    (decided : decidedEvent (runtime := runtime) key = some event) :
    expect ((Native).runBehavioralTerminalFrom certificate players start)
      (fun final => if DecisionFailed (runtime := runtime) key final.state then (1 : ℝ) else 0) =
      expect ((Native).runBehavioralUntil certificate players
        (fun stop => LateStopped setup runtime leaks bounds horizon nativeScheduler rank stop ∨
          ¬ Clear stop.state) start)
        (fun final => if DecisionFailed (runtime := runtime) key final.state then (1 : ℝ) else 0)
          := by
  apply pending_failure_terminal_eq_stopped (runtime := runtime) ?_ certificate players start
    current ordered clear key
    event ready decided
  exact Recovery.CompletesPlay.clear_counted_native (runtime := runtime) bounds initialized
    nativeLaw completes


end Recovery

end Vegas
