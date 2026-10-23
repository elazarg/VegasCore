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
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

local notation "menu" => bounds.onePacketMenu (runtime setup) leaks
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol menu (initialLaw setup) horizon
  scheduler

open Classical in
/-- Once the decided event has completed, its primitive failure indicator is
constant under arbitrary terminal continuations. No graph-completion contract
or source terminal readout is used. -/
theorem completed_decisionFailure_terminal_expect
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (start : (E).History) {control : (application setup leaks).Control}
    (current : start.state = some control) (key : LateKey setup leaks)
    (event : (graph setup).EventId) (decided : decidedEvent key = some event)
    (completed : event ∈ control.execution.application.config.cut.completed) :
    expect ((N).runBehavioralTerminalFrom certificate players start)
      (fun final => if DecisionFailed key final.state then (1 : ℝ) else 0) =
        if DecisionFailed key start.state then 1 else 0 := by
  obtain ⟨value, read⟩ := Option.isSome_iff_exists.mp
    ((control.execution.application.config.output_available event).mpr completed)
  have stored : control.execution.application.config.store (.inr event) = some value := read
  let property : (application setup leaks).ProtocolState → Prop := fun state =>
    ∃ next : (application setup leaks).Control, state = some next ∧
      next.execution.application.config.store (.inr event) = some value
  have closed : ∀ before joint (legal : (E).Legal before joint) after,
      property before → after ∈ ((E).step before ⟨joint, legal⟩).support → property after := by
    rintro before joint legal after ⟨next, rfl, present⟩ reached
    change after ∈ ((application setup leaks).transition (initialLaw setup) horizon scheduler
      (some next) joint).support at reached
    obtain ⟨last, rfl, _⟩ := (application setup leaks).transition_recall_prefix (initialLaw setup)
      horizon scheduler next after joint reached
    refine ⟨last, rfl, ?_⟩
    rcases transition_configStep (initialLaw setup) horizon scheduler next last joint reached with
      same | ⟨completedEvent, ready, action, sampled⟩
    · rw [same]
      exact present
    · exact next.execution.application.config.step_store_of_some last.execution.application.config
        completedEvent ready action sampled (.inr event) value present
  have remains := (N).runBehavioralTerminalFrom_support_closed certificate players property closed
    start ⟨control, current, stored⟩
  calc _ = expect ((N).runBehavioralTerminalFrom certificate players start)
        (fun _ => if DecisionFailed key start.state then (1 : ℝ) else 0) := by
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
        have agrees : DecisionFailed key final.state ↔ DecisionFailed key start.state := by
          rw [state, current]
          simp only [DecisionFailed, decided, lastCompleted, completed, true_and, failed]
        rw [agrees]
    _ = _ := expect_constant _ _

section Recovery

variable {initial : PMF (RecoveryState (graph setup))}
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (RecoveryState.mk (State.initial inputs) ∅ : RecoveryState (graph setup)))
  (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
  {recoveryScheduler : (recoveryApplication (runtime setup) leaks).Scheduler}
  (completes : Recovery.CompletesPlay (runtime setup) leaks initial horizon recoveryScheduler)

local notation "nativeScheduler" => RecoveryProjection.nativeScheduler (runtime setup) leaks
  recoveryScheduler
local notation "Native" => onePacketModel setup leaks bounds (initialLaw setup) horizon
  nativeScheduler
local notation "Protocol" => ReactiveApplication.ResponseMenu.protocol menu (initialLaw setup)
  horizon nativeScheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => PublicExclusionRecord (RecoveryState.mk native ∅))

include initialized nativeLaw completes in
open Classical in
/-- The primitive failure probability of the pending event can be evaluated at
its next completion boundary instead of at the end of native play. The only
completion premise concerns the actual recovery runtime. -/
theorem recovery_pending_failure_terminal_eq_stopped [Finite (Protocol).History]
    (certificate : (Protocol).WellFoundedHistories)
    (players : ∀ player, (Native).BehavioralPolicy player)
    (start : (Protocol).History) {control : (application setup leaks).Control}
    (current : start.state = some control) {rank : Nat}
    (ordered : control.execution.application.config.cut.IsPrefix rank)
    (clear : PublicExclusionRecord (RecoveryState.mk control.execution.application ∅))
    (key : LateKey setup leaks) (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event)
    (decided : decidedEvent key = some event) :
    expect ((Native).runBehavioralTerminalFrom certificate players start)
      (fun final => if DecisionFailed key final.state then (1 : ℝ) else 0) =
      expect ((Native).runBehavioralUntil certificate players
        (fun stop => LateStopped setup leaks bounds horizon nativeScheduler rank stop ∨
          ¬ Clear stop.state) start)
        (fun final => if DecisionFailed key final.state then (1 : ℝ) else 0) := by
  rw [(Native).runBehavioralTerminalFrom_eq_bind_runBehavioralUntil certificate players
    (fun stop => LateStopped setup leaks bounds horizon nativeScheduler rank stop ∨
      ¬ Clear stop.state) start, expect_bind_of_finite]
  apply expect_congr_on_support
  intro final supported
  obtain ⟨anchor, state, completed, _ordered, _seen⟩ := recovery_pending_stop_completed initialized
    nativeLaw completes true certificate players start current ordered clear event ready final
      supported
  exact completed_decisionFailure_terminal_expect certificate players final state key event decided
    completed

end Recovery

end Vegas
