module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketLateLumping
public import Vegas.Game.OnePacketLateSuccess
public import Vegas.Game.OnePacketEventPhaseLaw
public import Vegas.Pending.ReactiveAcceptedOutput

@[expose] public section

/-! # Primitive failure at the current native completion stop -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

local notation "menu" => bounds.onePacketMenu timeouts leaks
local notation "N" => onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
  scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol menu (initialLaw setup) horizon
  scheduler

open Classical in
/-- Once the decided event has completed, its primitive failure indicator is
constant under arbitrary terminal continuations. No graph-completion contract
or source terminal readout is used. -/
theorem completed_decisionFailure_terminal_expect
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (start : (E).History) {control : (application setup timeouts leaks).Control}
    (current : start.state = some control) (key : LateKey setup timeouts leaks)
    (event : (graph setup).EventId) (decided : decidedEvent (timeouts := timeouts) key = some event)
    (completed : event ∈ control.execution.application.config.cut.completed) :
    expect ((N).runBehavioralTerminalFrom certificate players start)
      (fun final => if DecisionFailed (timeouts := timeouts) key final.state then (1 : ℝ) else 0) =
        if DecisionFailed (timeouts := timeouts) key start.state then 1 else 0 := by
  obtain ⟨value, read⟩ := Option.isSome_iff_exists.mp
    ((control.execution.application.config.output_available event).mpr completed)
  have stored : control.execution.application.config.store (.inr event) = some value := read
  let property : (application setup timeouts leaks).ProtocolState → Prop := fun state =>
    ∃ next : (application setup timeouts leaks).Control, state = some next ∧
      next.execution.application.config.store (.inr event) = some value
  have closed : ∀ before joint (legal : (E).Legal before joint) after,
      property before → after ∈ ((E).step before ⟨joint, legal⟩).support → property after := by
    rintro before joint legal after ⟨next, rfl, present⟩ reached
    change after ∈ ((application setup timeouts leaks).transition (initialLaw setup) horizon
      scheduler
      (some next) joint).support at reached
    obtain ⟨last, rfl, _⟩ := (application setup timeouts leaks).transition_recall_prefix
      (initialLaw setup)
      horizon scheduler next after joint reached
    refine ⟨last, rfl, ?_⟩
    exact (keepsStore_step timeouts leaks).transition (initialLaw setup) horizon scheduler
      next last joint reached (.inr event) value present
  have remains := (N).runBehavioralTerminalFrom_support_closed certificate players property closed
    start ⟨control, current, stored⟩
  calc _ = expect ((N).runBehavioralTerminalFrom certificate players start)
        (fun _ => if DecisionFailed (timeouts := timeouts) key start.state then (1 : ℝ) else 0)
          := by
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
        have agrees : DecisionFailed (timeouts := timeouts) key final.state ↔ DecisionFailed
          (timeouts := timeouts) key start.state := by
          rw [state, current]
          simp only [DecisionFailed, decided, lastCompleted, completed, true_and, failed]
        rw [agrees]
    _ = _ := expect_constant _ _

local notation "ClearState" => ReactiveApplication.stateInvariant
  (app := application setup timeouts leaks)
    (fun native : EventGraphRuntime.State (graph setup) =>
      EventGraph.Config.defaulted (EventGraphRuntime.State.config native) = ∅)

open Classical in
/-- Under counted clear terminal completeness, the pending event's terminal
failure probability is its probability at the first completion or public failure. -/
theorem pending_failure_terminal_eq_stopped [Finite (E).History]
    (terminalCompletes : ∀ (final : (application setup timeouts leaks).Control),
      ((menu).protocol (initialLaw setup) horizon scheduler).Trace (some final) →
      final.execution.application.config.defaulted = ∅ →
      (application setup timeouts leaks).terminal (some final) →
      final.execution.application.config.cut.Terminal)
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (start : (E).History) {control : (application setup timeouts leaks).Control}
    (current : start.state = some control) {rank : Nat}
    (ordered : control.execution.application.config.cut.IsPrefix rank)
    (clear : control.execution.application.config.defaulted = ∅)
    (key : LateKey setup timeouts leaks) (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event)
    (decided : decidedEvent (timeouts := timeouts) key = some event) :
    expect ((N).runBehavioralTerminalFrom certificate players start)
      (fun final => if DecisionFailed (timeouts := timeouts) key final.state then (1 : ℝ) else 0) =
      expect ((N).runBehavioralUntil certificate players
        (fun stop => LateStopped setup timeouts leaks bounds horizon scheduler rank stop ∨
          ¬ ClearState stop.state) start)
        (fun final => if DecisionFailed (timeouts := timeouts) key final.state then (1 : ℝ) else 0)
          := by
  rw [(N).runBehavioralTerminalFrom_eq_bind_runBehavioralUntil certificate players
    (fun stop => LateStopped setup timeouts leaks bounds horizon scheduler rank stop ∨
      ¬ ClearState stop.state) start, expect_bind_of_finite]
  apply expect_congr_on_support
  intro final supported
  have phaseEq := pending_until_eq_clearUntil (timeouts := timeouts) certificate players start
    current ordered clear event ready
  have lateMember : final ∈ ((N).runBehavioralUntil certificate players
      (LateStopped setup timeouts leaks bounds horizon scheduler rank) start).support := by
    rw [phaseEq]
    exact supported
  obtain ⟨anchor, state, action, primary, sampled, drained⟩ := lateStop_primary_drain
    certificate players ordered ready
      (fun last trace ended same => by
        have lastClear : last.execution.application.config.defaulted = ∅ := by
          rw [same]
          exact clear
        rw [terminalCompletes last trace lastClear ended]
        exact Finset.mem_univ _) start current rfl final lateMember
  have completed : event ∈ anchor.execution.application.config.cut.completed := by
    rw [drained]
    apply EventGraph.Config.Step.path_completed_mono primary.drain_graph_steps
    rw [control.execution.application.config.step_cut event ready action primary.config sampled]
    exact (EventOrder.Cut.mem_complete _ event ready event).mpr (Or.inl rfl)
  exact completed_decisionFailure_terminal_expect (timeouts := timeouts) certificate players final
    state key event decided
    completed


open Classical in
/-- A completed event's persistent failure flag can be measured at
its first completion under counted clear terminal completeness. -/
theorem pending_failure_run_eq_phase [Finite (E).History]
    (terminalCompletes : ∀ (final : (application setup timeouts leaks).Control),
      ((menu).protocol (initialLaw setup) horizon scheduler).Trace (some final) →
      final.execution.application.config.defaulted = ∅ →
      (application setup timeouts leaks).terminal (some final) →
      final.execution.application.config.cut.Terminal)
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (start : (E).History) {control : (application setup timeouts leaks).Control}
    (current : start.state = some control) {rank : Nat}
    (ordered : control.execution.application.config.cut.IsPrefix rank)
    (clear : control.execution.application.config.defaulted = ∅)
    (key : LateKey setup timeouts leaks) (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event)
    (decided : decidedEvent (timeouts := timeouts) key = some event) :
    expect ((N).runBehavioralFrom players (2 * horizon + 1) start)
        (fun final => if DecisionFailed (timeouts := timeouts) key final.state then (1 : ℝ) else
          0) =
      expect ((N).runBehavioralUntil certificate players
        (LateStopped setup timeouts leaks bounds horizon scheduler rank) start)
        (fun final => if DecisionFailed (timeouts := timeouts) key final.state then (1 : ℝ) else 0)
          := by
  rw [← (N).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate
    ((bounds.onePacketMenu timeouts leaks).bounded (initialLaw setup) horizon scheduler),
    pending_failure_terminal_eq_stopped (timeouts := timeouts) terminalCompletes certificate
      players start current ordered clear key event ready decided,
    ← pending_until_eq_clearUntil (timeouts := timeouts) certificate
      players start current ordered clear event ready]


end Vegas
