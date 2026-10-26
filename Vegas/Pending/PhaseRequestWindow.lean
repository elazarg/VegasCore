/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseServiceContract
import Vegas.Pending.PhaseCountMenu
import Vegas.Pending.PhaseReadyResolution
import GameTheoryExtensions.Analysis.Protocol.StoppedHistoryAtom

/-! # Actual stopping windows for a physical request

The completion contract prevents a bounded horizon from cutting off a still-ready
request. The existing stopped evaluator supplies its first absent-request endpoint,
its strict initialized history prefix, and the actual final environment command.
No observation restriction, finite-Nature assumption or source law is imposed.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseService

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (menu : (phaseApplication runtime leaks).ResponseMenu)
  (initial : PMF (PhaseRuntimeState graph)) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "RawMenu" => menu
local notation "P" => ReactiveApplication.ResponseMenu.protocol (RawMenu) initial horizon scheduler
local notation "M" => ReactiveApplication.ResponseMenu.information (RawMenu) initial horizon
  scheduler

/-- Actual bounded play reaches the first loss of an original ready request.
Horizon termination cannot truncate that request, by the physical completion
contract. The entire initialized history and a strict prefix are retained. -/
theorem request_window_reaches_loss
    (completes : CompletesPlay runtime leaks initial horizon scheduler)
    (profile : ∀ who, (M).BehavioralPolicy who)
    (start : (P).History) (control : (app).Control) (atStart : start.state = some control)
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (requested : control.execution.application.SeedRequest owner coordinate)
    (final : (P).History)
    (supported : final ∈ ((M).runBehavioralUntil
      ((RawMenu).bounded initial horizon scheduler).wellFoundedHistories profile
      (fun history => ∀ current, history.state = some current →
        ¬ current.execution.application.SeedRequest owner coordinate) start).support) :
    (∀ current, final.state = some current →
      ¬ current.execution.application.SeedRequest owner coordinate) ∧
      TracePrefix start.trace final.trace ∧ start.trace.length < final.trace.length := by
  let stopped : (P).History → Prop := fun history => ∀ current,
    history.state = some current → ¬ current.execution.application.SeedRequest owner coordinate
  let certificate := ((RawMenu).bounded initial horizon scheduler).wellFoundedHistories
  have halted : stopped final := by
    rcases (M).mem_support_runBehavioralUntil certificate profile stopped start final supported
        with lost | ended
    · exact lost
    · intro current atFinal request
      have trace : ((app).protocol initial horizon scheduler).Trace (some current) :=
        atFinal ▸ (RawMenu).toRawTrace initial horizon scheduler final.trace
      have terminal : (app).terminal (some current) := atFinal ▸ ended
      have completed := completes current trace terminal
      exact request.2.2.1.1 (by rw [completed]; exact Finset.mem_univ _)
  have retained :=
    (M).runBehavioralUntil_support_prefix certificate profile stopped start final
    supported
  have longer : start.trace.length < final.trace.length := by
    apply lt_of_le_of_ne retained.length_le
    intro same
    have equality : start = final := retained.eq_of_length same
    exact halted control (equality ▸ atStart) requested
  exact ⟨halted, retained, longer⟩

/-- The stopped endpoint exposes its actual final environment command and
predecessor. Player responses cannot be the edge that loses a request. -/
theorem request_window_last_environment
    (completes : CompletesPlay runtime leaks initial horizon scheduler)
    (profile : ∀ who, (M).BehavioralPolicy who)
    (start : (P).History) (control : (app).Control) (atStart : start.state = some control)
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (requested : control.execution.application.SeedRequest owner coordinate)
    (final : (P).History) (finalControl : (app).Control)
    (atFinal : final.state = some finalControl)
    (supported : final ∈ ((M).runBehavioralUntil
      ((RawMenu).bounded initial horizon scheduler).wellFoundedHistories profile
      (fun history => ∀ current, history.state = some current →
        ¬ current.execution.application.SeedRequest owner coordinate) start).support) :
    ∃ (before : (app).Control) (prior : (P).Trace (some before)),
      TracePrefix start.trace prior ∧ TracePrefix prior final.trace ∧
      before.actor = none ∧ before.execution.application.SeedRequest owner coordinate ∧
      ¬ finalControl.execution.application.SeedRequest owner coordinate ∧
      ∃ command ∈ (scheduler before.execution.environmentRecall
          (before.execution.observeEnvironment app)).support,
        finalControl.execution ∈ (before.execution.environmentStep app command).support ∧
        finalControl.remaining + 1 = before.remaining ∧
          finalControl.actor = command.actor? app := by
  classical
  let stopped : (P).History → Prop := fun history => ∀ current,
    history.state = some current → ¬ current.execution.application.SeedRequest owner coordinate
  let certificate := ((RawMenu).bounded initial horizon scheduler).wellFoundedHistories
  obtain ⟨lost, retained, longer⟩ := request_window_reaches_loss runtime leaks menu initial
    horizon scheduler completes profile start control atStart owner coordinate requested final
      supported
  obtain ⟨previousState, prior, joint, legal, moved, priorPrefix, finalTrace⟩ :=
    retained.exists_last_transition longer
  have priorFinal : TracePrefix prior final.trace := finalTrace ▸ .extend .refl joint legal moved
  have shorter : prior.length < final.trace.length := by rw [finalTrace]; simp [Trace.length]
  have unhalted := (M).runBehavioralUntil_support_first certificate profile stopped start final
    supported ⟨previousState, prior⟩ priorPrefix priorFinal shorter
  change ¬ ∀ current, previousState = some current →
    ¬ current.execution.application.SeedRequest owner coordinate at unhalted
  push Not at unhalted
  obtain ⟨before, atBefore, wasRequested⟩ := unhalted
  subst previousState
  have lastLost := lost finalControl atFinal
  change final.state ∈ ((app).transition initial horizon scheduler (some before) joint).support
    at moved
  rw [atFinal] at moved
  cases active : before.actor with
  | some actor =>
      simp only [ReactiveApplication.transition, active, PMF.mem_support_pure_iff] at moved
      have executionEq : finalControl.execution = before.execution.respond app actor
          ((joint actor).getD ⟨none⟩) := congrArg ReactiveApplication.Control.execution
        (Option.some.inj moved)
      apply False.elim
      apply lastLost
      rw [executionEq]
      exact respond_request runtime leaks before.execution actor _ owner coordinate wasRequested
  | none =>
      cases remaining : before.remaining with
      | zero => exact (legal.1 (show (app).terminal (some before) from ⟨remaining, active⟩)).elim
      | succ rounds =>
          simp only [ReactiveApplication.transition, active, remaining,
            PMF.mem_support_bind_iff] at moved
          obtain ⟨command, selected, reached⟩ := moved
          obtain ⟨after, stepped, controls⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
          have equal : finalControl = ⟨rounds, command.actor? app, after⟩ :=
            (Option.some.inj controls).symm
          refine ⟨before, prior, priorPrefix, priorFinal, active, wasRequested, lastLost,
            command, selected, ?_, ?_, ?_⟩
          · simpa only [equal] using stepped
          · rw [equal]
            exact remaining.symm
          · rw [equal]

end Vegas.EventGraphRuntime.PhaseService
