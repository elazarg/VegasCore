/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseAttemptControls
import Vegas.Game.PhaseAttemptContinuation
import Vegas.Pending.PhaseRetryCompletion
import Vegas.Pending.PhaseNativeInvariant
import GameTheoryExtensions.Analysis.Protocol.StoppedHistoryInvariant

/-! # Surviving retry endpoints of the original stopped behavioral execution -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (menu : (phaseApplication runtime leaks).ResponseMenu)
  (runtimePlan : RuntimePhasePlan (serviceGraph setup mode))
  (initial : PMF (phaseApplication runtime leaks).State)
  (initialized : ∀ state ∈ initial.support,
    ∃ draw, state = PhaseRuntimeState.initial runtimePlan draw)
  (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "N" => ReactiveApplication.ResponseMenu.information menu initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol menu initial horizon scheduler

include initialized in
/-- Stopping the original native behavioral run at focal exclusion or attempt
exit retains an actual old-attempt completion record at every surviving retry.
The full start history, recall, network and arbitrary continuation policies
are retained; no source posterior or event-success premise is supplied. -/
theorem phase_attempt_boundary_retry_completed
    (profile : ∀ who, (N).BehavioralPolicy who)
    (start : (app).Control) (trace : (E).Trace (some start))
    (owner : Player) (event : (serviceGraph setup mode).EventId)
    (request : start.execution.application.SeedRequest owner
      ⟨start.execution.application.attempt, event⟩)
    (final : (E).History)
    (supported : final ∈ ((N).runBehavioralUntil
      ((menu).bounded initial horizon scheduler).wellFoundedHistories profile
      (fun history => PhaseAttemptExit setup mode runtime leaks owner
        start.execution.application.attempt history.state) ⟨some start, trace⟩).support)
    (retry : PhaseSurvivingRetry setup mode runtime leaks owner
      start.execution.application.attempt final.state) :
    ∃ next : (app).Control, final.state = some next ∧
      ∃ record ∈ next.execution.application.retired,
        record.attempt = start.execution.application.attempt ∧
          event ∈ record.state.config.cut.completed ∧ record.state.ReceiptsComplete ∧
            ¬ record.state.PublicFailure event := by
  classical
  let attempt := start.execution.application.attempt
  let phases := start.execution.application.phases
  let property : (app).ProtocolState → Prop := fun state =>
    ∃ current : (app).Control, state = some current ∧
      (current.execution.application.attempt = attempt →
        current.execution.application.phases = phases) ∧
      (PhaseSurvivingRetry setup mode runtime leaks owner attempt state →
        ∃ record ∈ current.execution.application.retired, record.attempt = attempt ∧
          event ∈ record.state.config.cut.completed ∧ record.state.ReceiptsComplete ∧
            ¬ record.state.PublicFailure event)
  have holds : property (some start) := by
    refine ⟨start, rfl, fun _ => rfl, ?_⟩
    rintro ⟨_survives, changed⟩
    exact (changed rfl).elim
  have preserved : ∀ history : (E).History,
      ¬ PhaseAttemptExit setup mode runtime leaks owner attempt history.state →
      ¬ (E).terminal history.state → ∀ joint (legal : (E).Legal history.state joint) target,
      property history.state → target ∈ ((E).step history.state ⟨joint, legal⟩).support →
        property target := by
    intro history running _notTerminal joint _legal target valid moved
    obtain ⟨current, currentState, phasesKept, _previousRetry⟩ := valid
    have rawTrace := (menu).toRawTrace initial horizon scheduler
      (currentState ▸ history.trace)
    have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
      (fun state member => by
        obtain ⟨draw, rfl⟩ := initialized state member
        exact PhaseRuntimeState.initial_ordered runtimePlan draw) rawTrace
    have coverage := (phaseApplication_failureCoverage runtime leaks).history initial horizon
      scheduler (fun state member => by
        obtain ⟨draw, rfl⟩ := initialized state member
        exact PhaseRuntimeState.initial_failureCoverage runtimePlan draw) rawTrace
    have same : current.execution.application.attempt = attempt := by
      by_contra different
      exact running (currentState ▸ Or.inr different)
    have earlierPhases := phasesKept same
    have realized : target ∈ ((app).transition initial horizon scheduler (some current)
        joint).support := by
      change target ∈ ((app).transition initial horizon scheduler history.state joint).support
        at moved
      simpa only [currentState] using moved
    obtain ⟨next, rfl, _recall⟩ := (app).transition_recall_prefix initial horizon scheduler current
      target joint realized
    refine ⟨next, rfl, ?_, ?_⟩
    · intro sameNext
      have retained := (phaseApplication_sameAttempt_controls runtime leaks).transition initial
        horizon scheduler current next joint realized ordered (same.trans sameNext.symm)
      exact retained.1.trans earlierPhases
    · intro survives
      obtain ⟨phase, installed, inside⟩ := request.2.1
      have installedNow : phase ∈ current.execution.application.phases.head? := by
        simpa only [earlierPhases] using installed
      have result := (phaseApplication_retryCompletion runtime leaks).transition initial horizon
        scheduler current next joint realized coverage.active phase installedNow event inside
          owner request.2.2.2.1 survives.1
      have changed : next.execution.application.generation ≠
          current.execution.application.generation := by
        have generations := congrArg CommitAttemptId.generation same
        exact fun equal => survives.2 (equal.trans generations)
      obtain ⟨record, archived, old, completed, receipts, nonfailure⟩ := result changed
      exact ⟨record, archived, old.trans same, completed, receipts, nonfailure⟩
  have endpoint := (N).runBehavioralUntil_support_closed_of_going
    ((menu).bounded initial horizon scheduler).wellFoundedHistories profile
    (fun history => PhaseAttemptExit setup mode runtime leaks owner attempt history.state)
    property preserved ⟨some start, trace⟩ holds final supported
  obtain ⟨next, shape, _phases, recorded⟩ := endpoint
  exact ⟨next, shape, recorded retry⟩

end Vegas
