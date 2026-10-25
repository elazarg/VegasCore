/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseTraceProjection
import Vegas.Game.SequentialPhaseCountedMenu
import Vegas.Pending.PhaseResponseAliases
import Interaction.ReactiveMenuRestriction

/-! # Actual canonical counted traces projected to recovery counted traces

Operational normalization supplies a genuine subgame of the phase counted menu.
Every actual clear trace of this subgame projects, callback by callback, to the
recovery counted game with identical length and complete projected endpoint.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph)

/-- Normalizing admitted counted choices retains their actual counted-menu admission. -/
theorem normalized_onePacket_included :
    ((normalization runtime leaks).menu (onePacketMenu runtime leaks bounds)).IncludedIn
      (onePacketMenu runtime leaks bounds) := by
  intro who past view response member
  obtain ⟨original, admitted, rfl⟩ :=
    (ReactiveApplication.SubmissionNormalization.menu_mem _ _ _ _ _ _).mp member
  exact onePacketMenu_closed runtime leaks bounds who past view original admitted

end PhaseCount

namespace PhaseRecoveryProjection

open SourceProgram EventGraph Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)
  (runtime : EventGraphRuntime ((toEventGraph program).withMode .sequential))
  (leaks : MessageNetwork.ObservationRule Player
    (CommitAttemptPacket ((toEventGraph program).withMode .sequential)))
  (bounds : MessageBounds ((toEventGraph program).withMode .sequential))

local notation "plan" => sequentialRuntimePhasePlan program
local notation "recoveryLeaks" => PhaseNativeProjection.nativeLeaks leaks plan
local notation "P" => phaseApplication runtime leaks
local notation "R" => recoveryApplication runtime recoveryLeaks
local notation "raw" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "normal" => PhaseCount.normalization runtime leaks
local notation "canonical" =>
  ReactiveApplication.SubmissionNormalization.menu (normal) (raw)
local notation "included" => PhaseCount.normalized_onePacket_included runtime leaks bounds
local notation "projection" => protocolState runtime leaks recoveryLeaks
local notation "recoveryScheduler" =>
  SequentialPhaseSchedulerInformation.scheduler program runtime leaks recoveryLeaks
local notation "phaseInitial" => PMF.map (PhaseRuntimeState.initial plan)
local notation "recoveryInitial" =>
  PMF.map (fun input => RecoveryState.mk (State.initial input) ∅)
local notation "RecoveryMenu" => Recovery.onePacketMenu runtime recoveryLeaks bounds

/-- Every canonical legal joint at an actual clear prefix is a legal recovery counted joint. -/
theorem legal_projected_canonical_clear
    (inputs : PMF ((toEventGraph program).withMode .sequential).Inputs) (horizon : Nat)
    (scheduler : (P).Scheduler) {state : (P).ProtocolState}
    (prior : ((canonical).protocol (phaseInitial inputs) horizon scheduler).Trace state)
    (clear : ReactiveApplication.stateInvariant
      (fun state : PhaseRuntimeState ((toEventGraph program).withMode .sequential) =>
        state.current.excluded = ∅) state)
    (joint : Player → Option (P).Action)
    (legal : ((canonical).protocol (phaseInitial inputs) horizon scheduler).Legal state joint) :
    ((RecoveryMenu).protocol (recoveryInitial inputs) horizon (recoveryScheduler scheduler)).Legal
      (projection state) (jointActions runtime leaks recoveryLeaks joint) := by
  have rawLegal := legal_projected_raw runtime leaks recoveryLeaks (phaseInitial inputs)
    (recoveryInitial inputs) horizon scheduler (recoveryScheduler scheduler) state joint
    ((canonical).legal_raw _ _ _ legal)
  refine ⟨rawLegal.1, fun who => ?_⟩
  have player := legal.2 who
  have projected := rawLegal.2 who
  cases selected : joint who with
  | none =>
      simpa only [jointActions, selected, Option.map_none, ReactiveApplication.protocol,
        ReactiveApplication.ResponseMenu.protocol] using projected
  | some response =>
      simp only [jointActions, selected, Option.map_some] at projected ⊢
      refine ⟨projected.1, ?_⟩
      cases state with
      | none => exact Set.mem_univ _
      | some current =>
          rw [selected] at player
          have member : response ∈ (canonical).actions who (current.execution.recall who)
              (current.execution.observe (P) who) := player.2
          have counted := (included).trace (phaseInitial inputs) horizon scheduler prior
          have admitted := (included) who _ _ member
          have fixed := (normal).menu_normal (raw) who (current.execution.recall who)
            (current.execution.observe (P) who) response member
          exact recovery_onePacket_mem_of_normal_phase_history program runtime leaks recoveryLeaks
            bounds inputs horizon scheduler counted clear who response admitted fixed

/-- Every canonical counted clear phase trace has an actual recovery counted trace,
without postulating that recovery trace or a final distribution as an adapter premise. -/
theorem trace_projected_canonical_clear
    (inputs : PMF ((toEventGraph program).withMode .sequential).Inputs) (horizon : Nat)
    (scheduler : (P).Scheduler) {state : (P).ProtocolState}
    (trace : ((canonical).protocol (phaseInitial inputs) horizon scheduler).Trace state)
    (clear : ReactiveApplication.stateInvariant
      (fun state : PhaseRuntimeState ((toEventGraph program).withMode .sequential) =>
        state.current.excluded = ∅) state) :
    ∃ projected : ((RecoveryMenu).protocol (recoveryInitial inputs) horizon
      (recoveryScheduler scheduler)).Trace (projection state), projected.length = trace.length := by
  have origin : ∀ {state}
      (history : ((canonical).protocol (phaseInitial inputs) horizon scheduler).Trace state),
      ReactiveApplication.stateInvariant
        (fun state : PhaseRuntimeState ((toEventGraph program).withMode .sequential) =>
          state.current.excluded = ∅) state →
      ∃ projected : ((RecoveryMenu).protocol (recoveryInitial inputs) horizon
        (recoveryScheduler scheduler)).Trace (projection state),
        projected.length = history.length := by
    intro state history
    induction history with
    | start => intro _clear; exact ⟨.start, rfl⟩
    | @extend source target prior joint legal reached ih =>
        intro clear
        have actual : target ∈ ((P).transition (phaseInitial inputs) horizon scheduler source
            joint).support := reached
        have priorClear : ReactiveApplication.stateInvariant
            (fun state : PhaseRuntimeState ((toEventGraph program).withMode .sequential) =>
              state.current.excluded = ∅) source := by
          cases source with
          | none => trivial
          | some before =>
              obtain ⟨after, targetEq, _⟩ := (P).transition_recall_prefix
                (phaseInitial inputs) horizon scheduler before target joint actual
              have retained := (phaseApplication_exclusion_monotone runtime leaks).transition
                (phaseInitial inputs) horizon scheduler before after joint
                (by rwa [targetEq] at actual)
              rw [targetEq] at clear
              change after.execution.application.current.excluded = ∅ at clear
              exact Finset.subset_empty.mp (by simpa only [clear] using retained)
        obtain ⟨projected, length⟩ := ih priorClear
        have projectedLegal := legal_projected_canonical_clear program runtime leaks bounds inputs
          horizon scheduler prior priorClear joint legal
        have law : (((P).transition (phaseInitial inputs) horizon scheduler source joint).map
            projection) = (R).transition (recoveryInitial inputs) horizon
              (recoveryScheduler scheduler)
              (projection source) (jointActions runtime leaks recoveryLeaks joint) := by
          cases source with
          | none =>
              exact transition_projected_initial program runtime leaks inputs horizon scheduler
                joint
          | some current =>
              apply transition_projected_clear_history program runtime leaks bounds inputs horizon
                scheduler ((included).trace (phaseInitial inputs) horizon scheduler prior)
                priorClear
                joint
              intro who active
              have player := legal.2 who
              cases selected : joint who with
              | none => rw [selected] at player; exact (player active).elim
              | some response =>
                  rw [selected] at player
                  exact (included) who _ _ player.2
        have supported : projection target ∈ ((R).transition (recoveryInitial inputs) horizon
            (recoveryScheduler scheduler) (projection source)
              (jointActions runtime leaks recoveryLeaks joint)).support := by
          rw [← law, PMF.mem_support_map_iff]
          exact ⟨target, actual, rfl⟩
        exact ⟨projected.extend (jointActions runtime leaks recoveryLeaks joint) projectedLegal
          supported, congrArg (· + 1) length⟩
  exact origin trace clear

end PhaseRecoveryProjection
end Vegas.EventGraphRuntime
