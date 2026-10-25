/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseTransition
import Interaction.ReactiveInvariantPrefix

/-! # Actual recovery traces through the first singleton phase exclusion

Every clear counted phase trace projects to a legal recovery trace.
One further actual transition can be retained, including its first-exclusion
endpoint. No converse lifting of arbitrary recovery histories is asserted.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseRecoveryProjection

open SourceProgram EventGraph Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (recoveryLeaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "P" => phaseApplication runtime leaks
local notation "R" => recoveryApplication runtime recoveryLeaks

/-- Raw recovery availability accepts every mapped phase response, and the
physical projection retains the active player and terminal rank. -/
theorem legal_projected_raw
    (phaseInitial : PMF (P).State) (recoveryInitial : PMF (R).State) (horizon : Nat)
    (phaseScheduler : (P).Scheduler) (recoveryScheduler : (R).Scheduler)
    (state : (P).ProtocolState) (joint : Player → Option (P).Action)
    (legal : ((P).protocol phaseInitial horizon phaseScheduler).Legal state joint) :
    ((R).protocol recoveryInitial horizon recoveryScheduler).Legal
      (protocolState runtime leaks recoveryLeaks state)
      (jointActions runtime leaks recoveryLeaks joint) := by
  have sameTerminal : (R).terminal (protocolState runtime leaks recoveryLeaks state) ↔
      (P).terminal state := by cases state <;> rfl
  have sameActor : (R).actor (protocolState runtime leaks recoveryLeaks state) =
      (P).actor state := by cases state <;> rfl
  refine ⟨fun ended => legal.1 (sameTerminal.mp ended), fun who => ?_⟩
  have localLegal := legal.2 who
  cases selected : joint who with
  | none =>
      rw [selected] at localLegal
      simp only [jointActions, selected, Option.map_none]
      change ¬ (R).actor _ = some who
      rwa [sameActor]
  | some response =>
      rw [selected] at localLegal
      simp only [jointActions, selected, Option.map_some]
      change (R).actor _ = some who ∧ _
      exact ⟨sameActor.trans localLegal.1, Set.mem_univ _⟩

end PhaseRecoveryProjection

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
local notation "projection" => protocolState runtime leaks recoveryLeaks
local notation "recoveryScheduler" =>
  SequentialPhaseSchedulerInformation.scheduler program runtime leaks recoveryLeaks
local notation "phaseInitial" => PMF.map (PhaseRuntimeState.initial plan)
local notation "recoveryInitial" =>
  PMF.map (fun input => RecoveryState.mk (State.initial input) ∅)

/-- An actual clear phase source extends any already matched raw recovery prefix.
The successor may contain a first exclusion; no successor decoding is needed. -/
theorem trace_projected_extend
    (inputs : PMF ((toEventGraph program).withMode .sequential).Inputs) (horizon : Nat)
    (scheduler : (P).Scheduler) {source : (P).ProtocolState}
    (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (phaseInitial inputs) horizon scheduler).Trace source)
    (clear : ReactiveApplication.stateInvariant
      (fun state : PhaseRuntimeState ((toEventGraph program).withMode .sequential) =>
        state.current.excluded = ∅) source)
    (projected : ((R).protocol (recoveryInitial inputs) horizon
      (recoveryScheduler scheduler)).Trace (projection source))
    (joint : Player → Option (P).Action)
    (legal : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (phaseInitial inputs) horizon scheduler).Legal source joint)
    (target : (P).ProtocolState)
    (reached : target ∈
      ((P).transition (phaseInitial inputs) horizon scheduler source joint).support) :
    ∃ next : ((R).protocol (recoveryInitial inputs) horizon
      (recoveryScheduler scheduler)).Trace (projection target),
      next.length = projected.length + 1 := by
  have allowed := legal_projected_raw runtime leaks recoveryLeaks (phaseInitial inputs)
    (recoveryInitial inputs) horizon scheduler (recoveryScheduler scheduler) source joint
    ((PhaseCount.onePacketMenu runtime leaks bounds).legal_raw _ _ _ legal)
  have law : (((P).transition (phaseInitial inputs) horizon scheduler source joint).map
      projection) = (R).transition (recoveryInitial inputs) horizon (recoveryScheduler scheduler)
        (projection source) (jointActions runtime leaks recoveryLeaks joint) := by
    cases source with
    | none =>
        exact transition_projected_initial program runtime leaks inputs horizon scheduler joint
    | some current =>
        apply transition_projected_clear_history program runtime leaks bounds inputs horizon
          scheduler prior clear joint
        intro who active
        have localLegal := legal.2 who
        cases selected : joint who with
        | none =>
            rw [selected] at localLegal
            exact (localLegal active).elim
        | some response =>
            rw [selected] at localLegal
            exact localLegal.2
  have supported : projection target ∈ ((R).transition (recoveryInitial inputs) horizon
      (recoveryScheduler scheduler) (projection source)
        (jointActions runtime leaks recoveryLeaks joint)).support := by
    rw [← law, PMF.mem_support_map_iff]
    exact ⟨target, reached, rfl⟩
  exact ⟨projected.extend (jointActions runtime leaks recoveryLeaks joint) allowed supported, rfl⟩

/-- Every actual clear counted phase history has a length-preserving legal raw
recovery history at its complete physical execution projection. -/
theorem trace_projected_clear
    (inputs : PMF ((toEventGraph program).withMode .sequential).Inputs) (horizon : Nat)
    (scheduler : (P).Scheduler) {state : (P).ProtocolState}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (phaseInitial inputs) horizon scheduler).Trace state)
    (clear : ReactiveApplication.stateInvariant
      (fun state : PhaseRuntimeState ((toEventGraph program).withMode .sequential) =>
        state.current.excluded = ∅) state) :
    ∃ projected : ((R).protocol (recoveryInitial inputs) horizon
      (recoveryScheduler scheduler)).Trace (projection state),
      projected.length = trace.length := by
  have origin : ∀ {state} (history : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (phaseInitial inputs) horizon scheduler).Trace state),
      ReactiveApplication.stateInvariant
        (fun state : PhaseRuntimeState ((toEventGraph program).withMode .sequential) =>
          state.current.excluded = ∅) state →
      ∃ projected : ((R).protocol (recoveryInitial inputs) horizon
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
        obtain ⟨next, nextLength⟩ := trace_projected_extend program runtime leaks bounds inputs
          horizon scheduler prior priorClear projected joint legal target actual
        exact ⟨next, nextLength.trans (congrArg (· + 1) length)⟩
  exact origin trace clear


end PhaseRecoveryProjection
end Vegas.EventGraphRuntime
