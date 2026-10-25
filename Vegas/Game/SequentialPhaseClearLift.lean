/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseCanonicalTrace
import Vegas.Game.SequentialPhaseCountedMenuReverse
import Vegas.Pending.ExclusionBoundedHistory

/-! # Lifting actual clear recovery counterfactuals to canonical singleton phases

The original source prior is retained in full. Native counted prefixes are
obtained from the supplied recovery trace itself; they justify reverse callback
admission without assuming the phase trace that is subsequently constructed.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseRecoveryProjection

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (recoveryLeaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- Restore each optional response with exactly the original submission material. -/
def phaseJointActions (joint : Player → Option (recoveryApplication runtime recoveryLeaks).Action) :
    Player → Option (phaseApplication runtime leaks).Action :=
  fun who => (joint who).map (phaseAction runtime leaks recoveryLeaks)

@[simp] theorem jointActions_phaseJointActions
    (joint : Player → Option (recoveryApplication runtime recoveryLeaks).Action) :
    jointActions runtime leaks recoveryLeaks
      (phaseJointActions runtime leaks recoveryLeaks joint) = joint := by
  funext who
  cases selected : joint who <;>
    simp only [phaseJointActions, jointActions, selected, Option.map_none, Option.map_some,
      action_phaseAction]

end Vegas.EventGraphRuntime.PhaseRecoveryProjection

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup))

local notation "inputs" => PMF.map setup.eventInputs setup.initialLaw
local notation "plan" => sequentialRuntimePhasePlan setup.program
local notation "recoveryLeaks" => PhaseNativeProjection.nativeLeaks leaks plan
local notation "P" => phaseApplication (runtime setup) leaks
local notation "R" => recoveryApplication (runtime setup) recoveryLeaks
local notation "N" => application setup recoveryLeaks
local notation "normal" => PhaseCount.normalization (runtime setup) leaks
local notation "canonical" => ReactiveApplication.SubmissionNormalization.menu (normal)
  (PhaseCount.onePacketMenu (runtime setup) leaks bounds)
local notation "included" => PhaseCount.normalized_onePacket_included (runtime setup) leaks bounds
local notation "projection" => PhaseRecoveryProjection.protocolState (runtime setup) leaks
  recoveryLeaks
local notation "phaseInitial" => PMF.map (PhaseRuntimeState.initial plan) (inputs)
local notation "recoveryInitial" => PMF.map
  (fun native => RecoveryState.mk native ∅) (initialLaw setup)
local notation "old" => Recovery.onePacketMenu (runtime setup) recoveryLeaks bounds
local notation "nativeMenu" => MessageBounds.onePacketMenu (runtime setup) recoveryLeaks bounds
local notation "recoveryScheduler" => SequentialPhaseSchedulerInformation.scheduler setup.program
  (runtime setup) leaks recoveryLeaks
local notation "nativeScheduler" => RecoveryProjection.nativeScheduler (runtime setup) recoveryLeaks

omit [Fintype Player] in
private theorem compiled_recovery_initial :
    PMF.map (fun input => (⟨State.initial input, ∅⟩ : RecoveryState (graph setup))) (inputs) =
      recoveryInitial := by
  simp only [initialLaw, serviceInitialLaw, PMF.map_comp, Function.comp_def]

/-- A supplied actual clear recovery counted prefix has its own genuine native
counted prefix and exact absence of public failure evidence. -/
theorem exists_native_of_clear_recovery_counted_trace
    (horizon : Nat) (scheduler : (R).Scheduler) {state : (R).ProtocolState}
    (trace : ((old).protocol recoveryInitial horizon scheduler).Trace state)
    (clear : ReactiveApplication.stateInvariant
      (fun state : RecoveryState (graph setup) => state.excluded = ∅) state) :
    ∃ native : (onePacketProtocol setup recoveryLeaks bounds horizon
        (nativeScheduler scheduler)).History,
      native.state = RecoveryProjection.protocolState (runtime setup) recoveryLeaks state ∧
      ∀ current, native.state = some current →
        ExclusionEvidence 0 ∅
          (⟨current.execution.application, ∅⟩ : RecoveryState (graph setup)) := by
  have initialized : ∀ value ∈ (recoveryInitial).support, ∃ draw,
      value = (⟨State.initial draw, ∅⟩ : RecoveryState (graph setup)) := by
    intro value supported
    obtain ⟨native, nativeSupported, rfl⟩ := PMF.support_map .. ▸ supported
    change native ∈ (setup.initialLaw.map
      (fun draw => State.initial (graph := graph setup) (setup.eventInputs draw))).support
        at nativeSupported
    obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ nativeSupported
    exact ⟨setup.eventInputs draw, rfl⟩
  have empty : ∀ current, state = some current → current.execution.application.excluded = ∅ := by
    intro current same
    rw [same] at clear
    exact clear
  let rawTrace := (old).toRawTrace recoveryInitial horizon scheduler trace
  have nativeLaw : (recoveryInitial).map RecoveryState.native = initialLaw setup := by
    simp only [PMF.map_comp, Function.comp_def]
    exact PMF.map_id _
  obtain ⟨native, rawEq⟩ := RecoveryProjection.exists_nativeBoundedHistory (runtime setup)
    recoveryLeaks bounds recoveryInitial initialized horizon scheduler ⟨state, trace⟩ empty
  have endpoint := congrArg (fun history :
      (((runtime setup).reactiveApplication recoveryLeaks).protocol
        ((recoveryInitial).map RecoveryState.native) horizon (nativeScheduler scheduler)).History =>
      history.state) rawEq
  have record : ∀ current, native.state = some current →
      ExclusionEvidence 0 ∅ (⟨current.execution.application, ∅⟩ : RecoveryState (graph setup)) := by
    intro current same
    exact RecoveryProjection.nativeHistory_record (runtime setup) recoveryLeaks recoveryInitial
      initialized horizon scheduler rawTrace empty current (endpoint.symm.trans same)
  have result : ∃ native : ((nativeMenu).protocol
        ((recoveryInitial).map RecoveryState.native) horizon
          (nativeScheduler scheduler)).History,
      native.state = RecoveryProjection.protocolState (runtime setup) recoveryLeaks state ∧
      ∀ current, native.state = some current →
        ExclusionEvidence 0 ∅ (⟨current.execution.application, ∅⟩ : RecoveryState (graph setup)) :=
    ⟨native, endpoint, record⟩
  rw [nativeLaw] at result
  exact result

/-- At matched actual clear prefixes every original legal counted joint has a
canonical phase counted realization with identical submitted materials. -/
theorem legal_phaseJoint_of_clear_recovery_trace
    (horizon : Nat) (scheduler : (P).Scheduler)
    {phaseState : (P).ProtocolState} {oldState : (R).ProtocolState}
    (phaseTrace : ((canonical).protocol phaseInitial horizon scheduler).Trace phaseState)
    (oldTrace : ((old).protocol recoveryInitial horizon
      (recoveryScheduler scheduler)).Trace oldState)
    (matched : projection phaseState = oldState)
    (clear : ReactiveApplication.stateInvariant
      (fun state : RecoveryState (graph setup) => state.excluded = ∅) oldState)
    (joint : Player → Option (R).Action)
    (legal : ((old).protocol recoveryInitial horizon (recoveryScheduler scheduler)).Legal oldState
      joint) :
    ((canonical).protocol phaseInitial horizon scheduler).Legal phaseState
      (PhaseRecoveryProjection.phaseJointActions (runtime setup) leaks recoveryLeaks joint) := by
  subst oldState
  have terminal : (R).terminal (projection phaseState) ↔ (P).terminal phaseState := by
    cases phaseState <;> rfl
  have actor : (R).actor (projection phaseState) = (P).actor phaseState := by
    cases phaseState <;> rfl
  refine ⟨fun ended => legal.1 (terminal.mpr ended), fun who => ?_⟩
  have player := legal.2 who
  cases selected : joint who with
  | none =>
      simp only [PhaseRecoveryProjection.phaseJointActions, selected, Option.map_none]
      rw [selected] at player
      change ¬ (P).actor phaseState = some who
      exact fun active => player (actor.trans active)
  | some response =>
      simp only [PhaseRecoveryProjection.phaseJointActions, selected, Option.map_some]
      rw [selected] at player
      refine ⟨actor.symm.trans player.1, ?_⟩
      cases phaseState with
      | none => exact Set.mem_univ _
      | some current =>
          have phaseClear : current.execution.application.current.excluded = ∅ := clear
          obtain ⟨native, nativeState, nativeRecord⟩ :=
            exists_native_of_clear_recovery_counted_trace setup leaks bounds horizon
              (recoveryScheduler scheduler) oldTrace clear
          let nativeControl := RecoveryProjection.control (runtime setup) recoveryLeaks
            (PhaseRecoveryProjection.control (runtime setup) leaks recoveryLeaks current)
          change native.state = some nativeControl at nativeState
          have actualNative : (onePacketProtocol setup recoveryLeaks bounds horizon
              (nativeScheduler (recoveryScheduler scheduler))).Trace (some nativeControl) := by
            exact nativeState ▸ native.trace
          have oldMember : response ∈ Recovery.onePacketActions (runtime setup) recoveryLeaks
              bounds who
              ((PhaseRecoveryProjection.execution (runtime setup) leaks recoveryLeaks
                current.execution).recall who)
              ((PhaseRecoveryProjection.execution (runtime setup) leaks recoveryLeaks
                current.execution).observe (R) who) := player.2
          rw [PhaseRecoveryProjection.observe] at oldMember
          change response ∈ Recovery.onePacketActions (runtime setup) recoveryLeaks bounds who
            ((current.execution.recall who).map
              (PhaseRecoveryProjection.playerEntry (runtime setup) leaks recoveryLeaks))
            (PhaseRecoveryProjection.playerView (runtime setup) leaks recoveryLeaks
              (current.execution.observe (P) who)) at oldMember
          have counted := (included).trace phaseInitial horizon scheduler phaseTrace
          have member := phase_onePacket_mem_of_recovery_paired_history setup leaks recoveryLeaks
            bounds inputs horizon scheduler counted phaseClear
            (nativeScheduler (recoveryScheduler scheduler)) nativeControl actualNative
            (nativeRecord nativeControl nativeState) rfl who rfl rfl
            (PhaseRecoveryProjection.phaseAction (runtime setup) leaks recoveryLeaks response)
            (by simpa only [PhaseRecoveryProjection.action_phaseAction] using oldMember)
          exact (ReactiveApplication.SubmissionNormalization.menu_mem _ _ _ _ _ _).mpr
            ⟨_, member.1, member.2⟩

/-- Every actual clear original recovery counted trace lifts to an actual canonical
singleton phase trace, with identical length and complete projected endpoint. -/
theorem exists_canonical_phase_of_clear_recovery_trace
    (horizon : Nat) (scheduler : (P).Scheduler) {state : (R).ProtocolState}
    (trace : ((old).protocol recoveryInitial horizon (recoveryScheduler scheduler)).Trace state)
    (clear : ReactiveApplication.stateInvariant
      (fun state : RecoveryState (graph setup) => state.excluded = ∅) state) :
    ∃ phase : ((canonical).protocol phaseInitial horizon scheduler).History,
      projection phase.state = state ∧ phase.trace.length = trace.length := by
  have origin : ∀ {state}
      (history : ((old).protocol recoveryInitial horizon
        (recoveryScheduler scheduler)).Trace state),
      ReactiveApplication.stateInvariant
        (fun state : RecoveryState (graph setup) => state.excluded = ∅) state →
      ∃ phase : ((canonical).protocol phaseInitial horizon scheduler).History,
        projection phase.state = state ∧ phase.trace.length = history.length := by
    intro state history
    induction history with
    | start => intro _clear; exact ⟨⟨none, .start⟩, rfl, rfl⟩
    | @extend source target prior joint legal reached ih =>
        intro clear
        have actual : target ∈ ((R).transition recoveryInitial horizon
            (recoveryScheduler scheduler) source joint).support := reached
        have priorClear : ReactiveApplication.stateInvariant
            (fun state : RecoveryState (graph setup) => state.excluded = ∅) source := by
          cases source with
          | none => trivial
          | some before =>
              obtain ⟨after, targetEq, _⟩ := (R).transition_recall_prefix recoveryInitial horizon
                (recoveryScheduler scheduler) before target joint actual
              have retained := (recoveryApplication_exclusion_monotone (runtime setup)
                recoveryLeaks).transition recoveryInitial horizon (recoveryScheduler scheduler)
                  before after joint (by rwa [targetEq] at actual)
              rw [targetEq] at clear
              change after.execution.application.excluded = ∅ at clear
              exact Finset.subset_empty.mp (by simpa only [clear] using retained)
        obtain ⟨phase, matched, length⟩ := ih priorClear
        have phaseClear : ReactiveApplication.stateInvariant
            (fun state : PhaseRuntimeState (graph setup) => state.current.excluded = ∅)
              phase.state := by
          rw [← matched] at priorClear
          cases phaseAt : phase.state with
          | none => trivial
          | some current =>
              rw [phaseAt] at priorClear
              exact priorClear
        let phaseJoint := PhaseRecoveryProjection.phaseJointActions (runtime setup) leaks
          recoveryLeaks joint
        have phaseLegal := legal_phaseJoint_of_clear_recovery_trace setup leaks bounds horizon
          scheduler phase.trace prior matched priorClear joint legal
        have law : (((P).transition phaseInitial horizon scheduler phase.state phaseJoint).map
            projection) = (R).transition recoveryInitial horizon (recoveryScheduler scheduler)
              source joint := by
          rw [← matched, ← compiled_recovery_initial setup]
          have jointEq : PhaseRecoveryProjection.jointActions (runtime setup) leaks recoveryLeaks
              phaseJoint = joint :=
            PhaseRecoveryProjection.jointActions_phaseJointActions (runtime setup) leaks
              recoveryLeaks joint
          rw [← jointEq]
          cases sourcePhase : phase.state with
          | none =>
              exact PhaseRecoveryProjection.transition_projected_initial setup.program
                (runtime setup)
                leaks inputs horizon scheduler phaseJoint
          | some current =>
              have priorPhase := (included).trace phaseInitial horizon scheduler phase.trace
              rw [sourcePhase] at priorPhase phaseClear phaseLegal
              have step := PhaseRecoveryProjection.transition_projected_clear_history setup.program
                (runtime setup) leaks bounds inputs horizon scheduler priorPhase phaseClear
                phaseJoint (by
                  intro who active
                  have player := phaseLegal.2 who
                  simp only [PhaseRecoveryProjection.phaseJointActions] at player
                  dsimp only [phaseJoint, PhaseRecoveryProjection.phaseJointActions]
                  cases selected : joint who with
                  | none =>
                      simp only [selected, Option.map_none] at player
                      exact (player active).elim
                  | some response =>
                      simp only [selected, Option.map_some] at player
                      exact (included) who _ _ player.2)
              exact step
        have preimage : target ∈ (((P).transition phaseInitial horizon scheduler phase.state
            phaseJoint).map projection).support := by rwa [law]
        obtain ⟨next, supported, endpoint⟩ := (PMF.mem_support_map_iff _ _ _).mp preimage
        exact ⟨⟨next, phase.trace.extend phaseJoint phaseLegal supported⟩, endpoint,
          congrArg (· + 1) length⟩
  exact origin trace clear

end Vegas
