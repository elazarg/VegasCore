/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseNativeTrace
import Vegas.Game.SequentialPhaseCountedMenuReverse

/-! # Local canonical counted choices before a public phase exclusion

Actual canonical phase histories supply the recovery and native legality
witnesses. The equivalence itself acts only on the player's response syntax;
no hidden history representative is consulted by either direction.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)

local notation "plan" => sequentialRuntimePhasePlan setup.program
local notation "recoveryLeaks" => PhaseNativeProjection.nativeLeaks leaks (plan)
local notation "P" => phaseApplication (runtime setup) leaks
local notation "R" => recoveryApplication (runtime setup) (recoveryLeaks)
local notation "N" => application setup (recoveryLeaks)
local notation "inputs" => setup.initialLaw.map setup.eventInputs
local notation "initial" => PMF.map (PhaseRuntimeState.initial (plan)) (inputs)
local notation "raw" => PhaseCount.onePacketMenu (runtime setup) leaks bounds
local notation "normal" => PhaseCount.normalization (runtime setup) leaks
local notation "canonical" => ReactiveApplication.SubmissionNormalization.menu (normal) (raw)
local notation "RecoveryMenu" => Recovery.onePacketMenu (runtime setup) (recoveryLeaks) bounds
local notation "RecoveryPrior" =>
  PMF.map (fun draw => (RecoveryState.mk (EventGraphRuntime.State.initial draw) ∅ :
    RecoveryState (graph setup))) (inputs)
local notation "RecoveryScheduler" => SequentialPhaseSchedulerInformation.scheduler setup.program
  (runtime setup) leaks (recoveryLeaks) scheduler

/-- Canonical callback legality agrees exactly at every actual clear canonical
phase prefix. The native legality witness is constructed from that same trace. -/
theorem phase_canonical_callback_iff_recovery {control : (P).Control}
    (trace : ((canonical).protocol (initial) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (who : Player) (response : (P).Action) :
    response ∈ (canonical).actions who (control.execution.recall who)
        (control.execution.observe (P) who) ↔
      PhaseRecoveryProjection.action (runtime setup) leaks (recoveryLeaks) response ∈
        (RecoveryMenu).actions who
          ((control.execution.recall who).map
            (PhaseRecoveryProjection.playerEntry (runtime setup) leaks (recoveryLeaks)))
          (PhaseRecoveryProjection.playerView (runtime setup) leaks (recoveryLeaks)
            (control.execution.observe (P) who)) := by
  have counted := (PhaseCount.normalized_onePacket_included (runtime setup) leaks bounds).trace
    (initial) horizon scheduler trace
  rw [(normal).menu_mem_iff_of_closed (raw) who (control.execution.recall who)
    (control.execution.observe (P) who)
    (PhaseCount.onePacketMenu_closed (runtime setup) leaks bounds who _ _) response]
  constructor
  · rintro ⟨admitted, fixed⟩
    exact PhaseRecoveryProjection.recovery_onePacket_mem_of_normal_phase_history setup.program
      (runtime setup) leaks (recoveryLeaks) bounds (inputs) horizon scheduler counted clear who
      response admitted fixed
  · intro admitted
    obtain ⟨native, endpoint, _length, nativeClear⟩ :=
      PhaseRecoveryProjection.exists_native_canonical_clear_history setup.program (runtime setup)
        leaks bounds (inputs) horizon scheduler trace clear
    let nativeControl : (N).Control := RecoveryProjection.control (runtime setup) (recoveryLeaks)
      (PhaseRecoveryProjection.control (runtime setup) leaks (recoveryLeaks) control)
    have current : native.state = some nativeControl := endpoint
    let nativeScheduler := RecoveryProjection.nativeScheduler (runtime setup) (recoveryLeaks)
      (RecoveryScheduler)
    have nativeTrace :
        (onePacketProtocol setup (recoveryLeaks) bounds horizon nativeScheduler).Trace
          (some nativeControl) := by
      have actual := current ▸ native.trace
      have prior : (RecoveryPrior).map RecoveryState.native = initialLaw setup := by
        simp only [PMF.map_comp, Function.comp_def, initialLaw, serviceInitialLaw]
      change ((bounds.onePacketMenu (runtime setup) (recoveryLeaks)).protocol
        ((RecoveryPrior).map RecoveryState.native) horizon nativeScheduler).Trace
          (some nativeControl) at actual
      exact Eq.mp (congrArg (fun prior : PMF (EventGraphRuntime.State (graph setup)) =>
        ((bounds.onePacketMenu (runtime setup) (recoveryLeaks)).protocol prior horizon
          nativeScheduler).Trace (some nativeControl)) prior) actual
    exact phase_onePacket_mem_of_recovery_paired_history setup leaks (recoveryLeaks) bounds
      (inputs) horizon scheduler counted clear nativeScheduler nativeControl nativeTrace
      (nativeClear nativeControl current) rfl who rfl rfl response admitted

/-- The callback equivalence changes only response syntax. Actual histories
justify membership, and the maps retain identical authenticated submissions. -/
def phaseCanonicalCallbackEquiv {control : (P).Control}
    (trace : ((canonical).protocol (initial) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅) (who : Player) :
    { response : (P).Action // response ∈ (canonical).actions who (control.execution.recall who)
      (control.execution.observe (P) who) } ≃
    { response : (R).Action // response ∈ (RecoveryMenu).actions who
      ((control.execution.recall who).map
        (PhaseRecoveryProjection.playerEntry (runtime setup) leaks (recoveryLeaks)))
      (PhaseRecoveryProjection.playerView (runtime setup) leaks (recoveryLeaks)
        (control.execution.observe (P) who)) } where
  toFun response :=
    ⟨PhaseRecoveryProjection.action (runtime setup) leaks (recoveryLeaks) response.1,
      (phase_canonical_callback_iff_recovery setup leaks bounds horizon scheduler trace clear who
        response.1).mp response.2⟩
  invFun response := ⟨PhaseRecoveryProjection.phaseAction (runtime setup) leaks (recoveryLeaks)
    response.1, (phase_canonical_callback_iff_recovery setup leaks bounds horizon scheduler
      trace clear who _).mpr (by
        simpa only [PhaseRecoveryProjection.action_phaseAction] using response.2)⟩
  left_inv response := Subtype.ext
    (PhaseRecoveryProjection.phaseAction_action (runtime setup) leaks (recoveryLeaks) response.1)
  right_inv response := Subtype.ext
    (PhaseRecoveryProjection.action_phaseAction (runtime setup) leaks (recoveryLeaks) response.1)

/-- At the corresponding actual local callback input, information-model choices
have the same equivalence. Optional actions are mapped purely by their syntax. -/
def phaseCanonicalChoiceEquiv {control : (P).Control}
    (trace : ((canonical).protocol (initial) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅) (who : Player) :
    ((canonical).information (initial) horizon scheduler).Choice who
        (some (control.execution.recall who, control.execution.observe (P) who)) ≃
      ((RecoveryMenu).information (RecoveryPrior) horizon (RecoveryScheduler)).Choice who
        (some ((control.execution.recall who).map
          (PhaseRecoveryProjection.playerEntry (runtime setup) leaks (recoveryLeaks)),
          PhaseRecoveryProjection.playerView (runtime setup) leaks (recoveryLeaks)
            (control.execution.observe (P) who))) where
  toFun choice :=
    ⟨choice.1.map (PhaseRecoveryProjection.action (runtime setup) leaks (recoveryLeaks)), by
      obtain ⟨response, admitted, chosen⟩ := choice.2
      refine ⟨PhaseRecoveryProjection.action (runtime setup) leaks (recoveryLeaks) response,
        (phase_canonical_callback_iff_recovery setup leaks bounds horizon scheduler trace clear who
          response).mp admitted, ?_⟩
      rw [chosen]
      rfl⟩
  invFun choice :=
    ⟨choice.1.map (PhaseRecoveryProjection.phaseAction (runtime setup) leaks (recoveryLeaks)), by
      obtain ⟨response, admitted, chosen⟩ := choice.2
      refine ⟨PhaseRecoveryProjection.phaseAction (runtime setup) leaks (recoveryLeaks) response,
        (phase_canonical_callback_iff_recovery setup leaks bounds horizon scheduler trace clear who
          _).mpr ?_, ?_⟩
      · simpa only [PhaseRecoveryProjection.action_phaseAction] using admitted
      · rw [chosen]
        rfl⟩
  left_inv choice := by
    apply Subtype.ext
    change (choice.1.map (PhaseRecoveryProjection.action (runtime setup) leaks (recoveryLeaks))).map
      (PhaseRecoveryProjection.phaseAction (runtime setup) leaks (recoveryLeaks)) = choice.1
    cases chosen : choice.1 with
    | none => rfl
    | some response =>
        exact congrArg some
          (PhaseRecoveryProjection.phaseAction_action (runtime setup) leaks (recoveryLeaks)
            response)
  right_inv choice := by
    apply Subtype.ext
    change (choice.1.map
      (PhaseRecoveryProjection.phaseAction (runtime setup) leaks (recoveryLeaks))).map
        (PhaseRecoveryProjection.action (runtime setup) leaks (recoveryLeaks)) = choice.1
    cases chosen : choice.1 with
    | none => rfl
    | some response =>
        exact congrArg some
          (PhaseRecoveryProjection.action_phaseAction (runtime setup) leaks (recoveryLeaks)
            response)

end Vegas
