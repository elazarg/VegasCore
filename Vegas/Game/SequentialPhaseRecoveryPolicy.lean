/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhasePlayerInformation
import Vegas.Game.SequentialPhaseTransition
import Interaction.ReactiveMenuPolicy
import Interaction.ReactiveMenuRestriction

/-! # Original recovery policies from counted singleton phase policies

Only the old player's own past and current view are decoded. The policy is
specified at every old input; its exact callback law is proved on every actual
clear counted phase history, including arbitrary admitted policy replacements.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.SequentialPhaseRecoveryPolicy

open SourceProgram EventGraph Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)
  (runtime : EventGraphRuntime ((toEventGraph program).withMode .sequential))
  (leaks : MessageNetwork.ObservationRule Player
    (CommitAttemptPacket ((toEventGraph program).withMode .sequential)))

local notation "plan" => sequentialRuntimePhasePlan program
local notation "recoveryLeaks" => PhaseNativeProjection.nativeLeaks leaks plan
local notation "P" => phaseApplication runtime leaks
local notation "R" => recoveryApplication runtime recoveryLeaks
local notation "decode" =>
  SequentialPhasePlayerInformation.information program runtime leaks recoveryLeaks
local notation "projectAction" => PhaseRecoveryProjection.action runtime leaks recoveryLeaks

/-- Run an original phase response policy on decoded old own information. -/
def policy (original : (P).Policy) : (R).Policy := fun past view =>
  (original (past.map
      (SequentialPhasePlayerInformation.playerEntry program runtime leaks recoveryLeaks))
    (SequentialPhasePlayerInformation.playerView program runtime leaks recoveryLeaks view)).map
      projectAction

private theorem encode_policy_map_val (original : (P).Policy) (info : (R).Info) :
    ((R).encodePolicy (policy program runtime leaks original) info).map Subtype.val =
      ((P).encodePolicy original (decode info)).map
        (fun choice => choice.1.map projectAction) := by
  cases info with
  | none =>
      simp only [ReactiveApplication.encodePolicy,
        SequentialPhasePlayerInformation.information, Option.map_none, PMF.pure_map]
  | some pair =>
      simp only [ReactiveApplication.encodePolicy, policy,
        SequentialPhasePlayerInformation.information, Option.map_some, PMF.map_comp,
        Function.comp_def]

variable [Fintype Player]
  (menu : (phaseApplication runtime leaks).ResponseMenu)
  (bounds : MessageBounds ((toEventGraph program).withMode .sequential))
  (included : menu.IncludedIn (PhaseCount.onePacketMenu runtime leaks bounds))
  (inputs : PMF ((toEventGraph program).withMode .sequential).Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "phaseInitial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "recoveryInitial" =>
  inputs.map (fun input => RecoveryState.mk (State.initial input) ∅)
local notation "recoveryScheduler" =>
  SequentialPhaseSchedulerInformation.scheduler program runtime leaks recoveryLeaks scheduler
local notation "M" =>
  ReactiveApplication.ResponseMenu.information (menu) phaseInitial horizon scheduler
local notation "N" =>
  ReactiveApplication.information (R) recoveryInitial horizon recoveryScheduler

/-- Derive a completely unrestricted old behavioral policy from an arbitrary
counted phase policy by its existing physical-policy encoding. -/
def behavioralPolicy (who : Player) (original : (M).BehavioralPolicy who) :
    (N).BehavioralPolicy who :=
  (R).encodePolicy (policy program runtime leaks
    ((P).decodePolicy ((menu).embedPolicy phaseInitial horizon scheduler who original)))

omit [Fintype Player] in
/-- Forgetting only menu witnesses, the derived old callback law is the exact
mapped phase-menu callback law at the decoded player input. -/
theorem behavioralPolicy_map_val (who : Player) (original : (M).BehavioralPolicy who)
    (info : (R).Info) :
    (behavioralPolicy program runtime leaks menu inputs horizon scheduler who original info).map
        Subtype.val =
      (original (decode info)).map (fun choice => choice.1.map projectAction) := by
  unfold behavioralPolicy
  rw [encode_policy_map_val, (P).encode_decodePolicy]
  simp only [ReactiveApplication.ResponseMenu.embedPolicy, PMF.map_comp]
  rfl

include included in
/-- Every actual clear counted callback is reproduced from the original own
input alone; no history index or scheduler memory enters the policy. -/
theorem policy_history (original : (P).Policy) {control : (P).Control}
    (trace : ((menu).protocol phaseInitial horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅) (who : Player) :
    policy program runtime leaks original
      ((PhaseRecoveryProjection.execution runtime leaks recoveryLeaks
        control.execution).recall who)
      ((PhaseRecoveryProjection.execution runtime leaks recoveryLeaks
        control.execution).observe (R) who) =
      (original (control.execution.recall who)
        (control.execution.observe (P) who)).map projectAction := by
  unfold policy
  rw [PhaseRecoveryProjection.observe]
  change (original (((control.execution.recall who).map
      (PhaseRecoveryProjection.playerEntry runtime leaks recoveryLeaks)).map
        (SequentialPhasePlayerInformation.playerEntry program runtime leaks recoveryLeaks))
      (SequentialPhasePlayerInformation.playerView program runtime leaks recoveryLeaks
        (PhaseRecoveryProjection.playerView runtime leaks recoveryLeaks
          (control.execution.observe (P) who)))).map projectAction = _
  rw [SequentialPhasePlayerInformation.recall_history program runtime leaks recoveryLeaks bounds
    inputs horizon scheduler (included.trace phaseInitial horizon scheduler trace) clear who,
    SequentialPhasePlayerInformation.playerView_history program runtime leaks recoveryLeaks bounds
      inputs horizon scheduler (included.trace phaseInitial horizon scheduler trace) clear who]

end Vegas.EventGraphRuntime.SequentialPhaseRecoveryPolicy
