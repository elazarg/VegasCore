/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseIntendedCheckpointStep
import Vegas.Game.RecoveryInitialCheckpoint
import Vegas.Pending.PhaseNativeInclusion
import Interaction.ReactiveHistory
import Interaction.ReactiveRecovery

/-! # Whole intended source checkpoints along actual canonical clear histories -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
  (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
  (assessment : setup.commitRecoveryModel.BehavioralAssessment)
  (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source assessment.strategy)
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "inputs" => setup.initialLaw.map encodeInputs
local notation "initial" => PMF.map (PhaseRuntimeState.initial plan) inputs

include source copies maximal

private theorem include_intended_checkpoint {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (checkpoint : RecoverySourceCheckpoint setup mode control.execution.application)
    (intended : ProtocolState.Intended setup.program (checkpoint.residual.lift
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source)))
    (consistent : ∀ who, (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment
      who).Consistent (control.execution.recall who))
    (id : MessageId Player)
    (nextClear : (control.execution.includePending app id).application.current.excluded = ∅) :
    ∃ chosen : RecoverySourceCheckpoint setup mode
        (control.execution.includePending app id).application,
      ProtocolState.Intended setup.program (chosen.residual.lift
        (ProtocolState.entry chosen.residual.tail chosen.source)) := by
  have handles (message : Message Player (CommitAttemptPacket (serviceGraph setup mode)))
      (selected : (control.execution.network.includePending id).1 = some message)
      (next : PhaseRuntimeState (serviceGraph setup mode))
      (accepted : (app).handle control.execution.application message = some next)
      (cleared : next.current.excluded = ∅) :=
    phase_handle_intended_checkpoint setup mode runtime leaks bounds wellFormed source assessment
      copies plan maximal inputs horizon scheduler trace clear checkpoint intended consistent
        message (PhaseNativeProjection.included_authentic runtime leaks plan bounds inputs
          horizon scheduler trace id message selected) next accepted cleared
  simp only [ReactiveApplication.Execution.includePending] at nextClear ⊢
  generalize queued : control.execution.network.includePending id = pair at nextClear ⊢
  rcases pair with ⟨envelope, network⟩
  cases envelope with
  | none => exact ⟨checkpoint, intended⟩
  | some message =>
      have selected : (control.execution.network.includePending id).1 = some message :=
        congrArg Prod.fst queued
      change ∃ chosen : RecoverySourceCheckpoint setup mode
          (((app).handle control.execution.application message).getD
            control.execution.application),
        ProtocolState.Intended setup.program (chosen.residual.lift
          (ProtocolState.entry chosen.residual.tail chosen.source))
      cases accepted : (app).handle control.execution.application message with
      | none =>
          exact ⟨checkpoint, intended⟩
      | some next =>
          simp only [accepted, Option.getD_some] at nextClear
          exact handles message selected next accepted nextClear

private theorem environmentStep_intended_checkpoint {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (checkpoint : RecoverySourceCheckpoint setup mode control.execution.application)
    (intended : ProtocolState.Intended setup.program (checkpoint.residual.lift
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source)))
    (consistent : ∀ who, (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment
      who).Consistent (control.execution.recall who))
    (command : (app).Command) (next : (app).Execution)
    (reached : next ∈ (control.execution.environmentStep app command).support)
    (nextClear : next.application.current.excluded = ∅) :
    ∃ chosen : RecoverySourceCheckpoint setup mode next.application,
      ProtocolState.Intended setup.program (chosen.residual.lift
        (ProtocolState.entry chosen.residual.tail chosen.source)) := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨checkpoint, intended⟩
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _positive, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨checkpoint, intended⟩
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact include_intended_checkpoint setup mode runtime leaks bounds wellFormed source
        assessment copies plan maximal horizon scheduler trace clear checkpoint intended consistent
          id nextClear
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      exact phase_environment_intended_checkpoint setup mode runtime leaks bounds wellFormed source
        assessment copies plan maximal inputs horizon scheduler trace clear checkpoint intended
          consistent command state changed nextClear

/-- Every actual initialized clear history consistent with the canonical
source policy has one whole intended source checkpoint. The induction retains
the old chosen checkpoint through each physical operation and constructs its
actual successor before continuing. -/
theorem phase_intended_checkpoint_history
    {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (consistent : ∀ who, (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment
      who).Consistent (control.execution.recall who)) :
    ∃ chosen : RecoverySourceCheckpoint setup mode control.execution.application,
      ProtocolState.Intended setup.program (chosen.residual.lift
        (ProtocolState.entry chosen.residual.tail chosen.source)) := by
  have result : ∀ {state} (history : ((menu).protocol initial horizon scheduler).Trace state),
      ∀ current : (app).Control, state = some current →
      current.execution.application.current.excluded = ∅ →
      (∀ who, (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment
        who).Consistent (current.execution.recall who)) →
      ∃ chosen : RecoverySourceCheckpoint setup mode current.execution.application,
        ProtocolState.Intended setup.program (chosen.residual.lift
          (ProtocolState.entry chosen.residual.tail chosen.source)) := by
    intro state history
    induction history with
    | start => intro current impossible; cases impossible
    | @extend before after prior joint _legal reached ih =>
        intro current same cleared faithful
        subst after
        change some current ∈ ((app).transition initial horizon scheduler before joint).support
          at reached
        cases before with
        | none =>
            obtain ⟨state, stateSupported, same⟩ :=
              (PMF.mem_support_map_iff _ _ _).mp reached
            cases Option.some.inj same
            obtain ⟨draw, drawSupported, rfl⟩ :=
              (PMF.mem_support_map_iff _ _ _).mp stateSupported
            obtain ⟨original, originalSupported, rfl⟩ :=
              (PMF.mem_support_map_iff _ _ _).mp drawSupported
            exact ⟨RecoverySourceCheckpoint.initialized setup mode plan original originalSupported,
              RecoverySourceCheckpoint.initialized_intended setup mode plan wellFormed original
                originalSupported⟩
        | some previous =>
            have priorClear : previous.execution.application.current.excluded = ∅ := by
              apply Finset.subset_empty.mp
              rw [← cleared]
              exact (phaseApplication_exclusion_monotone runtime leaks).transition initial horizon
                scheduler previous current joint reached
            have priorFaithful : ∀ who, (phaseSourcePolicy setup mode runtime leaks bounds
                wellFormed assessment who).Consistent (previous.execution.recall who) := by
              obtain ⟨next, finalState, past⟩ := (app).transition_recall_prefix initial horizon
                scheduler previous (some current) joint reached
              cases Option.some.inj finalState
              intro who
              obtain ⟨tail, retained⟩ := past who
              have valid := faithful who
              rw [← retained] at valid
              exact valid.of_append
            obtain ⟨checkpoint, intended⟩ := ih previous rfl priorClear priorFaithful
            rcases previous with ⟨remaining, actor, execution⟩
            cases actor with
            | some who =>
                cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
                rcases (joint who).getD ⟨none⟩ with ⟨transmission⟩
                cases transmission with
                | none => exact ⟨checkpoint, intended⟩
                | some material => exact ⟨checkpoint.transfer rfl rfl rfl, intended⟩
            | none =>
                cases remaining with
                | zero =>
                    cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
                    exact ⟨checkpoint, intended⟩
                | succ remaining =>
                    obtain ⟨command, _selected, moved⟩ :=
                      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                    obtain ⟨next, supported, same⟩ := PMF.support_map .. ▸ moved
                    cases Option.some.inj same
                    exact environmentStep_intended_checkpoint setup mode runtime leaks bounds
                      wellFormed source assessment copies plan maximal horizon scheduler prior
                        priorClear checkpoint intended priorFaithful command next supported cleared
  exact result trace control rfl clear consistent

end Vegas
