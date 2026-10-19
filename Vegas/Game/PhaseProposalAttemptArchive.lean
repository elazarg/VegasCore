/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCountServiceForeignWord
import Vegas.Game.PhaseProposalLabelFrame
import Vegas.Pending.PhaseAttemptControls
import Interaction.ReactiveInvariantPrefix

/-! # Earlier proposal buckets at one actual attempt namespace -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "graph" => serviceGraph setup mode
local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "inputs" => setup.initialLaw.map encodeInputs
local notation "initial" =>
  PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw)

/-- The original same-attempt prefix retains the complete descriptor and
retired-record carrier and earlier proposal buckets used by the saved replay. -/
theorem phaseProposal_same_attempt_archive_metadata
    (horizon : Nat) (scheduler : (app).Scheduler)
    (start ending : (app).Control)
    (startTrace : ((menu).protocol initial horizon scheduler).Trace (some start))
    (endingTrace : ((menu).protocol initial horizon scheduler).Trace (some ending))
    (kept : TracePrefix startTrace endingTrace)
    (same : start.execution.application.attempt = ending.execution.application.attempt) :
    ending.execution.application.phases = start.execution.application.phases ∧
      ending.execution.application.retired = start.execution.application.retired ∧
      (PhaseProposal.sourceArchive ending.execution.network.inputs).filter
        (fun proposal => proposal.address.phase < start.execution.application.attempt.phase) =
      (PhaseProposal.sourceArchive start.execution.network.inputs).filter
        (fun proposal => proposal.address.phase < start.execution.application.attempt.phase) := by
  have frame (before after : (app).Control) (joint : Player → Option (app).Action)
      (moved : some after ∈ ((app).transition initial horizon scheduler (some before)
        joint).support) :
      (PhaseProposal.sourceArchive after.execution.network.inputs).filter
          (fun proposal => proposal.address.phase < before.execution.application.attempt.phase) =
        (PhaseProposal.sourceArchive before.execution.network.inputs).filter
          (fun proposal => proposal.address.phase <
            before.execution.application.attempt.phase) := by
    rcases before with ⟨remaining, active, execution⟩
    cases active with
    | some owner =>
        cases (PMF.mem_support_pure_iff _ _).mp moved
        exact PhaseProposal.sourceArchive_respond_before runtime leaks execution owner
          ((joint owner).getD ⟨none⟩)
    | none =>
        cases remaining with
        | zero =>
            cases (PMF.mem_support_pure_iff _ _).mp moved
            rfl
        | succ remaining =>
            obtain ⟨command, _selected, realized⟩ :=
              Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
            obtain ⟨next, stepped, equal⟩ := PMF.support_map .. ▸ realized
            cases Option.some.inj equal
            rw [PhaseProposal.sourceArchive_environmentStep runtime leaks execution next command
              stepped]
  have initialized : ∀ state ∈ (initial).support, state.Ordered := by
    intro state supported
    obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan draw
  have firstOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
    scheduler initialized ((menu).toRawTrace initial horizon scheduler startTrace)
  have along : ∀ {target} {targetTrace : ((menu).protocol initial horizon scheduler).Trace target},
      TracePrefix startTrace targetTrace → ∃ current : (app).Control, target = some current ∧
        (start.execution.application.attempt = current.execution.application.attempt →
          current.execution.application.phases = start.execution.application.phases ∧
            current.execution.application.retired = start.execution.application.retired ∧
            (PhaseProposal.sourceArchive current.execution.network.inputs).filter
                (fun proposal => proposal.address.phase <
                  start.execution.application.attempt.phase) =
              (PhaseProposal.sourceArchive start.execution.network.inputs).filter
                (fun proposal => proposal.address.phase <
                  start.execution.application.attempt.phase)) := by
    intro target targetTrace retained
    induction retained with
    | refl => exact ⟨start, rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩
    | @extend source target earlier retained joint legal realized ih =>
      obtain ⟨middle, rfl, previous⟩ := ih
      have moved : target ∈
          ((app).transition initial horizon scheduler (some middle) joint).support :=
        realized
      obtain ⟨next, rfl, _recall⟩ := (app).transition_recall_prefix initial horizon scheduler
        middle target joint moved
      have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
        initialized ((menu).toRawTrace initial horizon scheduler earlier)
      have lower := phase_attempt_progress_of_prefix runtime leaks menu initial initialized
        horizon
        scheduler start middle startTrace earlier retained firstOrdered
      have progress := (phaseApplication_namespace_progress runtime leaks).transition initial
        horizon scheduler middle next joint moved ordered
      refine ⟨next, rfl, ?_⟩
      intro finalSame
      have middleSame : start.execution.application.attempt =
          middle.execution.application.attempt := by
        have generation := congrArg CommitAttemptId.generation finalSame
        have phase := congrArg CommitAttemptId.phase finalSame
        cases first : start.execution.application.attempt with
        | mk firstPhase firstGeneration =>
          cases second : middle.execution.application.attempt with
          | mk secondPhase secondGeneration =>
            simp only [first, second] at lower progress generation phase ⊢
            congr 1 <;> omega
      have following := (phaseApplication_sameAttempt_controls runtime leaks).transition initial
        horizon scheduler middle next joint moved ordered (middleSame.symm.trans finalSame)
      have archive := frame middle next joint moved
      have phase := congrArg CommitAttemptId.phase middleSame
      rw [← phase] at archive
      exact ⟨following.1.trans (previous middleSame).1,
        following.2.trans (previous middleSame).2.1,
        archive.trans (previous middleSame).2.2⟩
  obtain ⟨actual, stateEq, controls⟩ := along kept
  cases Option.some.inj stateEq
  exact controls same

end Vegas
