/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingWordPlan
import Interaction.ReactiveMixtureSupport
import Interaction.ReactiveRoundTrace
import Interaction.ReactiveControlOccupation
import Interaction.ReactiveRecovery



/-! # Supported original timing plans and chronological source words -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (runtimePlan : RuntimePhasePlan (serviceGraph setup mode))
  (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial runtimePlan)
variable [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    (inputs.map (PhaseRuntimeState.initial runtimePlan)) horizon scheduler).History]
  [∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information
    (inputs.map (PhaseRuntimeState.initial runtimePlan)) horizon scheduler).InfoState who)]

local notation "N" => ReactiveApplication.ResponseMenu.information (menu) initial horizon scheduler
local notation "Agent" => InformationModel.InformationAgent (N)
  (InformationModel.playedInformation (N))
local notation "isFree" => fun agent : Agent => PhasePublicExclusion setup mode runtime leaks
  (Subtype.val (Sigma.snd agent))
local notation "isKeyed" => fun agent : Agent => PhaseUnprotected runtime leaks bound
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "poolKey" => fun agent : Agent => phaseTimingKey runtime leaks
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "Pool" => FreeKeyedPool isFree isKeyed poolKey
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

local instance timingWordSupportedPoolFintype :
    Fintype (FreeKeyedPool isFree isKeyed poolKey) := Fintype.ofFinite _

variable {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
  (fallback : (who : Player) →
    ((PhaseCount.onePacketMenu runtime leaks bounds).information
      (inputs.map (PhaseRuntimeState.initial runtimePlan)) horizon scheduler).Policy who)
  (wellFormed : setup.WellFormed) (source : setup.commitRecoveryModel.BehavioralAssessment)
  (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)

local notation "family" => phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial
  horizon scheduler bound fallback wellFormed source block low generation slotWeight
    slotNonnegative slotBounded

open Classical in
/-- Every supported original draw, full timing plan, chronological source
word and physical member run yields a genuine counted history. Its complete
own recall is supported by the original plan-times-word behavioral mixture,
so no consistency premise is imposed at the final callback. The original
input draw remains tagged and failed typed results are retained. -/
theorem phaseTimingWordPlanPolicy_consistent_of_original_run
    (weights : (p : Pool) → PMF (Parts p))
    (suffix : SourceProgram Player L Δ P)
    (profile : SourceProgram.BehavioralProfile (block.prepend suffix))
    (sourceEntry : SourceProgram.Config Player L Γ) (count : Nat) (bounded : count < horizon)
    (draw : (serviceGraph setup mode).Inputs)
    (plan : (p : Pool) → Parts p) (word : SourceProgram.Config Player L Δ)
    (control : (app).Control) :
    let wordLaw := block.prefixLaw suffix profile sourceEntry
    let prior := fun who => wordLaw.map (SourceProgram.Config.view who)
    let original := fun who => (independentProduct weights).bind fun selected =>
      (prior who).map (Prod.mk selected)
    let members := fun who memory => family memory.1 who memory.2
    (draw, plan, word, some control) ∈ (inputs.bind fun input =>
      (independentProduct weights).bind fun selected => wordLaw.bind fun complete =>
        ((app).commandControlLaw scheduler (fun who => family selected who (complete.view who))
          (PMF.pure (PhaseRuntimeState.initial runtimePlan input)) (horizon - count - 1)
            count).map
              (fun result => (input, selected, complete, result))).support →
      Nonempty (((menu).protocol initial horizon scheduler).Trace
        (some control)) ∧
      ∀ who, ((app).policyMixture (original who) (members who)).policy.Consistent
          (control.execution.recall who) ∧
        (plan, word.view who) ∈
          (((app).policyMixture (original who) (members who)).posterior
            (control.execution.recall who)).support := by
  intro wordLaw prior original members supported
  obtain ⟨input, inputMem, selected, selectedMem, complete, completeMem, result, reached,
    equal⟩ := by
    simpa only [PMF.support_bind, Set.mem_iUnion, PMF.support_map] using supported
  obtain ⟨rfl, rfl, rfl, rfl⟩ := Prod.mk.inj equal |>.imp_right (fun rest =>
    Prod.mk.inj rest |>.imp_right Prod.mk.inj)
  simp only [ReactiveApplication.commandControlLaw, PMF.pure_bind, PMF.support_bind,
    Set.mem_iUnion, PMF.support_map] at reached
  obtain ⟨before, rounds, command, commanded, next, moved, equation⟩ := reached
  cases Option.some.inj equation
  let players := fun who => family selected who (complete.view who)
  have actual : PhaseRuntimeState.initial runtimePlan input ∈ (initial).support :=
    (PMF.mem_support_map_iff ..).mpr ⟨input, inputMem, rfl⟩
  obtain ⟨initialTrace⟩ := (menu).trace_initial initial horizon scheduler _ actual
  have covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ (menu).actions who past view := by
    intro who past view action admitted
    exact (menu).decode_embedPolicy_covered initial horizon scheduler who _ past view action
      admitted
  have trace := (menu).trace_runRounds initial horizon scheduler players covered
    (horizon - count) count _ before
      (by simpa only [Nat.sub_add_cancel bounded.le] using initialTrace) rounds
  obtain ⟨beforeTrace⟩ := trace
  have beforeTrace' : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨(horizon - count - 1) + 1, none, before⟩) := by
    have remainingEq : (horizon - count - 1) + 1 = horizon - count := by omega
    simpa only [remainingEq] using beforeTrace
  have pending := (menu).trace_environment initial horizon scheduler (horizon - count - 1)
    before next command beforeTrace' commanded moved
  have consistent := ((app).consistentRecall_policyInvariant players).runRounds scheduler count
    _ before (by intro who; exact .nil) rounds
  refine ⟨pending, ?_⟩
  intro who
  have wordMem : complete.view who ∈ (prior who).support :=
    (PMF.mem_support_map_iff ..).mpr ⟨complete, completeMem, rfl⟩
  have admitted : (selected, complete.view who) ∈ (original who).support := by
    rw [PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨selected, selectedMem,
      (PMF.mem_support_map_iff ..).mpr ⟨complete.view who, wordMem, rfl⟩⟩
  exact (app).policyMixture_consistent_of_supported_member (original who) (members who)
    (selected, complete.view who) admitted (next.recall who) (by
      rw [(app).environmentStep_recall before next command moved]
      exact consistent who)

end Vegas
