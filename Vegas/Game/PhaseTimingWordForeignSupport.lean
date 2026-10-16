/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAnchoredMixture
import Interaction.ReactiveMixtureSupport
import Vegas.Game.PhaseTimingWordPlan
import Vegas.Source.CommitPrefixProduct

/-! # Original foreign source words from a full authentic physical entry -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability
  Interaction.ReactiveApplication

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
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

open Classical in
/-- A genuine original plan/source-word row, continued from the FULL physical
entry under an arbitrary focal intervention, derives every FOREIGN member's
actual mixture consistency. Old raw aliases are replayed at unit likelihood;
the focal past is never required to have a latent source explanation. The
explicit full-plan law can retain its actual updated distribution at entry. -/
theorem phaseTimingWordForeign_consistent_of_entry_run
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (fallback : (who : Player) → (N).Policy who)
    (wellFormed : setup.WellFormed) (source : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (planLaw : PMF ((p : Pool) → Parts p))
    (suffix : SourceProgram Player L Δ P)
    (profile : SourceProgram.BehavioralProfile (block.prepend suffix))
    (sourceEntry : SourceProgram.Config Player L Γ)
    (anchor : (app).Execution) (remaining count : Nat)
    (anchorTrace : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨remaining + count + 1, none, anchor⟩))
    (focal : Player) (intervention : (N).BehavioralPolicy focal)
    (parts : (p : Pool) → Parts p) (complete : SourceProgram.Config Player L Δ)
    (control : (app).Control) :
    let wordLaw := block.prefixLaw suffix profile sourceEntry
    let family := fun selected who => phaseTimingWordPlanPolicy setup mode runtime leaks bounds
      initial horizon scheduler bound fallback wellFormed source block low generation slotWeight
        slotNonnegative slotBounded selected who
    let original := fun who => planLaw.bind fun selected =>
      (wordLaw.map (SourceProgram.Config.view who)).map (Prod.mk selected)
    let members := fun who memory => anchoredPolicy anchor
      (fun _ => family memory.1 who memory.2) who
    let focalPolicy := (app).decodePolicy ((menu).embedPolicy initial horizon scheduler focal
      intervention)
    (parts, complete, control) ∈ (planLaw.bind fun selected =>
      wordLaw.bind fun word =>
        let players := Function.update (fun who => family selected who (word.view who))
          focal focalPolicy
        ((app).runRounds scheduler players count anchor).bind fun before =>
          (scheduler before.environmentRecall (before.observeEnvironment (app))).bind fun command =>
            (before.environmentStep (app) command).map fun active =>
              (selected, word,
                (⟨remaining, command.actor? (app), active⟩ : (app).Control))).support →
      Nonempty (((menu).protocol initial horizon scheduler).Trace (some control)) ∧
      ∀ who, who ≠ focal →
        ((app).policyMixture (original who) (members who)).policy.Consistent
          (control.execution.recall who) ∧
        (parts, complete.view who) ∈
          (((app).policyMixture (original who) (members who)).posterior
            (control.execution.recall who)).support := by
  intro wordLaw family original members focalPolicy supported
  obtain ⟨selected, selectedMem, word, wordMem, before, rounds, command, commanded, active,
    moved, equal⟩ := by
    simpa only [PMF.support_bind, Set.mem_iUnion, PMF.support_map] using supported
  obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
  let players := Function.update (fun who => family selected who (word.view who)) focal focalPolicy
  have covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ (menu).actions who past view := by
    intro who past view action admitted
    by_cases same : who = focal
    · subst who
      simp only [players, Function.update_self] at admitted
      exact (menu).decode_embedPolicy_covered initial horizon scheduler focal intervention
        past view action admitted
    · simp only [players, Function.update_of_ne same] at admitted
      exact (menu).decode_embedPolicy_covered initial horizon scheduler who _ past view action
        admitted
  obtain ⟨beforeTrace⟩ := (menu).trace_runRounds initial horizon scheduler players covered
    (remaining + 1) count anchor before (by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using anchorTrace) rounds
  have pending := (menu).trace_environment initial horizon scheduler remaining before active command
    beforeTrace commanded moved
  have anchoredRounds : before ∈ ((app).runRounds scheduler (anchoredPolicy anchor players)
      count anchor).support := by
    rw [runRounds_anchoredPolicy]
    exact rounds
  have consistent :=
    ((app).consistentRecall_policyInvariant (anchoredPolicy anchor players)).runRounds
    scheduler count anchor before (fun who => anchoredPolicy_consistent anchor players who)
      anchoredRounds
  refine ⟨pending, ?_⟩
  intro who different
  have priorMember : (selected, word.view who) ∈ (original who).support := by
    rw [PMF.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨selected, selectedMem, ?_⟩
    apply (PMF.mem_support_map_iff ..).mpr
    refine ⟨word.view who, ?_, rfl⟩
    exact (PMF.mem_support_map_iff ..).mpr ⟨word, wordMem, rfl⟩
  have policyEq : anchoredPolicy anchor players who = members who (selected, word.view who) := by
    funext past view
    simp only [anchoredPolicy, players, Function.update_of_ne different]
    rfl
  apply (app).policyMixture_consistent_of_supported_member (original who) (members who)
    (selected, word.view who) priorMember (active.recall who)
  rw [(app).environmentStep_recall before active command moved, ← policyEq]
  exact consistent who

end Vegas
