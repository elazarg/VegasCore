/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingWordPlanFilledPosterior
import Interaction.ReactiveMixtureSupport

/-! # Correlated complete source configurations after actual focal recall -/

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

/-- The genuine NON-RAW focal recall conditions the ORIGINAL joint chronological source
configuration, retaining all foreign values and repeated-owner dependence. This
is an own-response posterior, not yet the posterior of the external runtime
observation or of a hidden-entry mixture. -/
theorem phaseTimingWordPlanPolicy_config_posterior_of_history
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    (earlier : SourceProgram.CommitPrefix Γ O Δ P) (later : SourceProgram.CommitPrefix Δ P Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (profile : SourceProgram.BehavioralProfile (earlier.prepend (later.prepend suffix)))
    (entry : SourceProgram.Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (earlier.prepend (later.prepend suffix))) (low generation : Nat)
    (rank : ∀ index, (embedding.event index).val = low + index.val)
    (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
      decodeEventAction (earlier.prepend (later.prepend suffix)) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (timingPlan : (p : Pool) → Parts p) (who : Player)
    {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (selected : (serviceGraph setup mode).EventId)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, selected⟩)
    (inside : low ≤ selected.val ∧ selected.val < low + (earlier.append later).length)
    (atEnd : selected.val = low + earlier.length)
    (address : control.execution.application.attempt = ⟨low, generation⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, selected⟩) :
    let current := earlier.tailProfile (later.prepend suffix) profile
    let before := earlier.prefixLaw (later.prepend suffix) profile entry
    let completeLaw := before.bind (later.prefixLaw suffix current)
    let prior := completeLaw.map (SourceProgram.Config.view who)
    let family := phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon
      scheduler bound fallback wellFormed source (earlier.append later) low generation slotWeight
        slotNonnegative slotBounded timingPlan who
    let filled := fillCommitPrefix setup.program earlier (later.prepend suffix) embedding
      control.execution.application.current.native.config.store entry
    ((app).policyMixture prior family).policy.Consistent (control.execution.recall who) →
      filled.view who ∈ (before.map (SourceProgram.Config.view who)).support ∧
        ((app).policyMixture completeLaw
          (fun config => family (config.view who))).posterior (control.execution.recall who) =
            fiberPosterior completeLaw (fun config => later.entryView who (config.view who))
              (filled.view who) := by
  classical
  intro current before completeLaw prior family filled consistent
  obtain ⟨present, ownPosterior⟩ := phaseTimingWordPlanPolicy_posterior_filled_of_history setup mode
    runtime leaks bounds runtimePlan inputs horizon scheduler bound fallback wellFormed source
      earlier later suffix profile entry embedding low generation rank actions slotWeight
        slotNonnegative slotBounded timingPlan who trace clear selected request inside atEnd
          address unsent consistent
  refine ⟨present, ?_⟩
  let past := control.execution.recall who
  have projection : prior.map (later.entryView who) =
      before.map (SourceProgram.Config.view who) :=
    earlier.prefixLaw_split_entryView later suffix profile entry who
  have viewPresent : filled.view who ∈ (prior.map (later.entryView who)).support := by
    rw [projection]
    exact present
  have compatible (word : DecisionView who Ξ) (supported : word ∈ prior.support) :
      (family word).Consistent past ↔ later.entryView who word = filled.view who := by
    constructor
    · intro member
      have possible := ((app).policyMixture_consistent_of_supported_member prior family word
        supported past member).2
      rw [ownPosterior] at possible
      exact (mem_support_fiberPosterior viewPresent possible).1
    · intro same
      have possible : word ∈
          (fiberPosterior prior (later.entryView who) (filled.view who)).support := by
        rw [fiberPosterior_support prior (later.entryView who) (filled.view who) viewPresent]
        exact ⟨same, supported⟩
      rw [← ownPosterior] at possible
      exact (app).policyMixture_member_consistent prior family past consistent word possible
  obtain ⟨original, possible⟩ :=
    ((app).policyMixture prior family).posterior past |>.support_nonempty
  have originalSupport := (app).policyMixture_posterior_mem_initial prior family past consistent
    original possible
  have originalMember := (app).policyMixture_member_consistent prior family past consistent
    original possible
  obtain ⟨config, admitted, same⟩ := (PMF.mem_support_map_iff ..).mp originalSupport
  let completeFamily := fun config : SourceProgram.Config Player L Ξ => family (config.view who)
  have configMember : (completeFamily config).Consistent past := by
    simpa only [completeFamily, same] using originalMember
  have fullConsistent := ((app).policyMixture_consistent_of_supported_member completeLaw
    completeFamily config admitted past configMember).1
  rw [(app).policyMixture_posterior_consistency_fiber completeLaw completeFamily (by
    intro recalled view response first second left right
    exact phaseTimingWordPlanPolicy_apply_eq_of_support setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed source (earlier.append later) low generation
        slotWeight slotNonnegative slotBounded timingPlan who (first.view who) (second.view who)
          recalled view response left right) past fullConsistent]
  apply fiberPosterior_eq_of_support_fiber
  intro candidate sampled
  have owned : candidate.view who ∈ prior.support :=
    (PMF.mem_support_map_iff ..).mpr ⟨candidate, sampled, rfl⟩
  simpa only [decide_eq_true_eq, completeFamily] using compatible (candidate.view who) owned

end Vegas
