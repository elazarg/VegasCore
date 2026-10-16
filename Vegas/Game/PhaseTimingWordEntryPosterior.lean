/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingWordPlanFilledPosterior
import Vegas.Source.CommitPrefixEntryKernel
import Interaction.ReactiveMixtureSupport

/-! # Original hidden source entries retained through actual focal recall -/

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

omit [Fintype Player] in
private theorem posterior_projected_fiber {Index Word View : Type}
    (law : PMF Index) (read : Index → Word) (family : Word → (app).Policy)
    (observe : Word → View) (wanted : View) (past : List (app).PlayerEntry)
    (atoms : ∀ earlier view response first second,
      response ∈ (family first earlier view).support →
      response ∈ (family second earlier view).support →
        family first earlier view response = family second earlier view response)
    (consistent : ((app).policyMixture (law.map read) family).policy.Consistent past)
    (posterior : ((app).policyMixture (law.map read) family).posterior past =
      fiberPosterior (law.map read) observe wanted)
    (present : wanted ∈ ((law.map read).map observe).support) :
    ((app).policyMixture law (fun index => family (read index))).posterior past =
      fiberPosterior law (fun index => observe (read index)) wanted := by
  classical
  let own := (app).policyMixture (law.map read) family
  have compatible (word : Word) (supported : word ∈ (law.map read).support) :
      (family word).Consistent past ↔ observe word = wanted := by
    constructor
    · intro member
      have possible := ((app).policyMixture_consistent_of_supported_member (law.map read) family
        word supported past member).2
      rw [posterior] at possible
      exact (mem_support_fiberPosterior present possible).1
    · intro same
      have possible : word ∈ (fiberPosterior (law.map read) observe wanted).support := by
        rw [fiberPosterior_support _ _ _ present]
        exact ⟨same, supported⟩
      rw [← posterior] at possible
      exact (app).policyMixture_member_consistent _ family past consistent word possible
  obtain ⟨word, possible⟩ := (own.posterior past).support_nonempty
  have wordSupport := (app).policyMixture_posterior_mem_initial (law.map read) family past
    consistent word possible
  have wordMember := (app).policyMixture_member_consistent (law.map read) family past consistent
    word possible
  obtain ⟨index, admitted, same⟩ := (PMF.mem_support_map_iff ..).mp wordSupport
  have member : (family (read index)).Consistent past := same.symm ▸ wordMember
  have full := ((app).policyMixture_consistent_of_supported_member law
    (fun index => family (read index)) index admitted past member).1
  rw [(app).policyMixture_posterior_consistency_fiber law (fun index => family (read index))
    (fun earlier view response first second => atoms earlier view response (read first)
      (read second)) past full]
  apply fiberPosterior_eq_of_support_fiber
  intro index admitted
  have observed : read index ∈ (law.map read).support :=
    (PMF.mem_support_map_iff ..).mpr ⟨index, admitted, rfl⟩
  simpa only [decide_eq_true_eq] using compatible (read index) observed

omit [Fintype Player] in
private theorem source_entry_fiber_redundant
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    (earlier : SourceProgram.CommitPrefix Γ O Δ P)
    (later : SourceProgram.CommitPrefix Δ P Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (profile : SourceProgram.BehavioralProfile ((earlier.append later).prepend suffix))
    (entryLaw : PMF (SourceProgram.Config Player L Γ)) (entry : SourceProgram.Config Player L Γ)
    (admitted : entry ∈ entryLaw.support) (who : Player) (observed : DecisionView who Δ) :
    let selected := fiberPosterior entryLaw (SourceProgram.Config.view who) (entry.view who)
    let kernel := fun original : SourceProgram.Config Player L Γ =>
      ((earlier.append later).prefixLaw suffix profile original).map (Prod.mk original)
    let fine := fun pair : SourceProgram.Config Player L Γ × SourceProgram.Config Player L Ξ =>
      later.entryView who (pair.2.view who)
    observed ∈ ((selected.bind kernel).map fine).support →
      fiberPosterior (selected.bind kernel) fine observed =
        fiberPosterior (entryLaw.bind kernel) fine observed := by
  intro selected kernel fine present
  let coarse := fun pair : SourceProgram.Config Player L Γ × SourceProgram.Config Player L Ξ =>
    pair.1.view who
  have entryPresent : entry.view who ∈ (entryLaw.map (SourceProgram.Config.view who)).support :=
    (PMF.mem_support_map_iff ..).mpr ⟨entry, admitted, rfl⟩
  have shifted := fiberPosterior_bind_of_observation entryLaw kernel
    (SourceProgram.Config.view who) coarse (by
      intro original _ row sampled
      obtain ⟨_final, _sampled, rfl⟩ := (PMF.mem_support_map_iff ..).mp sampled
      rfl) (entry.view who) entryPresent
  have coarseEq : fiberPosterior (entryLaw.bind kernel) coarse (entry.view who) =
      fiberPosterior (entryLaw.bind kernel) ((earlier.entryView who) ∘ fine)
        (entry.view who) := by
    apply fiberPosterior_eq_of_support_fiber
    intro pair sampled
    obtain ⟨original, _admitted, sampled⟩ := (PMF.mem_support_bind_iff ..).mp sampled
    obtain ⟨final, drawn, rfl⟩ := (PMF.mem_support_map_iff ..).mp sampled
    obtain ⟨attempt⟩ := (earlier.append later).prefixLaw_attempt suffix profile original final drawn
    have same := SourceProgram.CommitPrefix.Attempt.entryView_eq (earlier.append later) original
      final attempt who
    rw [SourceProgram.CommitPrefix.entryView_append] at same
    change original.view who = entry.view who ↔
      earlier.entryView who (later.entryView who (final.view who)) = entry.view who
    rw [same]
  have precise : observed ∈
      ((fiberPosterior (entryLaw.bind kernel) ((earlier.entryView who) ∘ fine)
        (entry.view who)).map fine).support := by
    rw [← coarseEq, shifted]
    exact present
  rw [← shifted, coarseEq]
  exact fiberPosterior_after_projection (entryLaw.bind kernel) fine (earlier.entryView who)
    (entry.view who) observed precise

/-- Sampling the ORIGINAL hidden source entry conditional only on its observed
owned entry view, then the original complete chronological word, retains the
entry tag when actual focal recall selects the filled current view. The
original source entry mixture remains correlated; identifying it with the
physical saved-entry law is a separate obligation. -/
theorem phaseTimingWordPlanPolicy_entry_posterior_of_history
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    (earlier : SourceProgram.CommitPrefix Γ O Δ P) (later : SourceProgram.CommitPrefix Δ P Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (profile : SourceProgram.BehavioralProfile (earlier.prepend (later.prepend suffix)))
    (entry : SourceProgram.Config Player L Γ)
    (entryLaw : PMF (SourceProgram.Config Player L Γ)) (admitted : entry ∈ entryLaw.support)
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
    let fullProfile := cast (congrArg SourceProgram.BehavioralProfile
      (earlier.prepend_append later suffix).symm) profile
    let selectedEntries := fiberPosterior entryLaw (SourceProgram.Config.view who) (entry.view who)
    let tagged := selectedEntries.bind fun original =>
      ((earlier.append later).prefixLaw suffix fullProfile original).map (Prod.mk original)
    let originalJoint := entryLaw.bind fun original =>
      ((earlier.append later).prefixLaw suffix fullProfile original).map (Prod.mk original)
    let family := phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon
      scheduler bound fallback wellFormed source (earlier.append later) low generation slotWeight
        slotNonnegative slotBounded timingPlan who
    let filled := fillCommitPrefix setup.program earlier (later.prepend suffix) embedding
      control.execution.application.current.native.config.store entry
    ((app).policyMixture prior family).policy.Consistent (control.execution.recall who) →
      filled.view who ∈ (before.map (SourceProgram.Config.view who)).support ∧
        ((app).policyMixture tagged
          (fun pair => family (pair.2.view who))).posterior (control.execution.recall who) =
            fiberPosterior originalJoint (fun pair => later.entryView who (pair.2.view who))
              (filled.view who) := by
  classical
  intro current before completeLaw prior fullProfile selectedEntries tagged originalJoint family
    filled consistent
  obtain ⟨present, ownPosterior⟩ := phaseTimingWordPlanPolicy_posterior_filled_of_history setup mode
    runtime leaks bounds runtimePlan inputs horizon scheduler bound fallback wellFormed source
      earlier later suffix profile entry embedding low generation rank actions slotWeight
        slotNonnegative slotBounded timingPlan who trace clear selected request inside atEnd
          address unsent consistent
  refine ⟨present, ?_⟩
  have wordLaw : (earlier.append later).prefixLaw suffix fullProfile entry = completeLaw := by
    simpa only [fullProfile, cast_cast, cast_eq] using
      earlier.prefixLaw_append later suffix fullProfile entry
  have entryProjection := (earlier.append later).ownedEntryWordKernel_at_entry suffix fullProfile
    entryLaw entry admitted who
  have projected : tagged.map (fun pair => pair.2.view who) = prior := by
    change ((selectedEntries.bind fun original =>
      ((earlier.append later).prefixLaw suffix fullProfile original).map (Prod.mk original)).map
        (fun pair => pair.2.view who)) = prior
    simpa only [SourceProgram.CommitPrefix.ownedEntryWordKernel, selectedEntries,
      PMF.map_bind, PMF.map_comp, Function.comp_def, wordLaw] using entryProjection
  have viewPresent : filled.view who ∈ (prior.map (later.entryView who)).support := by
    rw [earlier.prefixLaw_split_entryView later suffix profile entry who]
    exact present
  have taggedPresent : filled.view who ∈ (tagged.map
      (fun pair => later.entryView who (pair.2.view who))).support := by
    change filled.view who ∈ (tagged.map
      ((later.entryView who) ∘ (fun pair => pair.2.view who))).support
    rw [← PMF.map_comp, projected]
    exact viewPresent
  have collapse := source_entry_fiber_redundant earlier later suffix fullProfile entryLaw entry
    admitted who (filled.view who) taggedPresent
  refine Eq.trans ?_ collapse
  apply posterior_projected_fiber setup mode runtime leaks tagged (fun pair => pair.2.view who)
    family (later.entryView who) (filled.view who) (control.execution.recall who)
  · intro recalled view response first second left right
    exact phaseTimingWordPlanPolicy_apply_eq_of_support setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed source (earlier.append later) low generation
        slotWeight slotNonnegative slotBounded timingPlan who first second recalled view response
          left right
  · simpa only [projected] using consistent
  · simpa only [projected] using ownPosterior
  · simpa only [projected] using viewPresent

end Vegas
