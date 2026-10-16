/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryTimingWordReadyRealization
import Vegas.Game.RecoveryFixedCommitGeometry
import Vegas.Pending.PhaseNativeInvariant
import Vegas.Pending.PhaseFailureCoverage
import Vegas.Pending.PhaseBindingReadiness

/-! # The original complete source block realizes actual anchored binding callbacks -/

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

local instance timingWordFixedRealizationPoolFintype :
    Fintype (FreeKeyedPool isFree isKeyed poolKey) := Fintype.ofFinite _

open Classical in
/-- A callback inside the given original commitment block uses its SAME complete
word law. The actual event selects its typed prefix; source prior factorization
and all native history conditions are derived, including accepted failures. -/
theorem RecoverySourceCheckpoint.timing_word_anchored_policy_of_fixed_block
    {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (clearCurrent : control.execution.application.current.excluded = ∅)
    (checkpoint : RecoverySourceCheckpoint setup mode control.execution.application)
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (residual : SourceProgram.BehavioralProfile checkpoint.residual.tail)
    (raw : ∀ owner point,
      (residual owner).protocolAction checkpoint.residual.tail
          (ProtocolState.observe owner checkpoint.residual.tail point) =
        (setup.commitRecoveryNonmissingProfile assessment.strategy owner
          (setup.commitRecoveryClearInformation wellFormed owner
            (some (ProtocolState.observe owner setup.program
              (checkpoint.residual.lift point))))).map
                (fun choice => CommitRecoveryMove.underlying choice.1))
    {Ξ : SourceCtx Player L} {Q : Finset VarId}
    (block : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (reconstruct : block.prepend suffix = checkpoint.residual.tail)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : control.execution.application.phases = phase :: remaining)
    (positive : 0 < block.length) (boundary : IsCommitBoundary suffix)
    (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (inside : event ∈ phase.events)
    (binding : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (request : control.execution.application.SeedRequest owner
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (actingControl : control.actor = some owner)
    (fallback : (who : Player) → (N).Policy who)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (weights : (p : Pool) → PMF (Parts p))
    (capacity : horizon ≤ bounds.candidateCount)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (anchor : (app).Control)
    (anchorTrace : ((menu).protocol initial horizon scheduler).Trace (some anchor))
    (entryFresh : ∀ record ∈ anchor.execution.recall owner,
      record.beforeView.application.2.attempt ≠ control.execution.application.attempt) :
    let typed := cast (congrArg SourceProgram.BehavioralProfile reconstruct.symm) residual
    let wordLaw := block.prefixLaw suffix typed checkpoint.source
    let family := fun plan word => ReactiveApplication.anchoredPolicy anchor.execution
      (fun _ => phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler
        bound fallback wellFormed assessment block control.execution.application.attempt.phase
          control.execution.application.generation slotWeight slotNonnegative slotBounded plan
            owner word) owner
    let original := (independentProduct weights).bind fun plan =>
      (wordLaw.map (SourceProgram.Config.view owner)).map (Prod.mk plan)
    let flat := (app).policyMixture original (fun memory => family memory.1 memory.2)
    let profile := (N).agentBehavior (N).playedInformation fallback (fun agent =>
      (weights (phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler bound
        agent)).bind (phaseTimingComponent setup mode runtime leaks bounds initial horizon
          scheduler bound wellFormed assessment 0 le_rfl (by norm_num) slotWeight slotNonnegative
            slotBounded agent))
    flat.policy.Consistent (control.execution.recall owner) →
      flat.policy (control.execution.recall owner) (control.execution.observe (app) owner) =
        ((menu).decodeProfile initial horizon scheduler profile) owner
          (control.execution.recall owner) (control.execution.observe (app) owner) := by
  intro typed wordLaw family original flat profile consistent
  have exclusion := phaseExclusionRecord_history runtime leaks runtimePlan inputs horizon scheduler
    ((menu).toRawTrace initial horizon scheduler trace)
  have geometry := phasePlanGeometry_history runtime leaks runtimePlan maximal inputs horizon
    scheduler ((menu).toRawTrace initial horizon scheduler trace)
  have interval := checkpoint.commit_block_phase_geometry block suffix reconstruct positive boundary
    exclusion.frontier geometry.2.2 phase remaining installed
  obtain ⟨selected, selectedEq, Δ, P, name, fresh, guard, earlier, later, atEnd, sameBlock,
    reconstructed⟩ := checkpoint.fixed_binding_prefix block suffix reconstruct exclusion.frontier
      phase remaining installed interval.2 event inside request.2.2.1 owner payload binding
  subst block
  let rest := SourceProgram.CommitPrefix.commit name owner fresh guard later
  let splitProfile := cast (congrArg SourceProgram.BehavioralProfile reconstructed.symm) residual
  let appendedProfile := cast (congrArg SourceProgram.BehavioralProfile
    (earlier.prepend_append rest suffix).symm) splitProfile
  have profiles : appendedProfile = typed := by
    simp only [appendedProfile, splitProfile, typed, cast_cast]
  have words : (earlier.append rest).prefixLaw suffix typed checkpoint.source =
      (earlier.prefixLaw (rest.prepend suffix) splitProfile checkpoint.source).bind
        (rest.prefixLaw suffix (earlier.tailProfile (rest.prepend suffix) splitProfile)) := by
    rw [← profiles]
    simpa only [appendedProfile, cast_cast, cast_eq] using
      earlier.prefixLaw_append rest suffix appendedProfile checkpoint.source
  have member : control.execution.application.SeedRequest owner
      ⟨control.execution.application.attempt, checkpoint.embedding.event selected⟩ :=
    selectedEq.symm ▸ request
  have waiting : ∀ message ∈ (app).outputs (control.execution.recall owner),
      PhaseCount.event? message.payload ≠
        some ⟨control.execution.application.attempt, checkpoint.embedding.event selected⟩ :=
    selectedEq.symm ▸ unsent
  have output : (serviceGraph setup mode).outputLayout (checkpoint.embedding.event selected) =
      .binding owner payload := selectedEq.symm ▸ binding
  have actual := RecoverySourceCheckpoint.timing_word_anchored_policy_of_ready setup mode runtime
    leaks bounds runtimePlan inputs horizon scheduler bound trace maximal clearCurrent checkpoint
      wellFormed assessment residual raw fresh guard later suffix earlier reconstructed selected
        atEnd.symm fallback slotWeight slotNonnegative slotBounded weights member waiting
          actingControl output capacity values anchor anchorTrace entryFresh
  dsimp only [flat, original, wordLaw, family] at consistent ⊢
  rw [words] at consistent ⊢
  exact actual consistent

end Vegas
