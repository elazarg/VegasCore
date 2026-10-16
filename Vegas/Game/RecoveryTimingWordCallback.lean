/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryTimingWordFixedRealization
import Vegas.Pending.PhaseBindingMemoryCallback
import Interaction.ReactiveAnchoredMixture
import Vegas.Game.RecoveryFixedCommitGeometry
import Vegas.Pending.PhaseNativeInvariant
import Vegas.Pending.PhaseFailureCoverage
import Vegas.Pending.PhaseBindingReadiness

/-! # Total actual commitment callbacks realize the original anchored word mixture -/

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

local instance timingWordCallbackRealizationPoolFintype :
    Fintype (FreeKeyedPool isFree isKeyed poolKey) := Fintype.ofFinite _

open Classical in
/-- Every actual clear active callback in the same commitment block is
realized by the original anchored word mixture. Unsent binding responses use
the exact source law; sent or absent requests have the actual singleton menu. -/
theorem RecoverySourceCheckpoint.timing_word_anchored_policy_at_callback
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
    (owner : Player)
    (actingControl : control.actor = some owner)
    (fallback : (who : Player) → (N).Policy who)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (weights : (p : Pool) → PMF (Parts p))
    (capacity : horizon ≤ bounds.candidateCount)
    (values : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
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
  have interval := checkpoint.commit_phase_geometry block suffix reconstruct positive boundary
    exclusion.frontier geometry.2.2 phase remaining installed
  by_cases usable : ∃ coordinate, control.execution.application.SeedRequest owner coordinate ∧
      ∀ message ∈ (app).outputs (control.execution.recall owner),
        PhaseCount.event? message.payload ≠ some coordinate
  · obtain ⟨coordinate, request, unsent⟩ := usable
    obtain ⟨actual, head, inside⟩ := request.2.1
    have same : actual = phase := by
      simpa only [installed, List.head?_cons, Option.mem_def, Option.some.injEq] using head.symm
    subst actual
    have fields := phase.fields coordinate.event ((phase.mem_events coordinate.event).mp inside).1
      ((phase.mem_events coordinate.event).mp inside).2
    rw [interval.1] at fields
    obtain ⟨actor, payload, binding⟩ := fields
    have actorEq := ((serviceGraph setup mode).actor?_of_outputLayout_binding binding).symm.trans
      request.2.2.2.1
    cases Option.some.inj actorEq
    have current : coordinate = ⟨control.execution.application.attempt, coordinate.event⟩ := by
      cases coordinate with
      | mk tag event =>
          simp only [CommitAttemptEvent.mk.injEq]
          exact ⟨request.1, trivial⟩
    rw [current] at request unsent
    exact RecoverySourceCheckpoint.timing_word_anchored_policy_of_fixed_block setup mode runtime
      leaks bounds runtimePlan inputs horizon scheduler bound trace maximal clearCurrent checkpoint
        wellFormed assessment residual raw block suffix reconstruct phase remaining installed
          positive boundary owner coordinate.event payload inside binding request unsent
            actingControl fallback slotWeight slotNonnegative slotBounded weights capacity
              (values payload) anchor anchorTrace entryFresh consistent
  · have sameControl : control = ⟨control.remaining, some owner, control.execution⟩ := by
      cases control with
      | mk fuel actor execution => cases actingControl; rfl
    have activeTrace : ((menu).protocol initial horizon scheduler).Trace
        (some ⟨control.remaining, some owner, control.execution⟩) := sameControl ▸ trace
    have singleton := PhaseCount.onePacketActions_eq_singleton_of_no_unsent runtime leaks bounds
      runtimePlan (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler
        control.remaining owner control.execution activeTrace usable
    have own : flat.policy (control.execution.recall owner)
        (control.execution.observe (app) owner) = PMF.pure ⟨none⟩ := by
      apply pmf_eq_pure_of_support_subset_singleton
      intro action supported
      rw [ReactiveApplication.policyMixture_policy] at supported
      obtain ⟨memory, _present, selected⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      have covered := (menu).anchoredPolicy_covered initial horizon scheduler anchor anchorTrace
        (fun _ => phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon
          scheduler
          bound fallback wellFormed assessment block control.execution.application.attempt.phase
            control.execution.application.generation slotWeight slotNonnegative slotBounded
              memory.1 owner memory.2) owner
        (fun past view response member =>
          (menu).decode_embedPolicy_covered initial horizon scheduler owner _ past view response
            member)
        (control.execution.recall owner) (control.execution.observe (app) owner) action selected
      change action ∈ PhaseCount.onePacketActions runtime leaks bounds owner
        (control.execution.recall owner) (control.execution.observe (app) owner) at covered
      rw [singleton] at covered
      exact Finset.mem_singleton.mp covered
    have target : ((menu).decodeProfile initial horizon scheduler profile) owner
        (control.execution.recall owner) (control.execution.observe (app) owner) =
          PMF.pure ⟨none⟩ := by
      apply pmf_eq_pure_of_support_subset_singleton
      intro action supported
      have covered := (menu).decode_embedPolicy_covered initial horizon scheduler owner _
        (control.execution.recall owner) (control.execution.observe (app) owner) action supported
      change action ∈ PhaseCount.onePacketActions runtime leaks bounds owner
        (control.execution.recall owner) (control.execution.observe (app) owner) at covered
      rw [singleton] at covered
      exact Finset.mem_singleton.mp covered
    exact own.trans target.symm

end Vegas
