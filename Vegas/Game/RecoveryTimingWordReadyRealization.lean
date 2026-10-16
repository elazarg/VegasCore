/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryTimingWordAnchoredRealization
import Vegas.Game.RecoveryFixedCommitSelector
import Vegas.Pending.PhaseNativeInvariant
import Vegas.Pending.PhaseFailureCoverage
import Vegas.Pending.PhaseBindingReadiness

/-! # Actual clear binding histories discharge anchored callback invariants -/

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

local instance timingWordReadyRealizationPoolFintype :
    Fintype (FreeKeyedPool isFree isKeyed poolKey) := Fintype.ofFinite _

open Classical in
/-- At an actual clear ready binding, all native checkpoint, receipt, and
history conditions of the anchored word realization follow from the counted
trace. The exact typed source prefix and original product prior are retained. -/
theorem RecoverySourceCheckpoint.timing_word_anchored_policy_of_ready
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
    {Δ Ξ : SourceCtx Player L} {P Q : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} (fresh : name ∉ Δ.map Prod.fst)
    (guard : SourceGuard L Δ owner name payload)
    (later : SourceProgram.CommitPrefix ((name, .commitment owner payload) :: Δ)
      (insert name P) Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (reconstruct : earlier.prepend (.commit name owner fresh guard (later.prepend suffix)) =
      checkpoint.residual.tail)
    (selected : Fin (eventCount checkpoint.residual.tail))
    (atEnd : selected.val = earlier.length)
    (fallback : (who : Player) → (N).Policy who)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (weights : (p : Pool) → PMF (Parts p))
    (request : control.execution.application.SeedRequest owner
      ⟨control.execution.application.attempt, checkpoint.embedding.event selected⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall owner),
      PhaseCount.event? message.payload ≠
        some ⟨control.execution.application.attempt, checkpoint.embedding.event selected⟩)
    (actingControl : control.actor = some owner)
    (binding : (serviceGraph setup mode).outputLayout (checkpoint.embedding.event selected) =
      .binding owner payload)
    (capacity : horizon ≤ bounds.candidateCount)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (anchor : (app).Control)
    (anchorTrace : ((menu).protocol initial horizon scheduler).Trace (some anchor))
    (entryFresh : ∀ record ∈ anchor.execution.recall owner,
      record.beforeView.application.2.attempt ≠ control.execution.application.attempt) :
    let typed := cast (congrArg SourceProgram.BehavioralProfile reconstruct.symm) residual
    let rest := SourceProgram.CommitPrefix.commit name owner fresh guard later
    let current := earlier.tailProfile (rest.prepend suffix) typed
    let before := earlier.prefixLaw (rest.prepend suffix) typed checkpoint.source
    let prior := (before.bind (rest.prefixLaw suffix current)).map (SourceProgram.Config.view owner)
    let baseFamily := fun plan => phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed assessment (earlier.append rest)
        control.execution.application.attempt.phase control.execution.application.generation
          slotWeight slotNonnegative slotBounded plan owner
    let family := fun plan word => ReactiveApplication.anchoredPolicy anchor.execution
      (fun _ => baseFamily plan word) owner
    let original := (independentProduct weights).bind fun plan => prior.map (Prod.mk plan)
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
  intro typed rest current before prior baseFamily family original flat profile consistent
  have physical := (menu).toRawTrace initial horizon scheduler trace
  have exclusion := phaseExclusionRecord_history runtime leaks runtimePlan inputs horizon
    scheduler physical
  have bindings := phaseBindingRecord_history runtime leaks runtimePlan inputs horizon
    scheduler physical
  have stored := phaseStoredCheckpoint_history runtime leaks runtimePlan inputs horizon
    scheduler physical
  have retained := phaseHistoryCheckpoint_history runtime leaks runtimePlan inputs horizon
    scheduler physical
  have coverage := phaseFailureCoverage_history runtime leaks runtimePlan inputs horizon
    scheduler physical
  obtain ⟨draw, native⟩ := phaseNativeInvariant_history runtime leaks runtimePlan inputs horizon
    scheduler physical
  have clear : control.execution.application.entry.excluded = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro player excluded
    have current := coverage.inherited excluded
    rw [clearCurrent] at current
    exact Finset.notMem_empty _ current
  obtain ⟨phase, remaining, installed, _kind, _inside⟩ := phase_ready_binding_phase runtime leaks
    runtimePlan (serviceGraph_revealRelaxedOrdered setup mode) maximal inputs horizon scheduler
      physical owner (checkpoint.embedding.event selected) payload binding request.2.2.1
  have saved : control.execution.application.entry.native.config.cut.IsPrefix
      control.execution.application.attempt.phase := by
    have position := exclusion.frontier.positioned
    rw [installed] at position
    simpa only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some] using position.1
  exact RecoverySourceCheckpoint.timing_word_anchored_policy_of_history setup mode runtime leaks
    bounds runtimePlan inputs horizon scheduler bound trace maximal clearCurrent checkpoint
      wellFormed assessment
      residual raw fresh guard later suffix earlier reconstruct clear stored selected atEnd
        request.2.2.1 request.2.2.2.1
          (by simp only [binding, EventField.IsPublication, not_false_eq_true]) bindings.active
          native.active.reachable retained saved fallback slotWeight slotNonnegative slotBounded
            weights request unsent actingControl binding capacity values anchor anchorTrace
              entryFresh consistent

end Vegas
