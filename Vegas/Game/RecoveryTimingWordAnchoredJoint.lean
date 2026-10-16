/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingWordPlanFilledPosterior
import Vegas.Game.RecoveryTimingWordAnchoredPrediction
import Vegas.Game.PhaseTimingWordAnchoredUnread
import Interaction.ReactiveNestedPolicyMixture

/-! # Original timing weights and actual AUX next choices jointly -/

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

local instance timingWordAnchoredJointPoolFintype :
    Fintype (FreeKeyedPool isFree isKeyed poolKey) := Fintype.ofFinite _

open Classical in
/-- At a genuine clear callback the ORIGINAL plan-weight product and
original chronological word prior give the actual unread timing part and
genuine AUX next choice independently. Every supported fixed plan retains
the SAME actual filled-view word fiber; no target posterior is assumed. -/
theorem RecoverySourceCheckpoint.timing_word_anchored_current_joint_of_history
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
    (clear : control.execution.application.entry.excluded = ∅)
    (stored : control.execution.application.StoredCheckpoint)
    (selected : Fin (eventCount checkpoint.residual.tail))
    (atEnd : selected.val = earlier.length)
    (ready : control.execution.application.current.native.config.cut.Ready
      (checkpoint.embedding.event selected))
    (acting : (serviceGraph setup mode).actor? (checkpoint.embedding.event selected) = some owner)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout
      (checkpoint.embedding.event selected)).IsPublication)
    (valid : control.execution.application.current.native.BindingInvariant) {nativeInputs}
    (reachable : control.execution.application.current.native.config.Reachable nativeInputs)
    (retained : control.execution.application.HistoryCheckpoint)
    (saved : control.execution.application.entry.native.config.cut.IsPrefix
      control.execution.application.attempt.phase)
    (fallback : (who : Player) → (N).Policy who)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (weights : (p : Pool) → PMF (Parts p))
    (played : some (control.execution.recall owner, control.execution.observe (app) owner) ∈
      (N).playedInformation owner)
    (request : control.execution.application.SeedRequest owner
      ⟨control.execution.application.attempt, checkpoint.embedding.event selected⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall owner),
      PhaseCount.event? message.payload ≠
        some ⟨control.execution.application.attempt, checkpoint.embedding.event selected⟩)
    (anchor : (app).Control)
    (anchorTrace : ((menu).protocol initial horizon scheduler).Trace (some anchor))
    (entryFresh : ∀ record ∈ anchor.execution.recall owner,
      record.beforeView.application.2.attempt ≠ control.execution.application.attempt) :
    let typed := cast (congrArg SourceProgram.BehavioralProfile reconstruct.symm) residual
    let rest := SourceProgram.CommitPrefix.commit name owner fresh guard later
    let current := earlier.tailProfile (rest.prepend suffix) typed
    let before := earlier.prefixLaw (rest.prepend suffix) typed checkpoint.source
    let prior := (before.bind (rest.prefixLaw suffix current)).map (SourceProgram.Config.view owner)
    let embedding := cast (congrArg
      (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) reconstruct.symm) checkpoint.embedding
    let filled := fillCommitPrefix setup.program earlier (rest.prepend suffix) embedding
      control.execution.application.current.native.config.store checkpoint.source
    let baseFamily := fun plan => phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed assessment (earlier.append rest)
        control.execution.application.attempt.phase control.execution.application.generation
          slotWeight slotNonnegative slotBounded plan owner
    let family := fun plan word => ReactiveApplication.anchoredPolicy anchor.execution
      (fun _ => baseFamily plan word) owner
    let original := (independentProduct weights).bind fun plan => prior.map (Prod.mk plan)
    let flat := (app).policyMixture original (fun memory => family memory.1 memory.2)
    let outer := (app).policyMixture (independentProduct weights)
      (fun plan => ((app).policyMixture prior (family plan)).policy)
    let common := fiberPosterior prior (rest.entryView owner) (filled.view owner)
    let agent : Agent := ⟨owner, ⟨some (control.execution.recall owner,
      control.execution.observe (app) owner), played⟩⟩
    let sourceLaw := (setup.commitRecoveryNonmissingProfile assessment.strategy owner
      (setup.commitRecoveryClearInformation wellFormed owner
        (phaseSourceView? setup mode runtime leaks owner (checkpoint.embedding.event selected)
          (control.execution.observe (app) owner)))).map
            (fun choice => CommitRecoveryMove.underlying choice.1)
    flat.policy.Consistent (control.execution.recall owner) →
      flat.posterior (control.execution.recall owner) =
          (outer.posterior (control.execution.recall owner)).bind (fun plan =>
            common.map (Prod.mk plan)) ∧
        (flat.posterior (control.execution.recall owner)).map (fun memory =>
          (memory.1 (phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler
            bound agent), (earlier.append rest).wordAction owner earlier.length memory.2)) =
          (weights (phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler
            bound agent)).bind (fun part => sourceLaw.map (Prod.mk part)) := by
  classical
  intro typed rest current before prior typedEmbedding filled baseFamily family original flat outer
    common
    agent sourceLaw consistent
  let past := control.execution.recall owner
  let view := control.execution.observe (app) owner
  let selectedPool := phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler
    bound agent
  let read := (earlier.append rest).wordAction owner earlier.length
  have hierarchical := (app).policyMixture_hierarchical (independentProduct weights) prior family
    past consistent
  have each (plan) (supported : plan ∈ (outer.posterior past).support) :
      ((app).policyMixture prior (family plan)).posterior past = common ∧
        (((app).policyMixture prior (family plan)).posterior past).map read = sourceLaw := by
    have innerConsistent := (app).policyMixture_member_consistent (independentProduct weights)
      (fun plan => ((app).policyMixture prior (family plan)).policy) past hierarchical.2 plan
        supported
    exact RecoverySourceCheckpoint.timing_word_anchored_predicts_of_history setup mode runtime leaks
      bounds runtimePlan inputs horizon scheduler bound trace maximal clearCurrent checkpoint
        wellFormed assessment residual raw fresh guard later suffix earlier reconstruct clear
          stored selected atEnd ready acting notPublication valid reachable retained saved fallback
            slotWeight slotNonnegative slotBounded plan request unsent anchor anchorTrace entryFresh
              innerConsistent
  have tower : flat.posterior past = (outer.posterior past).bind
      (fun plan => common.map (Prod.mk plan)) := by
    refine hierarchical.1.trans ?_
    apply bind_congr_on_support _
    intro plan supported
    rw [(each plan supported).1]
  obtain ⟨witness, admitted⟩ := (outer.posterior past).support_nonempty
  have predicted : common.map read = sourceLaw := by
    rw [← (each witness admitted).1]
    exact (each witness admitted).2
  obtain ⟨remainder, currentPart⟩ := phaseTimingWordAnchoredPolicy_posterior_current_part setup mode
    runtime leaks bounds initial horizon scheduler bound fallback wellFormed assessment
      (earlier.append rest) control.execution.application.attempt.phase
        control.execution.application.generation slotWeight slotNonnegative slotBounded
          anchor.execution weights
          owner prior past view played
  have partMarginal : (flat.posterior past).map (fun memory => memory.1 selectedPool) =
      weights selectedPool := by
    have projected := congrArg (PMF.map Prod.fst) currentPart
    simp only [PMF.map_comp, PMF.map_bind] at projected
    change (flat.posterior past).map (fun memory => memory.1 selectedPool) =
      (weights selectedPool).bind (fun part => remainder.map (Function.const _ part)) at projected
    simpa only [PMF.map_const, PMF.bind_pure] using projected
  have outerPart : (outer.posterior past).map (fun plan => plan selectedPool) =
      weights selectedPool := by
    rw [tower] at partMarginal
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at partMarginal
    change ((outer.posterior past).bind fun plan => common.map
      (Function.const _ (plan selectedPool))) = weights selectedPool at partMarginal
    simp only [PMF.map_const] at partMarginal
    exact partMarginal
  refine ⟨tower, ?_⟩
  have jointMap : (flat.posterior past).map
      (fun memory => (memory.1 selectedPool, read memory.2)) =
        ((outer.posterior past).map (fun plan => plan selectedPool)).bind
          (fun part => (common.map read).map (Prod.mk part)) := by
    rw [tower]
    simp only [PMF.map_bind, PMF.map_comp, PMF.bind_map, Function.comp_def]
  change (flat.posterior past).map (fun memory => (memory.1 selectedPool, read memory.2)) = _
  rw [jointMap, outerPart, predicted]

end Vegas
