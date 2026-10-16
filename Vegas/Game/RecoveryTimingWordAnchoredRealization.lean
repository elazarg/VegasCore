/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingWordAnchoredFilledPosterior
import Vegas.Game.RecoveryTimingWordAnchoredJoint
import Vegas.Game.PhaseTimingWordBindingFactor

/-! # Actual residual response after anchored entry replay -/

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

local instance timingWordAnchoredRealizationPoolFintype :
    Fintype (FreeKeyedPool isFree isKeyed poolKey) := Fintype.ofFinite _

open Classical in
/-- The actual NON-RAW assembled residual response at a genuine clear
binding callback is realized by the ORIGINAL full timing-weight product and
chronological source word. The current part was unread; the full recalled
word posterior and genuine AUX choice law are derived. RAW remains separate. -/
theorem RecoverySourceCheckpoint.timing_word_anchored_policy_of_history
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
  let past := control.execution.recall owner
  let view := control.execution.observe (app) owner
  have running : ¬ ((menu).protocol initial horizon scheduler).terminal (some control) := by
    change ¬ (control.remaining = 0 ∧ control.actor = none)
    rintro ⟨_, idle⟩
    rw [actingControl] at idle
    cases idle
  have observed : (N).infoOf owner trace = some (past, view) :=
    ((menu).info initial horizon scheduler owner trace).trans (by
      simp only [ReactiveApplication.observe, actingControl, ite_true]
      rfl)
  have played := (N).mem_playedInformation (who := owner)
    (history := ⟨some control, trace⟩) running
  rw [observed] at played
  let agent : Agent := ⟨owner, ⟨some (past, view), played⟩⟩
  let selectedPool := phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler
    bound agent
  let read := (earlier.append rest).wordAction owner earlier.length
  let sourceLaw := (setup.commitRecoveryNonmissingProfile assessment.strategy owner
    (setup.commitRecoveryClearInformation wellFormed owner
      (phaseSourceView? setup mode runtime leaks owner (checkpoint.embedding.event selected)
        view))).map (fun choice => CommitRecoveryMove.underlying choice.1)
  have joint := RecoverySourceCheckpoint.timing_word_anchored_current_joint_of_history setup mode
    runtime
    leaks bounds runtimePlan inputs horizon scheduler bound trace maximal clearCurrent checkpoint
      wellFormed assessment residual raw fresh guard later suffix earlier reconstruct clear stored
        selected atEnd ready acting notPublication valid reachable retained saved fallback
          slotWeight
          slotNonnegative slotBounded weights played request unsent anchor anchorTrace entryFresh
          consistent
  have inside : control.execution.application.attempt.phase ≤
      (checkpoint.embedding.event selected).val ∧
        (checkpoint.embedding.event selected).val < control.execution.application.attempt.phase +
          (earlier.append rest).length := by
    rw [checkpoint.compiled.rankEq selected, atEnd]
    simp only [rest, SourceProgram.CommitPrefix.length_append, SourceProgram.CommitPrefix.length]
    omega
  have address : control.execution.application.attempt =
      ⟨control.execution.application.attempt.phase, control.execution.application.generation⟩ := rfl
  have readIndex : (checkpoint.embedding.event selected).val -
      control.execution.application.attempt.phase = earlier.length := by
    rw [checkpoint.compiled.rankEq selected, atEnd]
    omega
  obtain ⟨kernel, wordFactors, sourceFactors⟩ :=
    phaseTimingWordPlanPolicy_binding_factor_of_history setup mode runtime leaks bounds
      runtimePlan inputs horizon scheduler bound fallback wellFormed assessment
        (earlier.append rest) control.execution.application.attempt.phase
          control.execution.application.generation slotWeight slotNonnegative slotBounded
            control trace owner actingControl clearCurrent
              (checkpoint.embedding.event selected) payload
              binding request unsent inside address capacity values played
  rw [readIndex] at wordFactors
  have sampled := congrArg (fun law => law.bind fun pair => kernel pair.1 pair.2) joint.2
  simp only [PMF.bind_map, Function.comp_def, PMF.bind_bind] at sampled
  have target : ((menu).decodeProfile initial horizon scheduler profile) owner past view =
      (weights selectedPool).bind fun part =>
        (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
          wellFormed assessment 0 le_rfl (by norm_num) slotWeight slotNonnegative slotBounded
            agent part).map (fun choice => choice.1.getD ⟨none⟩) := by
    simp only [profile, ReactiveApplication.ResponseMenu.decodeProfile,
      ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy,
      PMF.map_comp, Function.comp_def, InformationModel.agentBehavior, dite_eq_left played,
      PMF.map_bind]
    rfl
  rw [ReactiveApplication.policyMixture_policy]
  calc
    _ = (weights selectedPool).bind (fun part => sourceLaw.bind (kernel part)) := by
      have factored : (flat.posterior past).bind (fun memory =>
          family memory.1 memory.2 past view) =
          (flat.posterior past).bind (fun memory =>
            kernel (memory.1 selectedPool) (read memory.2)) := by
        apply bind_congr_on_support _
        intro memory _
        have unchanged := phase_anchoredPolicy_of_fresh_attempt runtime leaks anchor.execution
          (fun _ => baseFamily memory.1 memory.2) owner control.execution.application.attempt
            entryFresh past view rfl
        exact unchanged.trans (wordFactors memory.1 memory.2)
      refine factored.trans ?_
      simpa only [sourceLaw, PMF.bind_map, Function.comp_def] using sampled
    _ = (weights selectedPool).bind (fun part =>
        (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
          wellFormed assessment 0 le_rfl (by norm_num) slotWeight slotNonnegative slotBounded
            agent part).map (fun choice => choice.1.getD ⟨none⟩)) := by
      apply bind_congr_on_support _
      intro part _
      exact (sourceFactors part).symm
    _ = _ := target.symm

end Vegas
