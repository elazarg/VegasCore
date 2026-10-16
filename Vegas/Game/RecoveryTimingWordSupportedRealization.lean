/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryTimingWordPlanRealization
import Vegas.Game.PhaseTimingWordSupportedRun

/-! # Actual supported original-word callback realization -/

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

local instance timingWordSupportedCallbackPoolFintype :
    Fintype (FreeKeyedPool isFree isKeyed poolKey) := Fintype.ofFinite _

open Classical in
/-- An ORIGINAL plan-and-source-word row of the actual physical command law
supplies the recall consistency needed for the real zero-RAW assembled callback.
No final consistency or source/native posterior identity is assumed. -/
theorem RecoverySourceCheckpoint.timing_word_policy_of_original_run
    {control : (app).Control}
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
    (count : Nat) (bounded : count < horizon) (draw : (serviceGraph setup mode).Inputs)
    (plan : (p : Pool) → Parts p) (complete : SourceProgram.Config Player L Ξ) :
    let typed := cast (congrArg SourceProgram.BehavioralProfile reconstruct.symm) residual
    let rest := SourceProgram.CommitPrefix.commit name owner fresh guard later
    let current := earlier.tailProfile (rest.prepend suffix) typed
    let before := earlier.prefixLaw (rest.prepend suffix) typed checkpoint.source
    let completeLaw := before.bind (rest.prefixLaw suffix current)
    let prior := completeLaw.map (SourceProgram.Config.view owner)
    let family := fun plan => phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed assessment (earlier.append rest)
        control.execution.application.attempt.phase control.execution.application.generation
          slotWeight slotNonnegative slotBounded plan owner
    let original := (independentProduct weights).bind fun plan => prior.map (Prod.mk plan)
    let flat := (app).policyMixture original (fun memory => family memory.1 memory.2)
    let profile := (N).agentBehavior (N).playedInformation fallback (fun agent =>
      (weights (phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler bound
        agent)).bind (phaseTimingComponent setup mode runtime leaks bounds initial horizon
          scheduler bound wellFormed assessment 0 le_rfl (by norm_num) slotWeight slotNonnegative
            slotBounded agent))
    (draw, plan, complete, some control) ∈ (inputs.bind fun input =>
      (independentProduct weights).bind fun selectedPlan => completeLaw.bind fun word =>
        ((app).commandControlLaw scheduler (fun who => phaseTimingWordPlanPolicy setup mode
          runtime leaks bounds initial horizon scheduler bound fallback wellFormed assessment
            (earlier.append rest) control.execution.application.attempt.phase
              control.execution.application.generation slotWeight slotNonnegative slotBounded
                selectedPlan who (word.view who))
          (PMF.pure (PhaseRuntimeState.initial runtimePlan input)) (horizon - count - 1)
            count).map (fun result => (input, selectedPlan, word, result))).support →
      flat.policy (control.execution.recall owner) (control.execution.observe (app) owner) =
        ((menu).decodeProfile initial horizon scheduler profile) owner
          (control.execution.recall owner) (control.execution.observe (app) owner) := by
  intro typed rest current before completeLaw prior family original flat profile supported
  let appendedProfile := cast (congrArg SourceProgram.BehavioralProfile
    (earlier.prepend_append rest suffix).symm) typed
  have wordLaw : (earlier.append rest).prefixLaw suffix appendedProfile checkpoint.source =
      completeLaw := by
    simpa only [appendedProfile, cast_cast, cast_eq] using
      earlier.prefixLaw_append rest suffix appendedProfile checkpoint.source
  have actual := phaseTimingWordPlanPolicy_consistent_of_original_run setup mode runtime leaks
    bounds runtimePlan inputs horizon scheduler bound fallback wellFormed assessment
      (earlier.append rest) control.execution.application.attempt.phase
        control.execution.application.generation slotWeight slotNonnegative slotBounded weights
          suffix appendedProfile checkpoint.source count bounded draw plan complete control
            (by simpa only [wordLaw] using supported)
  obtain ⟨⟨trace⟩, consistent⟩ := actual
  have own : flat.policy.Consistent (control.execution.recall owner) := by
    simpa only [wordLaw] using (consistent owner).1
  exact RecoverySourceCheckpoint.timing_word_policy_of_history setup mode runtime leaks bounds
    runtimePlan inputs horizon scheduler bound trace maximal clearCurrent checkpoint wellFormed
      assessment residual raw fresh guard later suffix earlier reconstruct clear stored selected
        atEnd ready acting notPublication valid reachable retained saved fallback slotWeight
          slotNonnegative slotBounded weights request unsent actingControl binding capacity values
            own

end Vegas
