/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingWordPlanFilledPosterior
import Vegas.Game.RecoveryBindingProfileLaw

/-! # Actual AUX kernels after complete timing-plan recall -/

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

/-- At an authentic initialized callback, the actual whole varying-plan
recall predicts the genuine AUX nonmissing choice law under the SAME fixed
residual profile. Only its structural all-point raw law is required. -/
theorem RecoverySourceCheckpoint.timing_word_predicts_of_history
    {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
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
    (timingPlan : (p : Pool) → Parts p)
    (request : control.execution.application.SeedRequest owner
      ⟨control.execution.application.attempt, checkpoint.embedding.event selected⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall owner),
      PhaseCount.event? message.payload ≠
        some ⟨control.execution.application.attempt, checkpoint.embedding.event selected⟩) :
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
    let family := phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon
      scheduler bound fallback wellFormed assessment (earlier.append rest)
        control.execution.application.attempt.phase control.execution.application.generation
          slotWeight slotNonnegative slotBounded timingPlan owner
    ((app).policyMixture prior family).policy.Consistent (control.execution.recall owner) →
      ((app).policyMixture prior family).posterior (control.execution.recall owner) =
          fiberPosterior prior (rest.entryView owner) (filled.view owner) ∧
      (((app).policyMixture prior family).posterior (control.execution.recall owner)).map
          ((earlier.append rest).wordAction owner earlier.length) =
        (setup.commitRecoveryNonmissingProfile assessment.strategy owner
          (setup.commitRecoveryClearInformation wellFormed owner
            (phaseSourceView? setup mode runtime leaks owner (checkpoint.embedding.event selected)
              (control.execution.observe (app) owner)))).map
                (fun choice => CommitRecoveryMove.underlying choice.1) := by
  intro typed rest current before prior typedEmbedding filled family consistent
  have sourceLaw := checkpoint.binding_kernel_source_of_ready runtime leaks control.execution
    wellFormed assessment residual raw fresh guard later suffix earlier reconstruct clear stored
      selected atEnd ready acting notPublication valid reachable retained saved
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, entry, refs, registry, embedding, beforeRefs,
    compiled, terminalAlignment, agrees, guards, failures, unique, ranks, actors, commits, owners,
    endpoints, automatic, histories, memories, steps, menus, readout, initialized, views,
    savedHistory, origin⟩
  dsimp only at *
  change SourceProgram.CommitPrefix Γ O Δ P at earlier
  change earlier.prepend (.commit name owner fresh guard (later.prepend suffix)) = program
    at reconstruct
  subst program
  have inside : control.execution.application.attempt.phase ≤ (embedding.event selected).val ∧
      (embedding.event selected).val < control.execution.application.attempt.phase +
        (earlier.append (.commit name owner fresh guard later)).length := by
    rw [compiled.rankEq selected, atEnd]
    simp only [SourceProgram.CommitPrefix.length_append, SourceProgram.CommitPrefix.length]
    omega
  have atRank : (embedding.event selected).val =
      control.execution.application.attempt.phase + earlier.length := by
    rw [compiled.rankEq selected, atEnd]
  have address : control.execution.application.attempt =
      ⟨control.execution.application.attempt.phase, control.execution.application.generation⟩ := rfl
  have posterior := phaseTimingWordPlanPolicy_posterior_filled_of_history setup mode runtime
    leaks bounds runtimePlan inputs horizon scheduler bound fallback wellFormed assessment
      earlier (.commit name owner fresh guard later) suffix residual entry embedding
        control.execution.application.attempt.phase control.execution.application.generation
          compiled.rankEq views.actionEq slotWeight slotNonnegative slotBounded timingPlan owner
            trace clearCurrent (embedding.event selected) request inside atRank address
              unsent
              consistent
  have prediction := phaseTimingWordPlanPolicy_next_action_of_history setup mode runtime leaks
    bounds runtimePlan inputs horizon scheduler bound fallback wellFormed assessment fresh guard
      earlier later suffix residual entry embedding control.execution.application.attempt.phase
        control.execution.application.generation compiled.rankEq views.actionEq slotWeight
          slotNonnegative slotBounded timingPlan trace clearCurrent
            (embedding.event selected)
            request inside atRank address unsent consistent
  exact ⟨posterior.2, prediction.trans sourceLaw⟩

end Vegas
