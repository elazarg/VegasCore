/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingMemorySourceMarginal
import Vegas.Game.RecoveryTimingStoppedMarginal
import Vegas.Game.RecoveryCommitPrefixSupport
import Vegas.Source.CommitPrefixFocalViewMarginal
import Interaction.ReactiveAnchoredStopped
import Interaction.ReactiveRecallReplay
import Vegas.Source.CommitPrefixProduct
import GameTheory.Math.Probability.ConditionalObservation

/-! # Literal zero-RAW physical law of the same source-current-view reference -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.InformationModel
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) horizon
      scheduler).History]
  [∀ who, DecidableEq
    (((PhaseCount.onePacketMenu runtime leaks bounds).information
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) horizon
        scheduler).InfoState who)]

local notation "graph" => serviceGraph setup mode
local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) (initial) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) (initial) horizon scheduler

local notation "Pool" => FreeKeyedPool
  (fun agent : (N).InformationAgent (N).playedInformation =>
    PhasePublicExclusion setup mode runtime leaks (Subtype.val (Sigma.snd agent)))
  (fun agent => PhaseUnprotected runtime leaks bound (Sigma.fst agent)
    (Subtype.val (Sigma.snd agent)))
  (fun agent => phaseTimingKey runtime leaks (Sigma.fst agent)
    (Subtype.val (Sigma.snd agent)))
local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

local instance timingSourceReferencePoolFintype : Fintype Pool := Fintype.ofFinite _

open Classical in
/-- The current-view ORIGINAL source reference has the literal actual zero-RAW
assembled target's full stopped-history marginal at the SAME source entry and
residual profile. Positivity comes from a typed prefix Attempt, not from a
hypothesis about source posteriors or factual RAW source origins. -/
theorem RecoverySourceCheckpoint.timing_word_anchored_reference_law
    {anchor : (app).Control}
    (anchorTrace : ((menu).protocol initial horizon scheduler).Trace (some anchor))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (clearEntry : anchor.execution.application.current.excluded = ∅)
    (checkpoint : RecoverySourceCheckpoint setup mode anchor.execution.application)
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (residual : SourceProgram.BehavioralProfile checkpoint.residual.tail)
    (raw : ∀ owner point,
      (residual owner).protocolAction checkpoint.residual.tail
          (ProtocolState.observe owner checkpoint.residual.tail point) =
        (setup.commitRecoveryNonmissingProfile assessment.strategy owner
          (setup.commitRecoveryClearInformation wellFormed owner
            (some (ProtocolState.observe owner setup.program
              (checkpoint.residual.lift point))))).map
                (fun choice => CommitRecoveryMove.underlying choice.1))
    {Δ Ξ : SourceCtx Player L} {P Q : Finset VarId}
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (later : SourceProgram.CommitPrefix Δ P Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (reconstruct : (earlier.append later).prepend suffix = checkpoint.residual.tail)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : anchor.execution.application.phases = phase :: remaining)
    (positive : 0 < (earlier.append later).length) (boundary : IsCommitBoundary suffix)
    (fallback : (who : Player) → (N).Policy who)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (weights : (p : Pool) → PMF (Parts p))
    (capacity : horizon ≤ bounds.candidateCount)
    (values : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (entryFresh : ∀ owner, ∀ record ∈ anchor.execution.recall owner,
      record.beforeView.application.2.attempt ≠ anchor.execution.application.attempt)
    (focal : Player) (intervention : (N).BehavioralPolicy focal)
    (filled : SourceProgram.Config Player L Δ)
    (attempt : earlier.Attempt checkpoint.source ∅ filled ∅)
    (certificate : ((menu).protocol initial horizon scheduler).WellFoundedHistories)
    (extra : ((menu).protocol initial horizon scheduler).History → Prop) :
    let block := earlier.append later
    let typed := cast (congrArg SourceProgram.BehavioralProfile reconstruct.symm) residual
    let wordLaw := block.prefixLaw suffix typed checkpoint.source
    let members := fun owner (memory : ((p : Pool) → Parts p) × DecisionView owner Ξ) =>
      ReactiveApplication.anchoredPolicy anchor.execution
        (fun _ => phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon
          scheduler
          bound fallback wellFormed assessment block anchor.execution.application.attempt.phase
            anchor.execution.application.generation slotWeight slotNonnegative slotBounded
              memory.1 owner memory.2) owner
    let profile := (N).agentBehavior (N).playedInformation fallback (fun agent =>
      (weights (phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler bound
        agent)).bind (phaseTimingComponent setup mode runtime leaks bounds initial horizon
          scheduler bound wellFormed assessment 0 le_rfl (by norm_num) slotWeight slotNonnegative
            slotBounded agent))
    let focalPolicy := (app).decodePolicy ((menu).embedPolicy initial horizon scheduler focal
      intervention)
    let family := fun owner memory =>
      if owner = focal then focalPolicy else members owner memory
    let stopped := fun history : ((menu).protocol initial horizon scheduler).History =>
      extra history ∨ match history.state with
        | none => True
        | some current => current.execution.application.current.excluded ≠ ∅ ∨
            current.execution.application.phases ≠ phase :: remaining
    let run := fun memories => (N).runBehavioralUntil certificate (fun who =>
      (menu).restrictPolicy initial horizon scheduler who (family who (memories who))) stopped
        ⟨some anchor, anchorTrace⟩
    let read := fun (plans : Player → ((p : Pool) → Parts p))
      (complete : SourceProgram.Config Player L Ξ) =>
        fun owner => (plans owner, complete.view owner)
    let reference := fiberPosterior wordLaw
      (fun complete => later.entryView focal (complete.view focal)) (filled.view focal)
    ((independentProduct (fun _ : Player => independentProduct weights)).bind fun plans =>
      reference.bind fun complete => run (read plans complete)) =
    (N).runBehavioralUntil certificate
      (GameTheory.Profile.update (sig := (N).behavioralSignature) profile focal intervention)
        stopped
        ⟨some anchor, anchorTrace⟩ := by
  intro block typed wordLaw members profile focalPolicy family stopped run read reference
  let inputs := setup.initialLaw.map (fun draw => encodeInputs draw)
  have initialEq : inputs.map (PhaseRuntimeState.initial plan) = initial := by
    simp only [inputs, PMF.map_comp, Function.comp_def]
  have originalLaw : ((independentProduct (fun _ : Player => independentProduct weights)).bind
      fun plans => wordLaw.bind fun complete => run (read plans complete)) =
      (N).runBehavioralUntil certificate
        (GameTheory.Profile.update (sig := (N).behavioralSignature) profile focal intervention)
          stopped ⟨some anchor, anchorTrace⟩ := by
    exact RecoverySourceCheckpoint.timing_word_anchored_stopped_marginal setup mode runtime leaks
      bounds plan inputs initial horizon scheduler bound initialEq.symm anchorTrace maximal
        clearEntry checkpoint wellFormed assessment residual raw block suffix reconstruct phase
          remaining installed positive boundary fallback slotWeight slotNonnegative slotBounded
            weights capacity values entryFresh focal intervention certificate extra stopped (by
              funext history
              dsimp only [stopped]
              cases history.state <;> rfl)
  have counted : ((menu).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some anchor) := by rw [initialEq]; exact anchorTrace
  have budget := (phaseApplication_seedBudget runtime leaks).history _ horizon scheduler
    (fun state present => by
      obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ present
      exact PhaseRuntimeState.initial_seedBudget plan draw)
        ((menu).toRawTrace _ horizon scheduler counted)
  have savedClear : anchor.execution.application.entry.excluded = ∅ :=
    Finset.eq_empty_iff_forall_notMem.mpr (fun owner member => by
      have yes := budget.excluded member
      rw [clearEntry] at yes
      exact Finset.notMem_empty owner yes)
  let sourceProfile := cast (congrArg SourceProgram.BehavioralProfile
    (earlier.prepend_append later suffix)) typed
  have reconstructEarlier : earlier.prepend (later.prepend suffix) = checkpoint.residual.tail :=
    (earlier.prepend_append later suffix).symm.trans reconstruct
  have supported := checkpoint.attempt_mem_prefixLaw savedClear wellFormed assessment mixed residual
    raw earlier (later.prepend suffix) reconstructEarlier filled attempt
  have present : filled.view focal ∈
      ((earlier.prefixLaw (later.prepend suffix) sourceProfile checkpoint.source).map
        (SourceProgram.Config.view focal)).support := by
    apply (PMF.mem_support_map_iff _ _ _).mpr
    refine ⟨filled, ?_, rfl⟩
    simpa only [sourceProfile, typed, cast_cast] using supported
  have splitLaw := earlier.prefixLaw_append later suffix typed checkpoint.source
  change wordLaw = (earlier.prefixLaw (later.prepend suffix) sourceProfile checkpoint.source).bind
    (later.prefixLaw suffix (earlier.tailProfile (later.prepend suffix) sourceProfile)) at splitLaw
  apply Eq.trans ?_ originalLaw
  apply bind_congr_on_support
  intro plans _
  have compared := phaseTimingOwnerWordProfile_memory_focal_view_marginal setup mode runtime
    leaks bounds plan horizon scheduler bound fallback wellFormed assessment earlier later suffix
      sourceProfile checkpoint.source anchor.execution.application.attempt.phase
        anchor.execution.application.generation slotWeight slotNonnegative slotBounded plans
          certificate focal intervention stopped anchor anchorTrace (filled.view focal) present
  dsimp only at compared
  rw [← splitLaw] at compared
  exact compared

end Vegas
