/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryTimingSourceReference
import Vegas.Game.PhaseTimingMemorySourcePosterior
import Vegas.Game.RecoveryCommitCurrentViewSupport
import Vegas.Pending.PhaseClearHistory
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

local instance timingReferenceInputPoolFintype : Fintype Pool := Fintype.ofFinite _

open Classical in
/-- Literal zero-noise native inputs condition the SAME source-current-view
reference while retaining its entire observation-tilted original owner-plan tag.
Those reference plan tags are not identified with factual updated plans. -/
theorem RecoverySourceCheckpoint.timing_word_literal_reference_input
    {anchor : (app).Control}
    (anchorTrace : ((menu).protocol initial horizon scheduler).Trace (some anchor))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (clearEntry : anchor.execution.application.current.excluded = ∅)
    (checkpoint : RecoverySourceCheckpoint setup mode anchor.execution.application)
    (wellFormed : setup.WellFormed)
    (finite : setup.program.FiniteBindingTypes)
    (target : setup.commitRecoveryModel.BehavioralAssessment)
    (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
      (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
        setup.commitRecoveryContinuingChoice)
    (n : Nat)
    (residual : SourceProgram.BehavioralProfile checkpoint.residual.tail)
    (raw : ∀ owner point,
      (residual owner).protocolAction checkpoint.residual.tail
          (ProtocolState.observe owner checkpoint.residual.tail point) =
        (setup.commitRecoveryNonmissingProfile (approximation.sequence n).strategy owner
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
    (committing : phase.kind = .commitment)
    (lower : phase.low = anchor.execution.application.attempt.phase)
    (upper : phase.high =
      anchor.execution.application.attempt.phase + (earlier.append later).length)
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
    (wanted observed : (N).InfoState focal) :
    let block := earlier.append later
    let typed := cast (congrArg SourceProgram.BehavioralProfile reconstruct.symm) residual
    let wordLaw := block.prefixLaw suffix typed checkpoint.source
    let members := fun owner (memory : ((p : Pool) → Parts p) × DecisionView owner Ξ) =>
      ReactiveApplication.anchoredPolicy anchor.execution (fun _ =>
        phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed (approximation.sequence n) block
            anchor.execution.application.attempt.phase 0 slotWeight slotNonnegative slotBounded
              memory.1 owner memory.2) owner
    let profile := (N).agentBehavior (N).playedInformation fallback (fun agent =>
      (weights (phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler bound
        agent)).bind (phaseTimingComponent setup mode runtime leaks bounds initial horizon
          scheduler bound wellFormed (approximation.sequence n) 0 le_rfl (by norm_num) slotWeight
            slotNonnegative slotBounded agent))
    let focalPolicy := (app).decodePolicy ((menu).embedPolicy initial horizon scheduler focal
      intervention)
    let family := fun owner memory =>
      if owner = focal then focalPolicy else members owner memory
    let exits : (E).History → Prop := fun history => match history.state with
      | none => True
      | some current => current.execution.application.current.excluded ≠ ∅ ∨
          current.execution.application.phases ≠ phase :: remaining
    let stopped := fun history : (E).History => exits history ∨
      ((app).actor history.state = some focal ∧ (N).infoOf focal history.trace = wanted)
    let readout := fun history : (E).History =>
      @ite _ (exits history) (Classical.propDecidable (exits history)) none
        ((N).infoOf focal history.trace)
    let run := fun memories => (N).runBehavioralUntil certificate (fun who =>
      (menu).restrictPolicy initial horizon scheduler who (family who (memories who))) stopped
        ⟨some anchor, anchorTrace⟩
    let read := fun (plans : Player → ((p : Pool) → Parts p))
      (complete : SourceProgram.Config Player L Ξ) =>
        fun owner => (plans owner, complete.view owner)
    let reference := fiberPosterior wordLaw
      (fun complete => later.entryView focal (complete.view focal)) (filled.view focal)
    let tagLaw := independentProduct (fun _ : Player => independentProduct weights)
    let physical := fun plans complete => (run (read plans complete)).map readout
    let targetLaw := (N).runBehavioralUntil certificate
      (GameTheory.Profile.update (sig := (N).behavioralSignature) profile focal intervention)
        stopped
        ⟨some anchor, anchorTrace⟩
    let joint := tagLaw.bind fun plans => reference.bind fun complete =>
      (physical plans complete).map fun output => (output, (plans, complete))
    let outer := tagLaw.bind fun plans =>
      (reference.bind (physical plans)).map fun output => (output, plans)
    outer.map Prod.fst = targetLaw.map readout ∧
      (observed ∈ (targetLaw.map readout).support →
        (fiberPosterior joint Prod.fst observed).map Prod.snd =
          ((fiberPosterior outer Prod.fst observed).map Prod.snd).bind
            (fun plans => reference.map (Prod.mk plans)) ∧
        ∀ plans ∈ ((fiberPosterior outer Prod.fst observed).map Prod.snd).support,
          ∀ complete ∈ reference.support,
            later.entryView focal (complete.view focal) = filled.view focal ∧
              complete ∈ wordLaw.support) := by
  intro block typed wordLaw members profile focalPolicy family exits stopped readout run read
    reference tagLaw physical targetLaw joint outer
  let inputs := setup.initialLaw.map (fun draw => encodeInputs draw)
  have initialEq : inputs.map (PhaseRuntimeState.initial plan) = initial := by
    simp only [inputs, PMF.map_comp, Function.comp_def]
  have counted : ((menu).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some anchor) := by rw [initialEq]; exact anchorTrace
  have rawTrace := (menu).toRawTrace _ horizon scheduler counted
  have generation := (phase_clear_history runtime leaks plan inputs horizon scheduler anchor
    rawTrace clearEntry).1
  have budget := (phaseApplication_seedBudget runtime leaks).history _ horizon scheduler
    (fun state present => by
      obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ present
      exact PhaseRuntimeState.initial_seedBudget plan draw) rawTrace
  have savedClear : anchor.execution.application.entry.excluded = ∅ :=
    Finset.eq_empty_iff_forall_notMem.mpr (fun owner member => by
      have yes := budget.excluded member
      rw [clearEntry] at yes
      exact Finset.notMem_empty owner yes)
  have sourcePresent := checkpoint.current_view_mem_prefixLaw savedClear wellFormed
    (approximation.sequence n) (approximation.mixed n) residual raw earlier later suffix reconstruct
      filled attempt focal
  change filled.view focal ∈ (wordLaw.map
    (fun complete => later.entryView focal (complete.view focal))).support at sourcePresent
  let wantedAt := fun history : (E).History =>
    (app).actor history.state = some focal ∧ (N).infoOf focal history.trace = wanted
  have literal := checkpoint.timing_word_anchored_reference_law setup mode runtime leaks bounds
    plan horizon scheduler bound anchorTrace maximal clearEntry wellFormed
      (approximation.sequence n) (approximation.mixed n) residual raw
        earlier later suffix reconstruct
        phase remaining installed positive boundary fallback slotWeight slotNonnegative slotBounded
          weights capacity values entryFresh focal intervention filled attempt certificate wantedAt
  dsimp only at literal
  rw [generation] at literal
  have normalizedLiteral :
      (tagLaw.bind fun plans => reference.bind fun complete => run (read plans complete)) =
        targetLaw := by
    dsimp only [tagLaw, reference, wordLaw, typed, block, run, read, family, members,
      focalPolicy, targetLaw, profile, stopped, exits, wantedAt]
    dsimp only [wantedAt] at literal
    simp only [or_comm] at literal ⊢
    convert! literal using 1
  have mapped := congrArg (PMF.map readout) normalizedLiteral
  simp only [PMF.map_bind] at mapped
  have mapIdentity {A : Type} (law : PMF A) : law.map (fun output => output) = law :=
    PMF.map_id law
  have inputLaw : outer.map Prod.fst = targetLaw.map readout := by
    simp only [outer, PMF.map_bind, PMF.map_comp, Function.comp_def]
    simp only [mapIdentity]
    exact mapped
  constructor
  · exact inputLaw
  intro present
  have native := phaseTimingOwnerWordProfile_memory_reference_posterior setup mode runtime leaks
    bounds plan maximal horizon scheduler bound finite wellFormed target approximation n fallback
      tagLaw (fun plans => plans) earlier later suffix (fun _ => typed) (fun _ => checkpoint.source)
        focal (fun _ => filled.view focal) anchor.execution.application.attempt.phase slotWeight
          slotNonnegative slotBounded (fun _ => anchor) (fun _ => ⟨some anchor, anchorTrace⟩)
            (fun _ _ => rfl) (fun _ _ => clearEntry) phase remaining
              (fun _ _ => installed) committing
              lower upper values capacity certificate wanted (fun _ => intervention) observed
                (fun _ _ => sourcePresent)
  have nativePresent : observed ∈ (tagLaw.bind fun plans =>
      reference.bind (physical plans)).support := by
    rw [← inputLaw] at present
    simpa only [outer, PMF.map_bind, PMF.map_comp, Function.comp_def, mapIdentity] using present
  exact native nativePresent

end Vegas
