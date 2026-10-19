/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalSourceHistoryReadout
import Vegas.Game.PhaseProposalOrdinaryStoppedSourceWord

/-! # The complete original source history law of an actual stopped native binding phase -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "graph" => serviceGraph setup mode
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds

variable {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

/-- The actual reserved native phase realizes the complete original enriched
source History law. The inverse readout is chosen only on supported complete
words and is unique by genuine source commitment determinacy. It retains the
same literal initialized source prefix, including all hidden inputs and old
remembered choices; no source or graph own-history equality is assumed. -/
theorem phaseProposalUnflagged_stopped_source_history
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (capacity : ReservedEpoch.executionHorizon runtime ≤ bounds.candidateCount)
    (anchor : (app).Control) (idle : anchor.actor = none)
    (anchorTrace : ((menu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some anchor))
    (phase : RuntimePhase (graph))
    (installed : anchor.execution.application.phases.head? = some phase)
    (commitment : phase.kind = .commitment)
    (entryExcluded : anchor.execution.application.entry.excluded =
      anchor.execution.application.current.excluded)
    (fresh : ∀ who, ∀ record ∈ anchor.execution.recall who,
      record.beforeView.application.2.attempt ≠ anchor.execution.application.attempt)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (cursor : PhaseProposalOrdinarySourceCursor setup mode runtime leaks plan anchor phase
      block suffix)
    (current : cursor.config = anchor.execution.application.current.native.config)
    (positive : 0 < block.length) :
    let startLaw := (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)
    let horizon := ReservedEpoch.executionHorizon runtime
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let model := (menu).information startLaw horizon scheduler
    let profile := fun who => (menu).restrictPolicy startLaw horizon scheduler who
      (ReactiveApplication.anchoredPolicy anchor.execution
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who)
    let stopped := fun history : ((menu).protocol startLaw horizon scheduler).History =>
      match history.state with
      | none => False
      | some next => next.execution.application.attempt ≠ anchor.execution.application.attempt
    let law := model.runBehavioralUntil
      ((menu).bounded startLaw horizon scheduler).wellFoundedHistories profile stopped
        ⟨some anchor, anchorTrace⟩
    let sourceLaw := setup.proposalRecoveryModel.runBehavioralFrom
      (setup.proposalRecoveryNormalizedTrembledProfile
        0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
      block.length ⟨some cursor.current, cursor.trace⟩
    let sourceWord := fun history : setup.proposalRecoveryProtocol.History =>
      ((setup.recoveryJointRecall
        (setup.proposalRecoveryEraseTrace history.trace)).take block.length).reverse
    ∃ (image : ((menu).protocol startLaw horizon scheduler).History → RecoveryState (graph))
      (sourceImage : ((menu).protocol startLaw horizon scheduler).History →
        setup.proposalRecoveryProtocol.History),
      (∀ final ∈ law.support,
        ∃ (ending before : (app).Control)
          (prior : ((menu).protocol startLaw horizon scheduler).Trace (some before))
          (joint : Player → Option (app).Action)
          (legal : ((menu).protocol startLaw horizon scheduler).Legal (some before) joint)
          (realized : some ending ∈ ((app).transition startLaw horizon scheduler
            (some before) joint).support) (raw : RecoveryState (graph)),
          final.state = some ending ∧ TracePrefix anchorTrace prior ∧
            TracePrefix (prior.extend joint legal realized) final.trace ∧
            PhaseClosingEffect runtime leaks before.execution ending.execution raw ∧
            image final = phase.drain raw ∧ phase.Finished (image final) ∧
            (image final).excluded = anchor.execution.application.current.excluded ∧
            PhaseProposal.sourceArchive ending.execution.network.inputs =
              PhaseProposal.sourceArchive anchor.execution.network.inputs ∧
            before.execution.application.attempt = anchor.execution.application.attempt ∧
            phase ∈ before.execution.application.phases.head? ∧
            ending.execution.application =
              ({ before.execution.application with current := raw } :
                PhaseRuntimeState graph).normalize ∧
            (image final).native.BindingInvariant ∧ (image final).FailureCoverage) ∧
      (∀ final ∈ law.support,
        sourceImage final ∈ sourceLaw.support ∧
          sourceWord (sourceImage final) =
            phaseProposalBindingWord setup.program block suffix cursor.embedding
              cursor.current.excluded (image final).native.config.store cursor.source) ∧
      law.map sourceImage = sourceLaw := by
  classical
  intro startLaw horizon scheduler model profile stopped law sourceLaw sourceWord
  obtain ⟨image, physical, wordLaw⟩ := phaseProposalUnflagged_stopped_source_binding_word setup
    mode runtime leaks bounds plan complete covered maximal values fullValues tape activationGap
      processingGap gaps margin capacity anchor idle anchorTrace phase installed commitment
        entryExcluded fresh block suffix cursor current
  let nativeWord := fun final : ((menu).protocol startLaw horizon scheduler).History =>
    phaseProposalBindingWord setup.program block suffix cursor.embedding cursor.current.excluded
      (image final).native.config.store cursor.source
  have wordLaw' : law.map nativeWord = sourceLaw.map sourceWord := wordLaw
  let selected := fun word : List (Player → Option (CommitRecoveryMove Player L)) =>
    ∃ history ∈ sourceLaw.support, sourceWord history = word
  let decode := fun word => if present : selected word then present.choose else
    (⟨some cursor.current, cursor.trace⟩ : setup.proposalRecoveryProtocol.History)
  have inverse : ∀ history ∈ sourceLaw.support, decode (sourceWord history) = history := by
    intro history supported
    have present : selected (sourceWord history) := ⟨history, supported, rfl⟩
    rw [show decode (sourceWord history) = present.choose by
      dsimp only [decode]; rw [dite_eq_left present]]
    exact phaseProposalBindingPotentialProfile_source_history_injective setup mode runtime leaks
      plan startLaw horizon scheduler anchor
        ((menu).toRawTrace startLaw horizon scheduler anchorTrace) phase values block suffix cursor
          positive present.choose history present.choose_spec.1 supported present.choose_spec.2
  have decodedLaw : (sourceLaw.map sourceWord).map decode = sourceLaw := by
    rw [PMF.map_comp]
    exact (map_congr_on_support sourceLaw inverse).trans (PMF.map_id sourceLaw)
  let sourceImage := fun final => decode (nativeWord final)
  refine ⟨image, sourceImage, physical, ?_, ?_⟩
  · intro final reached
    have member : nativeWord final ∈ (law.map nativeWord).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨final, reached, rfl⟩
    rw [wordLaw'] at member
    obtain ⟨history, supported, word⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    have same : sourceImage final = history := by
      change decode (nativeWord final) = history
      rw [← word]
      exact inverse history supported
    exact ⟨by rw [same]; exact supported, by rw [same]; exact word⟩
  · change law.map (fun final => decode (nativeWord final)) = sourceLaw
    exact (PMF.map_comp _ _ _).symm.trans
      ((congrArg (PMF.map decode) wordLaw').trans decodedLaw)

end Vegas
