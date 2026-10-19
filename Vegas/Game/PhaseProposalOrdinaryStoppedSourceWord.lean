/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalSourceWordReadout
import Vegas.Game.PhaseProposalBindingPhaseLaw

/-! # The actual stopped native binding word and its original source run -/

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

/-- The literal original binding word produced by the actual reserved native
phase has the law of the finite ordinary source run from its supplied SAME
source cursor. The signed source proposals and old initialized history remain
fixed; the graph continuation is eliminated by its checked source coupling. -/
theorem phaseProposalUnflagged_stopped_source_binding_word
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
    (current : cursor.config = anchor.execution.application.current.native.config) :
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
    ∃ image : ((menu).protocol startLaw horizon scheduler).History → RecoveryState (graph),
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
      law.map (fun final => phaseProposalBindingWord setup.program block suffix cursor.embedding
        cursor.current.excluded (image final).native.config.store cursor.source) =
        (setup.proposalRecoveryModel.runBehavioralFrom
          (setup.proposalRecoveryNormalizedTrembledProfile
            0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
          block.length ⟨some cursor.current, cursor.trace⟩).map
            (fun history => ((setup.recoveryJointRecall
              (setup.proposalRecoveryEraseTrace history.trace)).take block.length).reverse) := by
  intro startLaw horizon scheduler model profile stopped law
  obtain ⟨image, physical, wordLaw⟩ := phaseProposalUnflagged_stopped_binding_word setup mode
    runtime leaks bounds plan complete covered maximal values fullValues tape activationGap
      processingGap gaps margin capacity anchor idle anchorTrace phase installed commitment
        entryExcluded fresh block suffix cursor.embedding cursor.source cursor.interval
  refine ⟨image, physical, ?_⟩
  have sourceWord := phaseProposalBindingPotentialProfile_source_word_law setup mode runtime leaks
    plan startLaw horizon scheduler anchor
      ((menu).toRawTrace startLaw horizon scheduler anchorTrace) phase values block suffix cursor
  rw [cursor.excluded, current] at sourceWord
  rw [cursor.excluded]
  exact wordLaw.trans sourceWord

end Vegas
