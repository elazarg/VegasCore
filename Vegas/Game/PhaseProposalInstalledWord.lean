/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalBindingEntry
import Vegas.Game.PhaseProposalBindingPhaseLaw

/-! # The actual fresh phase word at its installed source checkpoint -/

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

/-- Select the actual first installed prefix, including its source checkpoint,
then realize the whole original drained image word. Fresh recall, idle control
and saved exclusion are derived from actual initialization and installation.
The law starts at that prefix; an old pending anchor is never resampled. -/
theorem phaseProposalUnflagged_installed_binding_word
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
    (control : (app).Control)
    (trace : ((menu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some control))
    (phase : RuntimePhase (graph))
    (installed : control.execution.application.phases.head? = some phase)
    (commitment : phase.kind = .commitment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix)) (entry : SourceProgram.Config Player L Γ)
    (locations : ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
      embedding.event index ∈ phase.events) :
    let startLaw := (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)
    let horizon := ReservedEpoch.executionHorizon runtime
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    ∃ (anchor : (app).Control)
      (anchorTrace : ((menu).protocol startLaw horizon scheduler).Trace (some anchor))
      (witness : RecoverySourceWitness setup mode plan anchor.execution.application),
      TracePrefix anchorTrace trace ∧
      anchor.execution.application.attempt = control.execution.application.attempt ∧
      anchor.actor = none ∧
      anchor.execution.application.entry.excluded = anchor.execution.application.current.excluded ∧
      (∀ who, ∀ record ∈ anchor.execution.recall who,
        record.beforeView.application.2.attempt ≠ anchor.execution.application.attempt) ∧
      witness.checkpoint.ArchivedProposals anchor.execution.network.inputs ∧
      let model := (menu).information startLaw horizon scheduler
      let profile := fun who => (menu).restrictPolicy startLaw horizon scheduler who
        (ReactiveApplication.anchoredPolicy anchor.execution
          (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who)
      let stopped := fun history : ((menu).protocol startLaw horizon scheduler).History =>
        match history.state with
        | none => False
        | some current =>
            current.execution.application.attempt ≠ anchor.execution.application.attempt
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
        law.map (fun final => phaseProposalBindingWord setup.program block suffix embedding
          anchor.execution.application.current.excluded (image final).native.config.store entry) =
            ((graph).canonicalContinuation
              (phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor.execution
                phase values) anchor.execution.application.current.native.config).map
                  (fun key => phaseProposalBindingWord setup.program block suffix embedding
                    anchor.execution.application.current.excluded key.2.1 entry) := by
  intro startLaw horizon scheduler
  obtain ⟨anchor, anchorTrace, witness, retained, same, anchorInstalled, idle, excluded,
      archived, fresh⟩ := phaseProposal_binding_entry_checkpoint setup mode runtime leaks bounds
    plan maximal horizon scheduler control trace phase installed
  refine ⟨anchor, anchorTrace, witness, retained, same, idle, excluded, fresh, archived, ?_⟩
  exact phaseProposalUnflagged_stopped_binding_word setup mode runtime leaks bounds plan
    complete covered maximal values fullValues tape activationGap processingGap gaps margin
      capacity anchor idle anchorTrace phase anchorInstalled commitment excluded fresh block suffix
        embedding entry locations

end Vegas
