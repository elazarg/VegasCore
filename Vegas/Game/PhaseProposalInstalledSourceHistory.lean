/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalInstalledSourceBlock
import Vegas.Game.PhaseProposalOrdinaryBindingCheckpoint
import Vegas.Source.CommitPrefixSplitting
import Vegas.Source.ProposalRecoveryCommitWindow

/-! # The selected original source history at the actual clean native checkpoint -/

noncomputable section

namespace Vegas

open SourceProgram SourceProgram.Setup EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
private theorem reaches_semantic (setup : Setup (Player := Player) (L := L))
    {fuel : Nat} {first last : setup.proposalRecoveryProtocol.History}
    (reached : setup.proposalRecoveryProtocol.ReachesWithin fuel first last) :
    setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨first.state, setup.proposalRecoveryEraseTrace first.trace⟩
      ⟨last.state, setup.proposalRecoveryEraseTrace last.trace⟩ := by
  induction reached with
  | refl fuel history => exact .refl fuel _
  | step joint legal realized rest ih =>
      exact .step (proposalRecoveryJoint joint) (setup.proposalRecovery_erase_legal joint legal)
        realized ih

omit [Fintype Player] in
private theorem lifted_commit_joint (setup : Setup (Player := Player) (L := L))
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool)
    (current : CommitRecoveryState setup.program)
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    {after : setup.proposalRecoveryProtocol.State}
    (supported : after ∈
      (setup.proposalRecoveryProtocol.step (some current) ⟨joint, legal⟩).support) :
    setup.proposalRecoveryLiftJoint labels
      ⟨some current, proposalRecoveryJoint joint, setup.proposalRecovery_erase_legal joint legal,
        after, supported⟩ = joint := by
  funext who
  cases chosen : joint who with
  | none => simp only [Setup.proposalRecoveryLiftJoint, proposalRecoveryJoint, chosen,
      Option.map_none]
  | some move =>
      have optionLegal : LegalOption setup.proposalRecoveryProtocol (some current) who
          (some move) := by
        simpa only [LegalOption, chosen] using legal.2 who
      have allowed : move.semantic ∈ ProtocolView.recoveryAvailable who setup.program
          (ProtocolState.observe who setup.program current.point) := optionLegal.2.1
      have ordinary := setup.proposalRecovery_option_ordinary_of_atCommit current committing who
        (some move) optionLegal
      simp only [Option.map_some] at ordinary
      simp only [Setup.proposalRecoveryLiftJoint, proposalRecoveryJoint, chosen, Option.map_some]
      cases action : move.semantic.action with
      | commit => simpa only [ProposalRecoveryMove.label, action] using ordinary
      | reveal owner name truth =>
          have impossible := ProtocolState.not_atCommit_of_recoveryAvailable_reveal who
            setup.program current.point move.semantic allowed ⟨owner, name, truth, action⟩
          rw [committing] at impossible
          cases impossible

omit [Fintype Player] in
private theorem lifted_commit_window (setup : Setup (Player := Player) (L := L))
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool)
    (first : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some first))
    (initial : setup.proposalRecoveryLiftTrace labels
      (setup.proposalRecoveryEraseTrace prior) = prior)
    (committing : ProtocolState.atCommit setup.program first.point = true)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) (retained : TracePrefix prior trace)
    (within : trace.length + ProtocolState.commitEnd setup.program first.point ≤
      prior.length + ProtocolState.remaining setup.program first.point) :
    setup.proposalRecoveryLiftTrace labels (setup.proposalRecoveryEraseTrace trace) = trace := by
  induction retained with
  | refl => exact initial
  | @extend before after middle kept joint legal supported ih =>
      have inside : middle.length + ProtocolState.commitEnd setup.program first.point <
          prior.length + ProtocolState.remaining setup.program first.point := by
        simp only [Trace.length] at within
        omega
      obtain ⟨current, same, currentCommit, _end, _rank⟩ :=
        setup.commitRecovery_prefix_inside_commit first
          (setup.proposalRecoveryEraseTrace prior) committing
          (setup.proposalRecoveryEraseTrace middle)
          (setup.proposalRecoveryEraseTrace_prefix kept)
          (by simpa only [setup.proposalRecoveryEraseTrace_length] using inside)
      cases same
      have earlier := ih inside.le
      have currentJoint := lifted_commit_joint setup labels current currentCommit joint legal
        supported
      change (setup.proposalRecoveryLiftTrace labels
        (setup.proposalRecoveryEraseTrace middle)).extend _ _ _ = _
      simp only [earlier, currentJoint]

/-- Once the actual completed native word is the chosen checkpoint's word,
commitment determinacy identifies the full semantic history. Ordinary labels
then identify the literal enriched history with that same checkpoint's archive
lift. This is a supported-history consequence, not a new source-law premise. -/
theorem phaseProposalBindingPotentialProfile_source_checkpoint_history
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (anchor : (phaseApplication runtime leaks).Control)
    (anchorTrace : ((phaseApplication runtime leaks).protocol initial horizon scheduler).Trace
      (some anchor))
    (phase : RuntimePhase (serviceGraph setup mode))
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (cursor : PhaseProposalOrdinarySourceCursor setup mode runtime leaks plan anchor phase
      block suffix) (positive : 0 < block.length)
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool)
    (ordinary : setup.proposalRecoveryLiftTrace labels
      (setup.proposalRecoveryEraseTrace cursor.trace) = cursor.trace)
    (closed : setup.proposalRecoveryProtocol.History)
    (supported : closed ∈ (setup.proposalRecoveryModel.runBehavioralFrom
      (setup.proposalRecoveryNormalizedTrembledProfile
        0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
      block.length ⟨some cursor.current, cursor.trace⟩).support)
    (nativeState : PhaseRuntimeState (serviceGraph setup mode))
    (next : RecoverySourceCheckpoint setup mode nativeState)
    {fuel : Nat}
    (path : setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨some cursor.current, setup.proposalRecoveryEraseTrace cursor.trace⟩ ⟨_, next.trace⟩)
    (word : setup.recoveryJointRecall next.trace =
      ((setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace closed.trace)).take
        block.length) ++
          setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace cursor.trace)) :
    (⟨closed.state, setup.proposalRecoveryEraseTrace closed.trace⟩ :
      setup.commitRecoveryProtocol.History) = ⟨_, next.trace⟩ ∧
    closed = ⟨_, setup.proposalRecoveryLiftTrace labels next.trace⟩ ∧
      ∀ who, who ∉ nativeState.entry.excluded → next.source.BindingsHoldValues who := by
  let strategy := setup.proposalRecoveryNormalizedTrembledProfile
    0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values
  have reached := setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin strategy block.length
    ⟨some cursor.current, cursor.trace⟩ closed supported
  obtain ⟨joint, first, _second, related, _prefixMarginal⟩ :=
    phaseProposalBindingPotentialProfile_source_block_coupling setup mode runtime leaks plan initial
      horizon scheduler anchor anchorTrace phase values block suffix cursor
  rw [← first] at supported
  obtain ⟨pair, member, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨source, state, trace, attempt, exactHistory, point, _excluded, _generation, live,
    _agreement, semanticWord, _labels⟩ := related pair member
  have exactClosed : closed = ⟨some state, trace⟩ := same.symm.trans exactHistory
  cases exactClosed
  have takeWord : (setup.recoveryJointRecall
      (setup.proposalRecoveryEraseTrace trace)).take block.length = attempt.joints.reverse := by
    rw [semanticWord, ← attempt.joints_length, ← List.length_reverse, List.take_left]
  have committing : ProtocolState.atCommit setup.program cursor.current.point = true := by
    rw [cursor.point, cursor.origin.atCommit_lift]
    cases block with
    | nil => cases Nat.not_lt_zero _ positive
    | commit => rfl
  have window : block.length + ProtocolState.commitEnd setup.program cursor.current.point ≤
      ProtocolState.remaining setup.program cursor.current.point := by
    rw [cursor.point, cursor.origin.commitEnd_lift, cursor.origin.remaining_lift]
    exact block.length_le_commit_window suffix cursor.source
  have length := reached.trace_length_le_add
  change trace.length ≤ cursor.trace.length + block.length at length
  have within : trace.length + ProtocolState.commitEnd setup.program cursor.current.point ≤
      cursor.trace.length + ProtocolState.remaining setup.program cursor.current.point := by omega
  have semantic := setup.commitRecovery_history_eq_of_commit_window cursor.current
    (setup.proposalRecoveryEraseTrace cursor.trace) committing
      (setup.proposalRecoveryEraseTrace trace) next.trace
      (reaches_semantic setup reached) path
      (semanticWord.trans (by rw [word, takeWord]))
      (by simpa only [setup.proposalRecoveryEraseTrace_length] using within)
  have enriched := lifted_commit_window setup labels cursor.current cursor.trace ordinary committing
    trace reached.tracePrefix within
  refine ⟨semantic, ?_, ?_⟩
  · have lifted := congrArg (fun history : setup.commitRecoveryProtocol.History =>
      (⟨history.state, setup.proposalRecoveryLiftTrace labels history.trace⟩ :
        setup.proposalRecoveryProtocol.History)) semantic
    exact (show (⟨some state, trace⟩ : setup.proposalRecoveryProtocol.History) =
      ⟨_, setup.proposalRecoveryLiftTrace labels
        (setup.proposalRecoveryEraseTrace trace)⟩ from congrArg (History.mk _) enriched.symm).trans
          lifted
  · intro who active
    have stateEq := Option.some.inj (congrArg History.state semantic)
    have activeState : who ∉ state.excluded := by rw [stateEq]; exact active
    have stateLive : ProtocolState.BindingsHoldValues who setup.program state.point := by
      rw [point]
      apply (cursor.origin.bindingsHoldValues_lift who _).mpr
      apply (block.bindingsHoldValues_liftPoint suffix who _).mpr
      exact (ProtocolState.bindingsHoldValues_entry who suffix source).mpr
        (live who activeState)
    rw [stateEq] at stateLive
    intro name payload cell
    exact (ProtocolState.bindingsHoldValues_entry who next.residual.tail next.source).mp
      ((next.origin.bindingsHoldValues_lift who _).mp stateLive) cell

omit [Fintype Player] in
private theorem maximal_commit_phase
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (boundary : IsCommitBoundary suffix) :
    commitPhase (block.prepend suffix) = ⟨Δ, P, suffix, block, rfl, boundary⟩ := by
  induction block with
  | nil => cases suffix <;> first | rfl | cases boundary
  | commit name owner fresh guard rest ih =>
      let extend : CommitPhase (rest.prepend suffix) →
          CommitPhase ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend
            suffix) := fun later =>
        ⟨later.context, later.pending, later.suffix,
          .commit name owner fresh guard later.block,
          congrArg (SourceProgram.commit name owner fresh guard) later.reconstruct,
          later.boundary⟩
      exact congrArg extend (ih suffix boundary)

omit [Fintype Player] in
theorem RecoverySourceCheckpoint.transfer_history
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state other : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (entry : other.entry = state.entry) (generation : other.generation = state.generation)
    (offset : other.attempt.phase = state.attempt.phase) :
    (⟨_, (checkpoint.transfer entry generation offset).trace⟩ :
      setup.commitRecoveryProtocol.History) = ⟨_, checkpoint.trace⟩ := by
  rcases state with ⟨phases, currentGeneration, saved, current, retired⟩
  rcases other with ⟨otherPhases, otherGeneration, otherSaved, otherCurrent, otherRetired⟩
  dsimp only at entry generation
  cases entry
  cases generation
  rfl

omit [Fintype Player] in
private theorem binding_word_of_reconstruct
    (setup : Setup (Player := Player) (L := L))
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (program : SourceProgram Player L Γ O)
    (programEmbedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      program)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (reconstruct : block.prepend suffix = program)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix))
    (embeddingEq : embedding = cast (congrArg (fun program => OutputEmbedding
      (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
        programEmbedding)
    (source : SourceProgram.Config Player L Γ) (excluded : Finset Player)
    (store : Store (graphLayout setup.program))
    (result : List (Player → Option (CommitRecoveryMove Player L)))
    (boundary : IsCommitBoundary suffix)
    (word : match commitPhase program with
      | ⟨_, _, suffix, block, reconstruct, _⟩ =>
        let embedding := cast (congrArg (fun program => OutputEmbedding
          (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
            programEmbedding
        phaseProposalBindingWord setup.program block suffix embedding excluded store source =
          result) :
    phaseProposalBindingWord setup.program block suffix embedding excluded store source =
      result := by
  revert embeddingEq word
  subst program
  intro embeddingEq word
  cases embeddingEq
  rw [maximal_commit_phase block suffix boundary] at word
  exact word

section Installed

variable (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "graph" => serviceGraph setup mode
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds

/-- The actual fresh installation, original enriched source law and actual
clean native close use one selected checkpoint throughout. The returned next
checkpoint is at the drained boundary; the physical ending follows the existing
automatic settle, and the selected full source history is its literal archive
lift. Original hidden inputs, remembered choices and all source controls remain
part of that history. -/
theorem RecoverySourceWitness.ordinary_installed_binding_history
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
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
    (phase : RuntimePhase graph)
    (installed : anchor.execution.application.phases.head? = some phase)
    (kind : phase.kind = .commitment)
    (entryExcluded : anchor.execution.application.entry.excluded =
      anchor.execution.application.current.excluded)
    (fresh : ∀ who, ∀ record ∈ anchor.execution.recall who,
      record.beforeView.application.2.attempt ≠ anchor.execution.application.attempt)
    (witness : RecoverySourceWitness setup mode plan anchor.execution.application)
    (archived : witness.checkpoint.ArchivedProposals anchor.execution.network.inputs)
    (ordinary : ∀ who, who ∉ anchor.execution.application.current.excluded →
      witness.checkpoint.source.BindingsHoldValues who) :
    let initial := (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)
    let horizon := ReservedEpoch.executionHorizon runtime
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let model := (menu).information initial horizon scheduler
    let profile := fun who => (menu).restrictPolicy initial horizon scheduler who
      (ReactiveApplication.anchoredPolicy anchor.execution
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who)
    let stopped := fun history : ((menu).protocol initial horizon scheduler).History =>
      match history.state with
      | none => False
      | some next => next.execution.application.attempt ≠ anchor.execution.application.attempt
    let law := model.runBehavioralUntil
      ((menu).bounded initial horizon scheduler).wellFoundedHistories profile stopped
        ⟨some anchor, anchorTrace⟩
    ∃ (Δ : SourceCtx Player L) (P : Finset VarId)
      (block : SourceProgram.CommitPrefix witness.checkpoint.residual.context
        witness.checkpoint.residual.names Δ P) (suffix : SourceProgram Player L Δ P)
      (cursor : PhaseProposalOrdinarySourceCursor setup mode runtime leaks plan anchor phase
        block suffix),
      block.length = phase.high - phase.low ∧
      (⟨some cursor.current, cursor.trace⟩ : setup.proposalRecoveryProtocol.History) =
        ⟨_, setup.proposalRecoveryLiftTrace
          (nativeArchiveLabels setup (PhaseProposal.sourceArchive anchor.execution.network.inputs))
          witness.checkpoint.trace⟩ ∧
      ∃ (image : ((menu).protocol initial horizon scheduler).History → RecoveryState graph)
        (sourceImage : ((menu).protocol initial horizon scheduler).History →
          setup.proposalRecoveryProtocol.History),
        law.map sourceImage = setup.proposalRecoveryModel.runBehavioralFrom
          (setup.proposalRecoveryNormalizedTrembledProfile
            0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
          block.length ⟨some cursor.current, cursor.trace⟩ ∧
        ∀ final ∈ law.support,
          ∃ (ending before : (app).Control)
            (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
            (joint : Player → Option (app).Action)
            (legal : ((menu).protocol initial horizon scheduler).Legal (some before) joint)
            (realized : some ending ∈ ((app).transition initial horizon scheduler
              (some before) joint).support) (raw : RecoveryState graph)
            (remaining : List (RuntimePhase graph))
            (next : RecoverySourceCheckpoint setup mode
              (⟨remaining, before.execution.application.generation,
                phase.drain raw, phase.drain raw,
                before.execution.application.retired⟩ : PhaseRuntimeState graph)),
            final.state = some ending ∧ TracePrefix anchorTrace prior ∧
            TracePrefix (prior.extend joint legal realized) final.trace ∧
            PhaseClosingEffect runtime leaks before.execution ending.execution raw ∧
            before.execution.application.attempt = anchor.execution.application.attempt ∧
            before.execution.application.phases = phase :: remaining ∧
            phase.Finished (phase.drain raw) ∧
            image final = phase.drain raw ∧
            ending.execution.application = PhaseRuntimeState.settle remaining
              before.execution.application.generation (phase.drain raw) (phase.drain raw)
                before.execution.application.retired ∧
            (image final).excluded = anchor.execution.application.current.excluded ∧
            PhaseProposal.sourceArchive ending.execution.network.inputs =
              PhaseProposal.sourceArchive anchor.execution.network.inputs ∧
            (∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
              ⟨_, witness.checkpoint.trace⟩ ⟨_, next.trace⟩) ∧
            setup.recoveryJointRecall
                (setup.proposalRecoveryEraseTrace (sourceImage final).trace) =
              (witness.checkpoint.commitInstructionWord (phase.drain raw).native).reverse ++
                setup.recoveryJointRecall witness.checkpoint.trace ∧
            (⟨(sourceImage final).state,
              setup.proposalRecoveryEraseTrace (sourceImage final).trace⟩ :
                setup.commitRecoveryProtocol.History) = ⟨_, next.trace⟩ ∧
            sourceImage final = ⟨_, setup.proposalRecoveryLiftTrace
              (nativeArchiveLabels setup
                (PhaseProposal.sourceArchive ending.execution.network.inputs)) next.trace⟩ ∧
            (∀ who, who ∉ (phase.drain raw).excluded → next.source.BindingsHoldValues who) := by
  intro initial horizon scheduler model profile stopped law
  obtain ⟨Δ, P, block, suffix, cursor, size, sourceEq, current, entry, refsEq, reconstruct,
    embeddingEq, liftEq⟩ := witness.ordinary_installed_binding_cursor setup mode runtime leaks
      bounds plan maximal horizon scheduler anchor anchorTrace phase installed kind entryExcluded
        fresh archived ordinary
  have positive : 0 < block.length := by
    have nonempty := phase.nonempty
    omega
  obtain ⟨image, sourceImage, physical, selected, sourceLaw⟩ :=
    phaseProposalUnflagged_stopped_source_history setup mode runtime leaks bounds plan complete
      covered maximal values fullValues tape activationGap processingGap gaps margin capacity anchor
        idle anchorTrace phase installed kind entryExcluded fresh block suffix cursor current
          positive
  refine ⟨Δ, P, block, suffix, cursor, size, entry, image, sourceImage, sourceLaw, ?_⟩
  intro final supported
  obtain ⟨ending, before, prior, joint, legal, realized, raw, stateEq, fromAnchor, toFinal, effect,
    imageEq, finished, imageE, archiveEq, sameAttempt, beforeInstalled, normalized, _binding,
      _coverage⟩ := physical final supported
  obtain ⟨remaining, phases⟩ := List.head?_eq_some_iff.mp (Option.mem_def.mp beforeInstalled)
  have initialized : ∀ state ∈ initial.support, state.Ordered := by
    intro state member
    obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ member
    exact PhaseRuntimeState.initial_ordered plan draw
  have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    initialized ((menu).toRawTrace initial horizon scheduler anchorTrace)
  have progress := phase_attempt_progress_of_prefix runtime leaks menu initial initialized horizon
    scheduler anchor before anchorTrace prior fromAnchor ordered
  have sameEntry := (progress.2.2 sameAttempt.symm).symm
  have sameGeneration : before.execution.application.generation =
      anchor.execution.application.generation := congrArg CommitAttemptId.generation sameAttempt
  have sameOffset := congrArg CommitAttemptId.phase sameAttempt
  let checkpoint : RecoverySourceCheckpoint setup mode before.execution.application :=
    witness.checkpoint.transfer sameEntry sameGeneration sameOffset
  have low : phase.low = before.execution.application.attempt.phase := by
    simp only [PhaseRuntimeState.attempt, phases, List.head?_cons, Option.map_some,
      Option.getD_some]
  have committing := checkpoint.compiled.atCommit_of_bindingPhase setup.program mode
    checkpoint.residual.tail checkpoint.refs checkpoint.source.revelations checkpoint.registry
      checkpoint.embedding checkpoint.before before.execution.application.attempt.phase phase kind
        low checkpoint.source
  have changed : ending.execution.application.attempt ≠ before.execution.application.attempt := by
    have closed : ending.execution.application.attempt ≠ anchor.execution.application.attempt := by
      rcases anchor with ⟨steps, actor, execution⟩
      change actor = none at idle
      subst actor
      obtain ⟨last, _before, _prior, _joint, _legal, _realized, _raw, lastEq, _lastIdle,
        changed, _rest⟩ := phaseProposalUnflagged_stopped_binding_image setup mode runtime leaks
          bounds plan complete covered maximal (serviceGraph_revealRelaxedOrdered setup mode)
            values fullValues tape activationGap processingGap gaps margin capacity steps execution
              anchorTrace phase (Option.mem_def.mpr installed) kind final (by
                convert supported using 1
                congr 3
                funext history
                dsimp only [stopped]
                cases history.state <;> rfl)
      have same := Option.some.inj (lastEq.symm.trans stateEq)
      cases same
      exact changed
    exact fun same => closed (same.trans sameAttempt)
  have imageEntry : (phase.drain raw).excluded = before.execution.application.entry.excluded := by
    rw [← imageEq, imageE, sameEntry, entryExcluded]
  obtain ⟨next, _point, ⟨fuel, path, instructions⟩, settled, decodedWord⟩ :=
    checkpoint.ordinary_closing_binding_checkpoint setup mode runtime leaks bounds plan maximal
      horizon scheduler before ending prior committing phase remaining phases kind raw effect
        changed
        normalized (imageEq ▸ finished) imageEntry
  have checkpointStart : (⟨_, checkpoint.trace⟩ : setup.commitRecoveryProtocol.History) =
      ⟨some cursor.current, setup.proposalRecoveryEraseTrace cursor.trace⟩ := by
    have erased := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
      (⟨history.state, setup.proposalRecoveryEraseTrace history.trace⟩ :
        setup.commitRecoveryProtocol.History)) entry
    exact (witness.checkpoint.transfer_history sameEntry sameGeneration sameOffset).trans
      (by simpa only [setup.proposalRecoveryEraseTrace_lift] using erased.symm)
  have savedSame : cursor.current.saved = cursor.current.point := by
    have state := Option.some.inj (congrArg History.state entry)
    rw [state]
    rfl
  have suffixEnd := cursor.savedEnd positive
  rw [savedSame, cursor.point, cursor.origin.commitEnd_lift] at suffixEnd
  have suffixEndpoint := (block.commitEnd_suffix suffix cursor.source
    (block.automatic cursor.source)).symm.trans suffixEnd
  have boundary : IsCommitBoundary suffix := by
    cases suffix with
    | ret => trivial
    | sample => trivial
    | reveal => trivial
    | commit name owner fresh guard tail =>
        have below := ProtocolState.commitEnd_lt_remaining
          (.commit name owner fresh guard tail)
          (ProtocolState.entry (.commit name owner fresh guard tail)
            (block.automatic cursor.source)) rfl
        rw [suffixEndpoint, ProtocolState.remaining_entry] at below
        exact (Nat.lt_irrefl _ below).elim
  have nativeWord : phaseProposalBindingWord setup.program block suffix cursor.embedding
        cursor.current.excluded (image final).native.config.store cursor.source =
      checkpoint.commitInstructionWord (phase.drain raw).native := by
    rw [imageEq]
    rw [sourceEq, cursor.excluded, ← entryExcluded, ← sameEntry]
    exact binding_word_of_reconstruct setup checkpoint.residual.tail checkpoint.embedding block
      suffix reconstruct cursor.embedding embeddingEq checkpoint.source
        before.execution.application.entry.excluded (phase.drain raw).native.config.store
          (checkpoint.commitInstructionWord (phase.drain raw).native) boundary decodedWord
  have fullWord : setup.recoveryJointRecall next.trace =
      ((setup.recoveryJointRecall
        (setup.proposalRecoveryEraseTrace (sourceImage final).trace)).take block.length) ++
          setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace cursor.trace) := by
    have wordEq := (selected final supported).2
    have prefixWord := congrArg
      (fun history : setup.commitRecoveryProtocol.History =>
        setup.recoveryJointRecall history.trace)
        checkpointStart
    rw [instructions, prefixWord, ← nativeWord, ← wordEq, List.reverse_reverse]
  have ordinaryLift : setup.proposalRecoveryLiftTrace
      (nativeArchiveLabels setup (PhaseProposal.sourceArchive anchor.execution.network.inputs))
        (setup.proposalRecoveryEraseTrace cursor.trace) = cursor.trace := by
    have lifted := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
      (⟨history.state, setup.proposalRecoveryLiftTrace
        (nativeArchiveLabels setup (PhaseProposal.sourceArchive anchor.execution.network.inputs))
          (setup.proposalRecoveryEraseTrace history.trace)⟩ :
            setup.proposalRecoveryProtocol.History)) entry
    rw [setup.proposalRecoveryEraseTrace_lift] at lifted
    have identical := lifted.trans entry.symm
    exact eq_of_heq (History.mk.inj identical).2
  rw [checkpointStart] at path
  obtain ⟨semantic, enriched, nextProper⟩ :=
    phaseProposalBindingPotentialProfile_source_checkpoint_history setup mode runtime leaks plan
      initial horizon scheduler anchor ((menu).toRawTrace initial horizon scheduler anchorTrace)
        phase values block suffix cursor positive
        (nativeArchiveLabels setup (PhaseProposal.sourceArchive anchor.execution.network.inputs))
        ordinaryLift (sourceImage final) (selected final supported).1 _ next path fullWord
  have sourceStart := witness.checkpoint.transfer_history sameEntry sameGeneration sameOffset
  have fromWitness : setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨_, witness.checkpoint.trace⟩ ⟨_, next.trace⟩ := by
    have restored := path
    rw [← checkpointStart] at restored
    rw [sourceStart] at restored
    exact restored
  have sameInstructionWord : checkpoint.commitInstructionWord (phase.drain raw).native =
      witness.checkpoint.commitInstructionWord (phase.drain raw).native := by
    simp only [checkpoint, RecoverySourceCheckpoint.transfer,
      RecoverySourceCheckpoint.commitInstructionWord]
    rw [congrArg RecoveryState.excluded sameEntry]
  have sourceWord : setup.recoveryJointRecall
        (setup.proposalRecoveryEraseTrace (sourceImage final).trace) =
      (witness.checkpoint.commitInstructionWord (phase.drain raw).native).reverse ++
        setup.recoveryJointRecall witness.checkpoint.trace := by
    have actual := congrArg (fun history : setup.commitRecoveryProtocol.History =>
      setup.recoveryJointRecall history.trace) semantic
    have retained := congrArg (fun history : setup.commitRecoveryProtocol.History =>
      setup.recoveryJointRecall history.trace) sourceStart
    exact actual.trans (instructions.trans (by rw [sameInstructionWord, retained]))
  rw [← archiveEq] at enriched
  exact ⟨ending, before, prior, joint, legal, realized, raw, remaining, next, stateEq, fromAnchor,
    toFinal, effect, sameAttempt, phases, imageEq ▸ finished,
    imageEq, settled, imageE, archiveEq, ⟨fuel, fromWitness⟩, sourceWord, semantic, enriched,
    nextProper⟩

end Installed
end Vegas
