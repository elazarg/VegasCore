/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochFocalWord
import Vegas.Game.PhaseProposalOrdinaryBindingCheckpoint
import Vegas.Game.PhaseProposalAttemptArchive
import Vegas.Pending.PhaseEntryExclusion

/-! # Actual binding resets cancel current attempted unusable values

The original attempt's failure scan determines its source omission word.
Different accepted typed choices and canceled private action words stay literal
until the actual reset dispatcher restores the common saved checkpoint.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [IExpr.ResultTypes L] in
private theorem omission_word_eq_of_exclusion_scan
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    {block : SourceProgram.CommitPrefix Γ O Δ P} {entry : Config Player L Γ}
    {excluded : Finset Player} {finished : Config Player L Δ} {after : Finset Player}
    (first : block.Attempt entry excluded finished after) :
    ∀ {otherEntry : Config Player L Γ} {otherFinished : Config Player L Δ}
      {otherAfter : Finset Player}
      (second : block.Attempt otherEntry excluded otherFinished otherAfter),
      first.exclusionsAfter = second.exclusionsAfter →
      first.joints.map (fun joint owner => CommitRecoveryMove.missed (joint owner)) =
        second.joints.map (fun joint owner => CommitRecoveryMove.missed (joint owner)) := by
  induction first with
  | nil => intro _ _ _ second _; cases second; rfl
  | @active Γ Δ O P name owner payload fresh guard rest entry excluded finished after
      active choice missed valid later ih =>
      intro otherEntry otherFinished otherAfter second scan
      cases second with
      | excluded inactive _ => exact (active inactive).elim
      | active active' otherChoice otherMissed _ otherLater =>
          have words := List.cons.inj scan
          have bits : missed = otherMissed := by
            cases missed <;> cases otherMissed
            · rfl
            · have member : owner ∈ excluded := by
                rw [show excluded = insert owner excluded from words.1]
                exact Finset.mem_insert_self _ _
              exact (active member).elim
            · have member : owner ∈ excluded := by
                rw [← show insert owner excluded = excluded from words.1]
                exact Finset.mem_insert_self _ _
              exact (active member).elim
            · rfl
          subst otherMissed
          have tail := ih otherLater words.2
          simp only [CommitPrefix.Attempt.joints, List.map_cons]
          refine congrArg₂ List.cons ?_ tail
          funext player
          by_cases same : player = owner <;>
            simp only [same, ↓reduceIte, CommitRecoveryMove.missed,
              Option.elim_some, Option.elim_none]
  | excluded inactive later ih =>
      intro otherEntry otherFinished otherAfter second scan
      cases second with
      | active active _ _ _ _ => exact (active inactive).elim
      | excluded _ otherLater =>
          exact congrArg (List.cons (fun _ => false)) (ih otherLater (List.cons.inj scan).2)

private theorem RecoverySourceCheckpoint.commit_omission_word_eq
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (first second : EventGraphRuntime.State (serviceGraph setup mode))
    (scan : checkpoint.commitExclusionWord first = checkpoint.commitExclusionWord second) :
    (checkpoint.commitInstructionWord first).map
        (fun joint owner => CommitRecoveryMove.missed (joint owner)) =
      (checkpoint.commitInstructionWord second).map
        (fun joint owner => CommitRecoveryMove.missed (joint owner)) := by
  unfold RecoverySourceCheckpoint.commitInstructionWord
  unfold RecoverySourceCheckpoint.commitExclusionWord at scan
  generalize decomposition : commitPhase checkpoint.residual.tail = segment at scan ⊢
  rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
  dsimp only at scan ⊢
  exact omission_word_eq_of_exclusion_scan _ _ scan

private theorem RecoverySourceCheckpoint.commit_word_boundary
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (native : EventGraphRuntime.State (serviceGraph setup mode)) :
    (checkpoint.commitInstructionWord native).length +
        ProtocolState.commitEnd setup.program (checkpoint.residual.lift
          (ProtocolState.entry checkpoint.residual.tail checkpoint.source)) =
      ProtocolState.remaining setup.program (checkpoint.residual.lift
        (ProtocolState.entry checkpoint.residual.tail checkpoint.source)) := by
  rw [checkpoint.commitEnd, checkpoint.remaining]
  unfold RecoverySourceCheckpoint.commitInstructionWord
  generalize decomposition : commitPhase checkpoint.residual.tail = segment at ⊢
  rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
  dsimp only
  rw [CommitPrefix.Attempt.joints_length, ← reconstruct,
    block.commitEnd_entry_prepend suffix boundary, ProtocolState.remaining_entry,
    block.instructionCount_prepend]

/-- The SAME checkpoint's genuinely chosen closed source histories have one
complete erased reset image when their original physical failure scans agree.
Both actual source paths and literal decoded instruction words are retained;
neither the reset endpoint nor a continuation equality is supplied. -/
theorem RecoverySourceCheckpoint.failed_commit_history_eq_of_scan [Fintype Player]
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (observer : Player) (first second : EventGraphRuntime.State (serviceGraph setup mode))
    (committing : ProtocolState.atCommit checkpoint.residual.tail
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source) = true)
    (archives : state.ArchivedExclusions)
    (saved : state.entry.native.config.cut.IsPrefix state.attempt.phase)
    (firstExtension : state.entry.native.PublicFailureExtension first)
    (secondExtension : state.entry.native.PublicFailureExtension second)
    (completed : ∀ native ∈ [first, second],
      match commitPhase checkpoint.residual.tail with
      | ⟨_, _, suffix, block, reconstruct, _⟩ =>
        let embedding := cast (congrArg (fun program => OutputEmbedding
          (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
            checkpoint.embedding
        ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
          embedding.event index ∈ native.config.cut.completed)
    (footprint : first.sourceFailureFootprint = second.sourceFailureFootprint)
    (firstClosed secondClosed : setup.commitRecoveryProtocol.History)
    {firstFuel secondFuel : Nat}
    (firstPath : setup.commitRecoveryProtocol.ReachesWithin firstFuel
      ⟨_, checkpoint.trace⟩ firstClosed)
    (secondPath : setup.commitRecoveryProtocol.ReachesWithin secondFuel
      ⟨_, checkpoint.trace⟩ secondClosed)
    (firstInstructions : setup.recoveryJointRecall firstClosed.trace =
      (checkpoint.commitInstructionWord first).reverse ++
        setup.recoveryJointRecall checkpoint.trace)
    (secondInstructions : setup.recoveryJointRecall secondClosed.trace =
      (checkpoint.commitInstructionWord second).reverse ++
        setup.recoveryJointRecall checkpoint.trace)
    (failed : firstClosed.state.elim False
      (fun after => (after.excluded \ state.entry.excluded).Nonempty)) :
    setup.commitRecoveryErasedHistory firstClosed =
      setup.commitRecoveryErasedHistory secondClosed := by
  have leftCompleted := completed first (List.mem_cons_self)
  have rightCompleted := completed second (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have firstScan := checkpoint.commit_exclusion_scan first archives saved firstExtension
    leftCompleted
  have secondScan := checkpoint.commit_exclusion_scan second archives saved secondExtension
    rightCompleted
  have wordLengths : (checkpoint.commitInstructionWord first).length =
      (checkpoint.commitInstructionWord second).length := by
    unfold RecoverySourceCheckpoint.commitInstructionWord
    generalize decomposition : commitPhase checkpoint.residual.tail = segment
    rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
    dsimp only
    rw [CommitPrefix.Attempt.joints_length, CommitPrefix.Attempt.joints_length]
  have scan : checkpoint.commitExclusionWord first = checkpoint.commitExclusionWord second := by
    rw [firstScan, secondScan, wordLengths]
    exact congrArg (fun scan => (List.range (checkpoint.commitInstructionWord second).length).map
      (fun index => PhaseRuntimeState.archivedFailureOwners state.retired ∪
        scan (state.attempt.phase + index + 1))) (congrArg Prod.fst footprint)
  have omissions := checkpoint.commit_omission_word_eq first second scan
  have same :
      (setup.recoveryJointRecall firstClosed.trace).map
          (fun joint owner => CommitRecoveryMove.missed (joint owner)) =
        (setup.recoveryJointRecall secondClosed.trace).map
          (fun joint owner => CommitRecoveryMove.missed (joint owner)) := by
    rw [firstInstructions, secondInstructions, List.map_append, List.map_append,
      List.map_reverse, List.map_reverse, omissions]
  have lengths := congrArg List.length firstInstructions
  simp only [setup.recoveryJointRecall_length, List.length_append, List.length_reverse] at lengths
  have boundary := checkpoint.commit_word_boundary first
  exact setup.commitRecovery_failed_attempt_erased_eq observer _ checkpoint.trace
    ((checkpoint.atCommit _).trans committing) firstClosed.trace secondClosed.trace
    firstPath.tracePrefix secondPath.tracePrefix same
    (by dsimp only [CommitRecoveryState.atPoint]; omega) failed

/-- The selected reset checkpoints extend the SAME original source history.
All typed saved fields and public observations agree after removing only
private remembered choices; those choices remain present in the actual traces. -/
def PairedBindingResetSources
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (left right : PhaseRuntimeState (serviceGraph setup mode))
    (leftImage rightImage : RecoveryState (serviceGraph setup mode)) : Prop :=
  ∃ (leftNext : RecoverySourceCheckpoint setup mode left)
    (rightNext : RecoverySourceCheckpoint setup mode right),
    (∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨_, checkpoint.trace⟩ ⟨_, leftNext.trace⟩) ∧
    (∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨_, checkpoint.trace⟩ ⟨_, rightNext.trace⟩) ∧
    leftNext.residual.lift (ProtocolState.entry leftNext.residual.tail leftNext.source) =
      ProtocolState.withHistory setup.program
        (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
        (ProtocolState.history setup.program (checkpoint.commitResultPoint leftImage)) ∧
    rightNext.residual.lift (ProtocolState.entry rightNext.residual.tail rightNext.source) =
      ProtocolState.withHistory setup.program
        (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
        (ProtocolState.history setup.program (checkpoint.commitResultPoint rightImage)) ∧
    setup.recoveryJointRecall leftNext.trace =
      (checkpoint.commitInstructionWord leftImage.native).reverse ++
        setup.recoveryJointRecall checkpoint.trace ∧
    setup.recoveryJointRecall rightNext.trace =
      (checkpoint.commitInstructionWord rightImage.native).reverse ++
        setup.recoveryJointRecall checkpoint.trace ∧
    (∀ owner, owner ∉ leftImage.excluded →
      leftNext.source.history owner = checkpoint.source.history owner ++
        (decodeHistory setup.program (leftImage.native.config.history.map
          ((toEventGraph setup.program).fromModeCompletion mode)) owner).drop
            (decodeHistory setup.program (state.entry.native.config.history.map
              ((toEventGraph setup.program).fromModeCompletion mode)) owner).length) ∧
    (∀ owner, owner ∉ rightImage.excluded →
      rightNext.source.history owner = checkpoint.source.history owner ++
        (decodeHistory setup.program (rightImage.native.config.history.map
          ((toEventGraph setup.program).fromModeCompletion mode)) owner).drop
            (decodeHistory setup.program (state.entry.native.config.history.map
              ((toEventGraph setup.program).fromModeCompletion mode)) owner).length) ∧
    setup.commitRecoveryErasedHistory ⟨_, leftNext.trace⟩ =
      setup.commitRecoveryErasedHistory ⟨_, rightNext.trace⟩ ∧
    ∀ labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool,
      setup.proposalRecoveryErasedHistory ⟨_, setup.proposalRecoveryLiftTrace labels
        leftNext.trace⟩ =
      setup.proposalRecoveryErasedHistory ⟨_, setup.proposalRecoveryLiftTrace labels
        rightNext.trace⟩

section ActualReset

variable [Fintype Player]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "graph" => serviceGraph setup mode
local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "inputs" => setup.initialLaw.map encodeInputs
local notation "nativeInitial" =>
  PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw)

private theorem binding_reset_sources_of_actual_closings
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (horizon : Nat) (scheduler : (app).Scheduler)
    (anchor : (app).Control)
    (anchorTrace : ((menu).protocol nativeInitial horizon scheduler).Trace (some anchor))
    (checkpoint : RecoverySourceCheckpoint setup mode anchor.execution.application)
    (phase : RuntimePhase graph) (installed : phase ∈ anchor.execution.application.phases.head?)
    (kind : phase.kind = .commitment) (observer : Player) (owned : observer ∈ phase.owners)
    (before ending : Bool → (app).Control)
    (priors : ∀ side, ((menu).protocol nativeInitial horizon scheduler).Trace (some (before side)))
    (kept : ∀ side, TracePrefix anchorTrace (priors side))
    (same : ∀ side, (before side).execution.application.attempt =
      anchor.execution.application.attempt)
    (changed : ∀ side, (ending side).execution.application.attempt ≠
      anchor.execution.application.attempt)
    (raw : Bool → RecoveryState graph)
    (effects : ∀ side, PhaseClosingEffect runtime leaks (before side).execution
      (ending side).execution (raw side))
    (normalized : ∀ side, (ending side).execution.application =
      ({ (before side).execution.application with current := raw side } :
        PhaseRuntimeState graph).normalize)
    (finished : ∀ side, phase.Finished (phase.drain (raw side)))
    (excluded : ∀ side, (phase.drain (raw side)).excluded =
      (ending side).execution.application.current.excluded)
    (survives : ∀ side, observer ∉ (ending side).execution.application.current.excluded)
    (sameExcluded : (phase.drain (raw false)).excluded = (phase.drain (raw true)).excluded)
    (footprint : (phase.drain (raw false)).native.sourceFailureFootprint =
      (phase.drain (raw true)).native.sourceFailureFootprint)
    (newFailure : ((phase.drain (raw true)).excluded \
      anchor.execution.application.entry.excluded).Nonempty) :
    PairedBindingResetSources checkpoint (ending false).execution.application
      (ending true).execution.application (phase.drain (raw false))
        (phase.drain (raw true)) := by
  classical
  have initialized : ∀ state ∈ (nativeInitial).support, state.Ordered := by
    intro state reached
    obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ reached
    exact PhaseRuntimeState.initial_ordered plan draw
  have anchorOrdered := (phaseApplication_seedOrder runtime leaks).history nativeInitial horizon
    scheduler initialized ((menu).toRawTrace nativeInitial horizon scheduler anchorTrace)
  have metadata := fun side => phaseProposal_same_attempt_archive_metadata setup mode runtime leaks
    bounds plan horizon scheduler anchor (before side) anchorTrace (priors side) (kept side)
      (same side).symm
  have entries : ∀ side, (before side).execution.application.entry =
      anchor.execution.application.entry := by
    intro side
    exact ((phase_attempt_progress_of_prefix runtime leaks menu nativeInitial initialized horizon
      scheduler anchor (before side) anchorTrace (priors side) (kept side)
        anchorOrdered).2.2 (same side).symm).symm
  have generations : ∀ side, (before side).execution.application.generation =
      anchor.execution.application.generation :=
    fun side => congrArg CommitAttemptId.generation (same side)
  let frames := fun side =>
    ({anchor.execution.application with current := raw side} : PhaseRuntimeState graph)
  have rawFrames : ∀ side,
      ({(before side).execution.application with current := raw side} : PhaseRuntimeState graph) =
        frames side := by
    intro side
    have controls := metadata side
    have entry := entries side
    have generation := generations side
    cases beforeEq : (before side).execution.application
    cases anchorEq : anchor.execution.application
    simp_all only [frames]
  have actual : ∀ side, (ending side).execution.application = (frames side).normalize := by
    intro side
    rw [normalized side, rawFrames side]
  have changedFrames : ∀ side, (frames side).normalize.attempt ≠ (frames side).attempt := by
    intro side
    rw [← actual side]
    exact changed side
  have endingEntry : ∀ side, (ending side).execution.application.entry.excluded =
      (ending side).execution.application.current.excluded := by
    intro side
    rw [actual side]
    exact PhaseRuntimeState.normalize_entry_excluded_of_changed _ (changedFrames side)
  obtain ⟨remaining, phases⟩ := List.head?_eq_some_iff.mp (Option.mem_def.mp installed)
  have low : anchor.execution.application.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, phases, List.head?_cons, Option.map_some,
      Option.getD_some]
  have committing := checkpoint.compiled.atCommit_of_bindingPhase setup.program mode
    checkpoint.residual.tail checkpoint.refs checkpoint.source.revelations
    checkpoint.registry checkpoint.embedding checkpoint.before
    anchor.execution.application.attempt.phase phase kind low.symm checkpoint.source
  have chain := (phasePlanGeometry_history runtime leaks plan maximal inputs horizon scheduler
    ((menu).toRawTrace nativeInitial horizon scheduler anchorTrace)).2.2
  have front := (phaseExclusionRecord_history runtime leaks plan inputs horizon scheduler
    ((menu).toRawTrace nativeInitial horizon scheduler anchorTrace)).frontier
  have geometry := checkpoint.commit_phase_geometry phase remaining phases kind front chain
  have rawFacts := fun side => phaseClosingEffect_checkpoint_facts setup mode runtime leaks bounds
    plan horizon scheduler (before side) (ending side) (priors side) (raw side) (effects side)
      (by simpa only [same side] using changed side)
  have selected : ∀ side, ∃ next : RecoverySourceCheckpoint setup mode
      (ending side).execution.application,
      (∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
        ⟨_, checkpoint.trace⟩ ⟨_, next.trace⟩) ∧
      next.residual.lift (ProtocolState.entry next.residual.tail next.source) =
        ProtocolState.withHistory setup.program
          (checkpoint.residual.lift
            (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
          (ProtocolState.history setup.program
            (checkpoint.commitResultPoint (phase.drain (raw side)))) ∧
      setup.recoveryJointRecall next.trace =
        (checkpoint.commitInstructionWord (phase.drain (raw side)).native).reverse ++
          setup.recoveryJointRecall checkpoint.trace ∧
      (∀ owner, owner ∉ (phase.drain (raw side)).excluded →
        next.source.history owner = checkpoint.source.history owner ++
          (decodeHistory setup.program ((phase.drain (raw side)).native.config.history.map
            ((toEventGraph setup.program).fromModeCompletion mode)) owner).drop
              (decodeHistory setup.program
                (anchor.execution.application.entry.native.config.history.map
                  ((toEventGraph setup.program).fromModeCompletion mode)) owner).length) := by
    intro side
    obtain ⟨native, binding, receipts, stored, remembered, _coverage⟩ := rawFacts side
    rw [rawFrames side] at native binding receipts stored remembered
    obtain ⟨draw, invariant⟩ := native
    have missed : (((phase.drain (raw side)).excluded \
        anchor.execution.application.entry.excluded) ∩ phase.owners).Nonempty := by
      have failure : ((phase.drain (raw side)).excluded \
          anchor.execution.application.entry.excluded).Nonempty := by
        cases side
        · rwa [sameExcluded]
        · exact newFailure
      obtain ⟨owner, member⟩ := failure
      have active : owner ∉ anchor.execution.application.entry.excluded :=
        (Finset.mem_sdiff.mp member).2
      have record := (receipts.exclusion.installed phase (by
        simpa only [frames] using installed)).phase_drain phase
      rcases (record.excluded owner).mp (Finset.mem_sdiff.mp member).1 with
        inherited | ⟨event, lower, acting, failed⟩
      · exact (active inherited).elim
      · have within := receipts.exclusion.frontier.positioned
        change PhaseRuntimeState.Positioned _ _ _ at within
        rw [show (frames side).phases = phase :: remaining from phases] at within
        have upper := (phase.drain_within (raw side) within.2).2 event failed.completed
        refine ⟨owner, Finset.mem_inter.mpr ⟨member, ?_⟩⟩
        exact Finset.mem_biUnion.mpr ⟨event, (phase.mem_events event).mpr ⟨lower, upper⟩,
          by simpa only [Option.mem_toFinset, Option.mem_def] using acting⟩
    have survivor : (phase.owners \ (phase.drain (raw side)).excluded).Nonempty :=
      ⟨observer, Finset.mem_sdiff.mpr ⟨owned, by simpa only [excluded side] using survives side⟩⟩
    let cp : RecoverySourceCheckpoint setup mode (frames side) := checkpoint.transfer rfl rfl rfl
    obtain ⟨next, point, ⟨fuel, path, word⟩, own⟩ := cp.after_commit_retry committing phase
      remaining phases chain binding receipts remembered invariant (finished side) missed survivor
    rw [actual side]
    exact ⟨next, ⟨fuel, path⟩, point, word, own⟩
  choose next paths points words own using selected
  have completed : ∀ native ∈ [(phase.drain (raw false)).native,
      (phase.drain (raw true)).native],
      match commitPhase checkpoint.residual.tail with
      | ⟨_, _, suffix, block, reconstruct, _⟩ =>
        let embedding := cast (congrArg (fun program => OutputEmbedding
          (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
            checkpoint.embedding
        ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
          embedding.event index ∈ native.config.cut.completed := by
    intro native member
    generalize decomposition : commitPhase checkpoint.residual.tail = segment at geometry ⊢
    rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
    dsimp only at geometry ⊢
    intro index bound
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact finished false (geometry.2 index bound)
    · exact finished true (geometry.2 index bound)
  have extensions : ∀ side, anchor.execution.application.entry.native.PublicFailureExtension
      (phase.drain (raw side)).native := by
    intro side
    have frame := phaseClosingEffect_failure_frame setup mode runtime leaks bounds plan horizon
      scheduler (before side) (ending side) (priors side) (raw side) (effects side)
    rw [rawFrames side] at frame
    exact frame.trans (phase.drain_publicFailureExtension (raw side))
  have saved := front.positioned
  rw [phases] at saved
  have reset := checkpoint.failed_commit_history_eq_of_scan observer
    (phase.drain (raw false)).native (phase.drain (raw true)).native committing
    (phaseArchivedExclusions_history runtime leaks plan inputs horizon scheduler
      ((menu).toRawTrace nativeInitial horizon scheduler anchorTrace))
    (by simpa only [low] using saved.1) (extensions false) (extensions true) completed footprint
    ⟨_, (next false).trace⟩ ⟨_, (next true).trace⟩ (paths false).choose_spec
    (paths true).choose_spec (words false) (words true) (by
      change (((ending false).execution.application.entry.excluded) \
        anchor.execution.application.entry.excluded).Nonempty
      rw [endingEntry false, ← excluded false, sameExcluded]
      exact newFailure)
  refine ⟨next false, next true, paths false, paths true, points false, points true,
    words false, words true,
    own false, own true, reset, ?_⟩
  intro labels
  have leftLength := congrArg List.length (words false)
  have rightLength := congrArg List.length (words true)
  simp only [setup.recoveryJointRecall_length, List.length_append, List.length_reverse]
    at leftLength rightLength
  have leftBoundary := checkpoint.commit_word_boundary (phase.drain (raw false)).native
  have rightBoundary := checkpoint.commit_word_boundary (phase.drain (raw true)).native
  let first := CommitRecoveryState.atPoint
    (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
      anchor.execution.application.entry.excluded anchor.execution.application.generation
  have firstCommit : ProtocolState.atCommit setup.program first.point = true :=
    (checkpoint.atCommit _).trans committing
  have sameLength : (next false).trace.length = (next true).trace.length := by omega
  dsimp only [Setup.proposalRecoveryErasedHistory]
  apply Prod.ext
  · simpa only [setup.proposalRecoveryEraseTrace_lift] using reset
  · change setup.proposalRecoveryDeltaRecall
        (setup.proposalRecoveryLiftTrace labels (next false).trace) =
      setup.proposalRecoveryDeltaRecall (setup.proposalRecoveryLiftTrace labels (next true).trace)
    rw [setup.proposalRecoveryDeltaRecall_commit_window first
      (setup.proposalRecoveryLiftTrace labels checkpoint.trace) firstCommit
      (setup.proposalRecoveryLiftTrace labels (next false).trace)
      (setup.proposalRecoveryLiftTrace_prefix labels (paths false).choose_spec.tracePrefix)
      (by simp only [setup.proposalRecoveryLiftTrace_length]
          dsimp only [first, CommitRecoveryState.atPoint]
          omega),
      setup.proposalRecoveryDeltaRecall_commit_window first
      (setup.proposalRecoveryLiftTrace labels checkpoint.trace) firstCommit
      (setup.proposalRecoveryLiftTrace labels (next true).trace)
      (setup.proposalRecoveryLiftTrace_prefix labels (paths true).choose_spec.tracePrefix)
      (by simp only [setup.proposalRecoveryLiftTrace_length]
          dsimp only [first, CommitRecoveryState.atPoint]
          omega)]
    simp only [setup.proposalRecoveryLiftTrace_length, sameLength]

open scoped Classical in
/-- Every actual stopped comparator-surviving pair with a new foreign omission
reaches SAME erased source reset histories from the original checkpoint.
The actual surviving receipt word is derived, never assumed. -/
theorem phaseProposalUnflagged_available_send_reset_boundary
    (complete : leaks = MessageNetwork.completePendingObservation)
    (coveredValues : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (ordered : (graph).RevealRelaxedOrdered)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (capacity : ReservedEpoch.executionHorizon runtime ≤ bounds.candidateCount)
    (remaining : Nat) (active : (app).Execution) (actor : Player)
    (leftResponse rightResponse : (app).Action)
    (activeTrace : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
        (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
          (some ⟨remaining, some actor, active⟩))
    (leftAvailable : leftResponse ∈ (menu).actions actor
      (active.recall actor) (active.observe app actor))
    (rightAvailable : rightResponse ∈ (menu).actions actor
      (active.recall actor) (active.observe app actor))
    (leftSends : leftResponse.transmission ≠ none)
    (phase : RuntimePhase graph) (installed : phase ∈ active.application.phases.head?)
    (commitment : phase.kind = .commitment)
    (checkpoint : RecoverySourceCheckpoint setup mode active.application) :
    let initial := (inputs).map (PhaseRuntimeState.initial plan)
    let horizon := ReservedEpoch.executionHorizon runtime
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let anchor := fun response : (app).Action => active.respond app actor response
    ∃ leftTrace : ((menu).protocol initial horizon scheduler).Trace
        (some ⟨remaining, none, anchor leftResponse⟩),
    ∃ rightTrace : ((menu).protocol initial horizon scheduler).Trace
        (some ⟨remaining, none, anchor rightResponse⟩),
    TracePrefix activeTrace leftTrace ∧ TracePrefix activeTrace rightTrace ∧
    let law := fun response (trace : ((menu).protocol initial horizon scheduler).Trace
        (some ⟨remaining, none, anchor response⟩)) =>
      let players := ReactiveApplication.anchoredPolicy (anchor response)
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values)
      let profile := fun who => (menu).restrictPolicy initial horizon scheduler who (players who)
      let stopped := fun history : ((menu).protocol initial horizon scheduler).History =>
        match history.state with
        | none => False
        | some control =>
            control.execution.application.attempt ≠ (anchor response).application.attempt
      ((menu).information initial horizon scheduler).runBehavioralUntil
        ((menu).bounded initial horizon scheduler).wellFoundedHistories profile stopped
          ⟨some ⟨remaining, none, anchor response⟩, trace⟩
    ∀ leftFinal ∈ (law leftResponse leftTrace).support,
    ∀ rightFinal ∈ (law rightResponse rightTrace).support,
      ∃ (leftEnding rightEnding leftBefore rightBefore : (app).Control)
        (leftPrior : ((menu).protocol initial horizon scheduler).Trace (some leftBefore))
        (rightPrior : ((menu).protocol initial horizon scheduler).Trace (some rightBefore))
        (leftJoint rightJoint : Player → Option (app).Action)
        (leftLegal : ((menu).protocol initial horizon scheduler).Legal (some leftBefore) leftJoint)
        (rightLegal : ((menu).protocol initial horizon scheduler).Legal
          (some rightBefore) rightJoint)
        (leftRealized : some leftEnding ∈ ((app).transition initial horizon scheduler
          (some leftBefore) leftJoint).support)
        (rightRealized : some rightEnding ∈ ((app).transition initial horizon scheduler
          (some rightBefore) rightJoint).support)
        (leftRaw rightRaw : RecoveryState graph),
        leftFinal.state = some leftEnding ∧ rightFinal.state = some rightEnding ∧
        TracePrefix leftTrace leftPrior ∧ TracePrefix rightTrace rightPrior ∧
        TracePrefix (leftPrior.extend leftJoint leftLegal leftRealized) leftFinal.trace ∧
        TracePrefix (rightPrior.extend rightJoint rightLegal rightRealized) rightFinal.trace ∧
        leftBefore.execution.application.attempt = active.application.attempt ∧
        rightBefore.execution.application.attempt = active.application.attempt ∧
        PhaseClosingEffect runtime leaks leftBefore.execution leftEnding.execution leftRaw ∧
        PhaseClosingEffect runtime leaks rightBefore.execution rightEnding.execution rightRaw ∧
        phase ∈ leftBefore.execution.application.phases.head? ∧
        phase ∈ rightBefore.execution.application.phases.head? ∧
        phase.Finished (phase.drain leftRaw) ∧ phase.Finished (phase.drain rightRaw) ∧
        leftEnding.actor = none ∧ rightEnding.actor = none ∧
        leftEnding.execution.application.attempt ≠ active.application.attempt ∧
        rightEnding.execution.application.attempt ≠ active.application.attempt ∧
        leftEnding.execution.application =
          ({ leftBefore.execution.application with current := leftRaw } :
            PhaseRuntimeState graph).normalize ∧
        rightEnding.execution.application =
          ({ rightBefore.execution.application with current := rightRaw } :
            PhaseRuntimeState graph).normalize ∧
        (phase.drain leftRaw).FailureCoverage ∧
        (phase.drain rightRaw).FailureCoverage ∧
        (phase.drain leftRaw).excluded = leftEnding.execution.application.current.excluded ∧
        (phase.drain rightRaw).excluded = rightEnding.execution.application.current.excluded ∧
        PhaseProposal.sourceArchive leftEnding.execution.network.inputs =
          PhaseProposal.sourceArchive rightEnding.execution.network.inputs ∧
        (∀ event ∈ phase.events, ∀ owner payload,
          (graph).outputLayout event = .binding owner payload →
          (leftRaw.native.accepted (.inr event) ≠ none ↔
            ReservedEpoch.ownedAcceptanceWord runtime leaks tape
              (anchor leftResponse) owner event)) ∧
        (∀ event ∈ phase.events, ∀ owner payload,
          (graph).outputLayout event = .binding owner payload →
          (rightRaw.native.accepted (.inr event) ≠ none ↔
            ReservedEpoch.ownedAcceptanceWord runtime leaks tape
              (anchor rightResponse) owner event)) ∧
        (∀ event ∈ phase.events, ∀ owner payload, owner ≠ actor →
          (graph).outputLayout event = .binding owner payload →
          (leftRaw.native.accepted (.inr event) ≠ none ↔
            rightRaw.native.accepted (.inr event) ≠ none)) ∧
        (actor ∉ rightEnding.execution.application.current.excluded →
          actor ∉ leftEnding.execution.application.current.excluded ∧
          (∀ event ∈ phase.events, ∀ payload,
            (graph).outputLayout event = .binding actor payload →
            rightRaw.native.accepted (.inr event) ≠ none) ∧
          (∀ event ∈ phase.events, ∀ payload,
            (graph).outputLayout event = .binding actor payload →
            leftRaw.native.accepted (.inr event) ≠ none) ∧
          (phase.drain leftRaw).native.sourceFailureFootprint =
            (phase.drain rightRaw).native.sourceFailureFootprint ∧
          (phase.drain leftRaw).excluded = (phase.drain rightRaw).excluded ∧
          PhaseRuntimeState.sourceControlRecords leftEnding.execution.application.retired =
            PhaseRuntimeState.sourceControlRecords rightEnding.execution.application.retired ∧
          (((phase.drain rightRaw).excluded \ active.application.entry.excluded).Nonempty →
            PairedBindingResetSources checkpoint leftEnding.execution.application
              rightEnding.execution.application (phase.drain leftRaw)
                (phase.drain rightRaw))) := by
  classical
  intro initial horizon scheduler anchor
  obtain ⟨leftTrace, rightTrace, leftResponsePrefix, rightResponsePrefix, paired⟩ :=
    phaseProposalUnflagged_available_send_stopped_word setup mode runtime leaks bounds plan complete
      coveredValues maximal ordered values fullValues tape activationGap processingGap gaps margin
      capacity remaining active actor leftResponse rightResponse activeTrace leftAvailable
      rightAvailable leftSends phase installed commitment
  refine ⟨leftTrace, rightTrace, leftResponsePrefix, rightResponsePrefix, ?_⟩
  intro law leftFinal leftSupported rightFinal rightSupported
  obtain ⟨leftEnding, rightEnding, leftBefore, rightBefore, leftPrior, rightPrior, leftJoint,
    rightJoint, leftLegal, rightLegal, leftRealized, rightRealized, leftRaw, rightRaw,
    leftState, rightState, leftPrefix, rightPrefix, leftEndPrefix, rightEndPrefix,
    leftAttempt, rightAttempt, leftEffect, rightEffect, leftInstalled, rightInstalled,
    leftFinished, rightFinished, leftIdle, rightIdle, leftChanged, rightChanged,
    leftNormalized, rightNormalized, leftCoverage, rightCoverage, leftExcluded,
    rightExcluded, archive, leftWord, rightWord, foreignWord, surviving⟩ :=
      paired leftFinal (by
        convert leftSupported using 1
        dsimp only [law]
        apply congrArg (fun mass : PMF ((menu).protocol initial horizon scheduler).History =>
          mass.support)
        apply congrArg (fun stopped : ((menu).protocol initial horizon scheduler).History → Prop =>
          ((menu).information initial horizon scheduler).runBehavioralUntil
            ((menu).bounded initial horizon scheduler).wellFoundedHistories
            (fun who => (menu).restrictPolicy initial horizon scheduler who
              (ReactiveApplication.anchoredPolicy (anchor leftResponse)
                (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who))
            stopped ⟨some ⟨remaining, none, anchor leftResponse⟩, leftTrace⟩)
        funext history
        cases history.state <;> rfl)
        rightFinal (by
          convert rightSupported using 1
          dsimp only [law]
          apply congrArg (fun mass : PMF ((menu).protocol initial horizon scheduler).History =>
            mass.support)
          apply congrArg (fun stopped :
              ((menu).protocol initial horizon scheduler).History → Prop =>
            ((menu).information initial horizon scheduler).runBehavioralUntil
              ((menu).bounded initial horizon scheduler).wellFoundedHistories
              (fun who => (menu).restrictPolicy initial horizon scheduler who
                (ReactiveApplication.anchoredPolicy (anchor rightResponse)
                  (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who))
              stopped ⟨some ⟨remaining, none, anchor rightResponse⟩, rightTrace⟩)
          funext history
          cases history.state <;> rfl)
  refine ⟨leftEnding, rightEnding, leftBefore, rightBefore, leftPrior, rightPrior, leftJoint,
    rightJoint, leftLegal, rightLegal, leftRealized, rightRealized, leftRaw, rightRaw,
    leftState, rightState, leftPrefix, rightPrefix, leftEndPrefix, rightEndPrefix,
    leftAttempt, rightAttempt, leftEffect, rightEffect, leftInstalled, rightInstalled,
    leftFinished, rightFinished, leftIdle, rightIdle, leftChanged, rightChanged,
    leftNormalized, rightNormalized, leftCoverage, rightCoverage, leftExcluded,
    rightExcluded, archive, leftWord, rightWord, foreignWord, ?_⟩
  intro rightSurvives
  obtain ⟨leftSurvives, rightAccepted, leftAccepted, footprint, sameExcluded, records⟩ :=
    surviving rightSurvives
  refine ⟨leftSurvives, rightAccepted, leftAccepted, footprint, sameExcluded, records, ?_⟩
  intro newFailure
  obtain ⟨material, sent⟩ : ∃ material : WitnessedSubmission graph,
      leftResponse = ⟨some material⟩ := by
    rcases leftResponse with ⟨transmission⟩
    cases transmission with
    | none => exact (leftSends rfl).elim
    | some material => exact ⟨material, rfl⟩
  have offered : (⟨some material⟩ : (app).Action) ∈ (menu).actions actor
      (active.recall actor) (active.observe app actor) := by
    simpa only [sent] using leftAvailable
  obtain ⟨coordinate, requested⟩ := PhaseCount.onePacket_request_of_nonsilent runtime leaks bounds
    plan inputs horizon scheduler remaining actor active activeTrace material offered
  obtain ⟨actualPhase, actualInstalled, inside⟩ := requested.2.1
  have phaseEq : actualPhase = phase := Option.some.inj
    ((Option.mem_def.mp actualInstalled).symm.trans (Option.mem_def.mp installed))
  subst actualPhase
  have owned : actor ∈ phase.owners := Finset.mem_biUnion.mpr
    ⟨coordinate.event, inside, by simpa only [Option.mem_toFinset, Option.mem_def]
      using requested.2.2.2.1⟩
  let before : Bool → (app).Control := fun side => if side then rightBefore else leftBefore
  let ending : Bool → (app).Control := fun side => if side then rightEnding else leftEnding
  let raw : Bool → RecoveryState graph := fun side => if side then rightRaw else leftRaw
  let priors : ∀ side, ((menu).protocol initial horizon scheduler).Trace (some (before side)) :=
    fun side => by
      cases side
      · exact leftPrior
      · exact rightPrior
  refine binding_reset_sources_of_actual_closings setup mode runtime leaks bounds plan maximal
    horizon scheduler ⟨remaining, some actor, active⟩ activeTrace checkpoint phase installed
    commitment actor owned before ending priors ?_ ?_ ?_ raw ?_ ?_ ?_ ?_ ?_
      sameExcluded footprint newFailure
  · intro side
    cases side
    · exact leftResponsePrefix.trans leftPrefix
    · exact rightResponsePrefix.trans rightPrefix
  · intro side
    cases side
    · exact leftAttempt
    · exact rightAttempt
  · intro side
    cases side
    · exact leftChanged
    · exact rightChanged
  · intro side
    cases side
    · exact leftEffect
    · exact rightEffect
  · intro side
    cases side
    · exact leftNormalized
    · exact rightNormalized
  · intro side
    cases side
    · exact leftFinished
    · exact rightFinished
  · intro side
    cases side
    · exact leftExcluded
    · exact rightExcluded
  · intro side
    cases side
    · exact leftSurvives
    · exact rightSurvives

end ActualReset
end Vegas
