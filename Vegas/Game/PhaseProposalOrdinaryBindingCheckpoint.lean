/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalOrdinaryStoppedSourceHistory

/-! # The same chosen checkpoint at an actual clean binding close -/

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
local notation "inputs" => setup.initialLaw.map encodeInputs
local notation "initial" =>
  PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw)

theorem phaseClosingEffect_checkpoint_facts
    (horizon : Nat) (scheduler : (app).Scheduler)
    (before ending : (app).Control)
    (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
    (raw : RecoveryState graph)
    (effect : PhaseClosingEffect runtime leaks before.execution ending.execution raw)
    (changed : ending.execution.application.attempt ≠ before.execution.application.attempt) :
    let state : PhaseRuntimeState graph := { before.execution.application with current := raw }
    (∃ draw, state.Invariant draw) ∧ state.BindingRecord ∧ state.ReceiptRecord ∧
      state.StoredCheckpoint ∧ state.HistoryCheckpoint ∧ state.FailureCoverage := by
  let trace := (menu).toRawTrace initial horizon scheduler prior
  have ordered := serviceGraph_revealRelaxedOrdered setup mode
  obtain ⟨draw, native⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    trace
  have remembered := phaseHistoryCheckpoint_history runtime leaks plan inputs horizon scheduler
    trace
  have coverage := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler trace
  rcases effect with ⟨id, message, result, found, moved, handled, rfl⟩ |
      ⟨command, result, moved, supported, rfl⟩
  · have selected : ending.execution.application =
        ((app).handle before.execution.application message).getD before.execution.application := by
      have exactMove := moved
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at exactMove
      have stateEq := congrArg (fun execution : (app).Execution => execution.application)
        ((PMF.mem_support_pure_iff _ _).mp exactMove)
      simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        found] using stateEq
    have allowed : (message.payload.tokenValid before.execution.application.attempt &&
        before.execution.application.allows message.payload.packet.call &&
          (!(before.execution.application.current.excludedCall message.payload.packet.call))) =
            true := by
      by_contra invalid
      have absent : before.execution.application.handle runtime message = none := by
        simp only [PhaseRuntimeState.handle, ite_eq_right invalid]
      have same : ending.execution.application = before.execution.application := by
        simpa only [show (app).handle before.execution.application message = none from absent,
          Option.getD_none] using selected
      exact changed (congrArg PhaseRuntimeState.attempt same)
    have authorized := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp allowed).1).2
    have permitted : before.execution.application.current.excludedCall
        message.payload.packet.call = false := by
      cases flag : before.execution.application.current.excludedCall message.payload.packet.call
      · rfl
      · have negative := (Bool.and_eq_true_iff.mp allowed).2
        rw [flag] at negative
        cases negative
    let nativeMessage : Message Player (Payload graph) :=
      ⟨message.id, message.payload.packet.call⟩
    obtain ⟨binding, stored, receipts⟩ := phase_inclusion_checkpoint_history runtime leaks ordered
      plan inputs horizon scheduler trace nativeMessage result authorized permitted handled
    refine ⟨⟨draw, native.saved, handle_invariant runtime _ result nativeMessage native.active
      handled⟩, binding, receipts, stored, ?_, ?_⟩
    · apply remembered.trans
      obtain ⟨event, _named, _ready, _action, reached⟩ :=
        handle_config_mem_step runtime _ result nativeMessage handled
      change before.execution.application.current.native.config.history.IsPrefix
        result.config.history
      rw [before.execution.application.current.native.config.step_history _ _ _ _ reached]
      exact ⟨_, rfl⟩
    · exact ⟨coverage.saved, coverage.active.inclusionResult runtime nativeMessage result handled,
        coverage.inherited.trans
          (before.execution.application.current.inclusionResult_excluded_subset _ _)⟩
  · have authorized : before.execution.application.commandAllowed command = true := by
      by_contra denied
      have stutters : (app).environment before.execution.application command =
          PMF.pure before.execution.application := by
        simp only [phaseApplication, PhaseRuntimeState.environment, ite_eq_right denied]
      have literal := moved
      simp only [ReactiveApplication.Execution.environmentStep, stutters, PMF.pure_map] at literal
      have same := congrArg (fun execution : (app).Execution => execution.application)
        ((PMF.mem_support_pure_iff _ _).mp literal)
      exact changed (congrArg PhaseRuntimeState.attempt same)
    obtain ⟨binding, stored, receipts⟩ := phase_environment_checkpoint_history runtime leaks ordered
      plan inputs horizon scheduler trace command result authorized supported
    exact ⟨⟨draw, native.saved, environmentStep_invariant runtime _ result command native.active
      supported⟩, binding, receipts, stored,
      remembered.trans (environmentStep_history_prefix runtime _ result command supported),
      coverage.saved, coverage.active.environmentResult runtime command result supported,
      coverage.inherited.trans
        (before.execution.application.current.environmentResult_excluded_subset _ _)⟩

/-- The original raw closing result has the actual source-order suppression
law before the dispatcher installs another namespace. -/
theorem phaseClosingEffect_publication_order
    (horizon : Nat) (scheduler : (app).Scheduler)
    (before ending : (app).Control)
    (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
    (phase : RuntimePhase graph) (head : before.execution.application.phases.head? = some phase)
    (raw : RecoveryState graph)
    (effect : PhaseClosingEffect runtime leaks before.execution ending.execution raw)
    (changed : ending.execution.application.attempt ≠ before.execution.application.attempt) :
    (phase.drain raw).OrderedPublicFailures phase.low
      before.execution.application.entry.excluded := by
  have ordered := serviceGraph_revealRelaxedOrdered setup mode
  let rawTrace := (menu).toRawTrace initial horizon scheduler prior
  rcases effect with ⟨id, message, native, found, moved, handled, rfl⟩ |
      ⟨command, native, _moved, supported, rfl⟩
  · have selected : ending.execution.application =
        ((app).handle before.execution.application message).getD
          before.execution.application := by
      have exactMove := moved
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at exactMove
      have stateEq := congrArg (fun execution : (app).Execution => execution.application)
        ((PMF.mem_support_pure_iff _ _).mp exactMove)
      simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        found] using stateEq
    have allowed : (message.payload.tokenValid before.execution.application.attempt &&
        before.execution.application.allows message.payload.packet.call &&
          (!(before.execution.application.current.excludedCall message.payload.packet.call))) =
            true := by
      by_contra invalid
      have absent : before.execution.application.handle runtime message = none := by
        simp only [PhaseRuntimeState.handle, ite_eq_right invalid]
      have same : ending.execution.application = before.execution.application := by
        simpa only [show (app).handle before.execution.application message = none from absent,
          Option.getD_none] using selected
      exact changed (congrArg PhaseRuntimeState.attempt same)
    have permitted : before.execution.application.current.excludedCall
        message.payload.packet.call = false := by
      cases flag : before.execution.application.current.excludedCall message.payload.packet.call
      · rfl
      · have negative := (Bool.and_eq_true_iff.mp allowed).2
        rw [flag] at negative
        cases negative
    exact phase_inclusion_failureOrder_history runtime leaks ordered plan inputs horizon
      scheduler rawTrace phase head ⟨message.id, message.payload.packet.call⟩ native permitted
        handled
  · exact phase_environment_failureOrder_history runtime leaks ordered plan inputs horizon
      scheduler rawTrace phase head command native supported

/-- The original closing operation retains the saved checkpoint's failure
verdicts before any actual dispatcher normalization. -/
theorem phaseClosingEffect_failure_frame
    (horizon : Nat) (scheduler : (app).Scheduler)
    (before ending : (app).Control)
    (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
    (raw : RecoveryState graph)
    (effect : PhaseClosingEffect runtime leaks before.execution ending.execution raw) :
    ({before.execution.application with current := raw} :
      PhaseRuntimeState graph).PublicFailureCheckpoint := by
  have saved := phasePublicFailureCheckpoint_history runtime leaks plan inputs horizon scheduler
    ((menu).toRawTrace initial horizon scheduler prior)
  rcases effect with ⟨id, message, native, _found, _moved, handled, rfl⟩ |
      ⟨command, native, _moved, supported, rfl⟩
  · exact saved.trans (completionStep_handle runtime _ native
      (⟨message.id, message.payload.packet.call⟩ : Message Player (Payload graph))
        handled).publicFailureExtension
  · exact saved.trans (completionStep_environmentStep runtime _ native command
      supported).publicFailureExtension

omit [Fintype Player] in
private theorem completed_binding_word
    {state : PhaseRuntimeState graph}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : state.phases = phase :: remaining) (kind : phase.kind = .commitment)
    (maximal : state.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (binding : state.BindingRecord) (receipts : state.ReceiptRecord)
    (stored : state.StoredCheckpoint) (finished : phase.Finished (phase.drain state.current))
    (excluded : (phase.drain state.current).excluded = state.entry.excluded) :
    match commitPhase checkpoint.residual.tail with
    | ⟨_, _, suffix, block, reconstruct, _⟩ =>
      let embedding := cast (congrArg (fun program => OutputEmbedding
        (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
          checkpoint.embedding
      phaseProposalBindingWord setup.program block suffix embedding state.entry.excluded
        (phase.drain state.current).native.config.store checkpoint.source =
          checkpoint.commitInstructionWord (phase.drain state.current).native := by
  have low : phase.low = state.attempt.phase := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons,
      Option.map_some, Option.getD_some]
  have committing := checkpoint.compiled.atCommit_of_bindingPhase setup.program mode
    checkpoint.residual.tail checkpoint.refs checkpoint.source.revelations checkpoint.registry
      checkpoint.embedding checkpoint.before state.attempt.phase phase kind low checkpoint.source
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, source, refs, registry, embedding, before,
    compiled, aligned, agree, guards, failures, unique, ranks, actors, commits, owners, endpoints,
    automatic, history, memory, steps, menus, readout, trace, views, historyAlignment, origin⟩
  dsimp only [RecoverySourceCheckpoint.commitInstructionWord] at ⊢
  dsimp only at committing
  generalize decomposition : commitPhase program = segment at ⊢
  rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
  subst program
  dsimp only
  have positive : 0 < block.length := by
    cases block with
    | nil =>
        cases suffix with
        | ret => cases committing
        | sample => cases committing
        | reveal => cases committing
        | commit => cases boundary
    | commit => simp only [SourceProgram.CommitPrefix.length]; omega
  have adjacent := receipts.exclusion.frontier.adjacent
  have last := receipts.exclusion.frontier.last
  rw [installed] at adjacent last maximal
  have phaseEq := compiledCommitPhase_eq_of_maximal setup.program mode block suffix embedding
    compiled positive boundary phase remaining adjacent last maximal low
  subst phase
  let phase := compiledCommitPhase setup.program mode block suffix embedding compiled positive
  let image := phase.drain state.current
  let decoded := decodeCommitAttempt setup.program mode block suffix embedding image.native source
    state.entry.excluded
  have head : phase ∈ state.phases.head? := by
    rw [installed]
    exact Option.mem_some_iff.mpr rfl
  have positioned := receipts.exclusion.frontier.positioned
  rw [installed] at positioned
  have after := decodeCommitAttempt_excluded_eq_physical setup.program mode block suffix embedding
    compiled positive image source state.entry.excluded
      ((receipts.exclusion.installed phase head).phase_drain phase)
      (phase.drain_within state.current positioned.2) finished
  have entryAgree : refs.Agrees source.state image.native.config.store := by
    intro name cell selected
    exact (refs.get selected).get?_preserved _ _
      (fun field value present => phase.drain_keepsStore state.current field value
        (stored field value present)) _ (agree selected)
  have finalAgree : (commitBlockRefs setup.program block suffix embedding refs).Agrees
      decoded.1.state image.native.config.store := by
    apply decodeCommitAttempt_state_agrees setup.program mode block suffix embedding refs
      image.native source state.entry.excluded state.attempt.phase compiled.rankEq
        (phase.drain_bindingInvariant state.current binding.active)
        ((receipts.ordered phase head rfl).congr (phase.drain_tables state.current).1) entryAgree
    intro index inside
    exact finished ((compiledCommitPhase_mem_iff setup.program mode block suffix embedding
      compiled positive _).mpr ⟨index, inside, rfl⟩)
  exact phaseProposalBindingWord_of_ordinary_attempt setup.program block suffix embedding refs
    image.native.config.store source source state.entry.excluded decoded.1 decoded.2.1
      decoded.2.2 (after.trans excluded) finalAgree

/-- A real raw closing operation extends this same selected source checkpoint.
The returned checkpoint is at the actual drained image before further automatic
phase normalization. Its type retains the saved/current image, generation,
exclusions and all compiler references; the ending is the existing settle. -/
theorem RecoverySourceCheckpoint.ordinary_closing_binding_checkpoint
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (horizon : Nat) (scheduler : (app).Scheduler)
    (before ending : (app).Control)
    (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
    (checkpoint : RecoverySourceCheckpoint setup mode before.execution.application)
    (committing : ProtocolState.atCommit checkpoint.residual.tail
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source) = true)
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : before.execution.application.phases = phase :: remaining)
    (kind : phase.kind = .commitment)
    (raw : RecoveryState graph)
    (effect : PhaseClosingEffect runtime leaks before.execution ending.execution raw)
    (changed : ending.execution.application.attempt ≠ before.execution.application.attempt)
    (normalized : ending.execution.application =
      ({ before.execution.application with current := raw } : PhaseRuntimeState graph).normalize)
    (finished : phase.Finished (phase.drain raw))
    (excluded : (phase.drain raw).excluded = before.execution.application.entry.excluded) :
    ∃ next : RecoverySourceCheckpoint setup mode
        (⟨remaining, before.execution.application.generation, phase.drain raw, phase.drain raw,
          before.execution.application.retired⟩ : PhaseRuntimeState graph),
      next.residual.lift (ProtocolState.entry next.residual.tail next.source) =
        checkpoint.commitResultPoint (phase.drain raw) ∧
      (∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
          ⟨_, checkpoint.trace⟩ ⟨_, next.trace⟩ ∧
        setup.recoveryJointRecall next.trace =
          (checkpoint.commitInstructionWord (phase.drain raw).native).reverse ++
            setup.recoveryJointRecall checkpoint.trace) ∧
      ending.execution.application = PhaseRuntimeState.settle remaining
        before.execution.application.generation (phase.drain raw) (phase.drain raw)
          before.execution.application.retired ∧
      (match commitPhase checkpoint.residual.tail with
      | ⟨_, _, suffix, block, reconstruct, _⟩ =>
        let embedding := cast (congrArg (fun program => OutputEmbedding
          (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
            checkpoint.embedding
        phaseProposalBindingWord setup.program block suffix embedding
          before.execution.application.entry.excluded (phase.drain raw).native.config.store
            checkpoint.source = checkpoint.commitInstructionWord (phase.drain raw).native) := by
  obtain ⟨⟨draw, native⟩, binding, receipts, stored, remembered, coverage⟩ :=
    phaseClosingEffect_checkpoint_facts setup mode runtime leaks bounds plan horizon scheduler
      before ending prior raw effect changed
  let state : PhaseRuntimeState graph := { before.execution.application with current := raw }
  let transferred : RecoverySourceCheckpoint setup mode state := checkpoint.transfer rfl rfl rfl
  have chain := (phasePlanGeometry_history runtime leaks plan maximal inputs horizon scheduler
    ((menu).toRawTrace initial horizon scheduler prior)).2.2
  have clean : ¬ (((phase.drain state.current).excluded \ state.entry.excluded) ∩
      phase.owners).Nonempty := by
    change ¬ (((phase.drain raw).excluded \ before.execution.application.entry.excluded) ∩
      phase.owners).Nonempty
    rw [excluded]
    simp only [Finset.sdiff_self, Finset.empty_inter, Finset.not_nonempty_empty, not_false_eq_true]
  obtain ⟨⟨next, point, path, _own, _intended⟩, settled⟩ :=
    transferred.after_commit_clean committing phase remaining installed chain binding receipts
      stored remembered native coverage finished clean
  exact ⟨next, point, path, normalized.trans settled,
    completed_binding_word setup mode transferred phase remaining installed kind chain
      binding receipts stored finished excluded⟩

end Vegas
