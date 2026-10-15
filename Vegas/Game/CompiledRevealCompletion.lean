/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledRevealBoundary
import Vegas.Pending.PhaseFailureOrderHistory
import Vegas.Pending.PhaseNativeInvariant

/-! # Source reveal recovery paths from actual physical completion effects -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]


variable (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)
  (refs : ContextRefs (graphLayout setup.program) Γ)
  (revelations : Revelations Γ) (registry : Registry Γ)
  (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
  (before : ContextRefsBefore refs embedding) (offset : Nat)
  (compiled : CompiledSuffix setup.program program refs revelations registry embedding before
    offset)
  (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
  (kind : phase.kind = .reveal) (low : phase.low = offset) (count : Nat)
  (high : phase.high = offset + count)

/-- A permitted actual packet acceptance or supported environment effect,
followed by the real phase-local drain, supplies its legal source recovery
path and exact typed checkpoint. All execution invariants are derived from
the initialized physical history, including source-ordered exclusion. -/
theorem sourceRecovery_of_actual_revealCompletion
    (runtime : EventGraphRuntime ((toEventGraph setup.program).withMode mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph setup.program).withMode mode)))
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (inputs : PMF ((toEventGraph setup.program).withMode mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (installed : control.execution.application.phases.head? = some phase)
    (raw : RecoveryState ((toEventGraph setup.program).withMode mode))
    (effect :
      (∃ message : Message Player (Payload ((toEventGraph setup.program).withMode mode)),
        ∃ native : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode),
          control.execution.application.allows message.payload = true ∧
          control.execution.application.current.excludedCall message.payload = false ∧
          EventGraphRuntime.handle runtime control.execution.application.current.native
            message = some native ∧
          raw = control.execution.application.current.inclusionResult message.payload native) ∨
      (∃ command : EnvironmentCommand ((toEventGraph setup.program).withMode mode),
        ∃ native : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode),
          control.execution.application.commandAllowed command = true ∧
          native ∈ (environmentStep runtime control.execution.application.current.native
            command).support ∧
          raw = control.execution.application.current.environmentResult command native))
    (entry : SourceProgram.Config Player L Γ)
    (agree : refs.Agrees entry.state control.execution.application.entry.native.config.store)
    (guards : Registry.FailureExtension entry.registry registry entry.state)
    (failures : Revelations.PreservesFailures entry.revelations entry.state)
    (sameRevelations : (@Config.revelations Player L Γ entry) = @revelations)
    (unique : (Γ.map Prod.fst).Nodup) (finished : phase.Finished (phase.drain raw)) :
    let prefixed := compiled.revealPrefix_of_phase setup.program mode program refs revelations
      registry embedding before offset phase kind low count high
    ∃ final : SourceProgram.Config Player L (revealTail count program prefixed).context,
      (revealTailRefs setup count program prefixed refs embedding).Agrees
        final.state (phase.drain raw).native.config.store ∧
      Registry.FailureExtension final.registry
        (revealTailRegistry count program prefixed registry) final.state ∧
      Revelations.PreservesFailures final.revelations final.state ∧
      (@Config.revelations Player L _ final) =
        (revealTailRevelations count program prefixed revelations :
          Revelations (revealTail count program prefixed).context) ∧
      Relation.ReflTransGen
        (fun left right : ProtocolState program × Finset Player =>
          ¬ ProtocolState.terminal program left.1 ∧
          ProtocolState.atCommit program left.1 = false ∧
          ∃ joint, right ∈ (ProtocolState.recoveryStep program left.1 left.2 joint).support)
        (ProtocolState.entry program entry, control.execution.application.entry.excluded)
        ((revealTail count program prefixed).lift (ProtocolState.entry _ final),
          (phase.drain raw).excluded) ∧
      ∀ generation, (commitRecoveryProtocol program entry).Reaches
        (CommitRecoveryState.atPoint (ProtocolState.entry program entry)
          control.execution.application.entry.excluded generation)
        (CommitRecoveryState.atPoint
          ((revealTail count program prefixed).lift (ProtocolState.entry _ final))
          (phase.drain raw).excluded generation) := by
  let state := control.execution.application
  let image : PhaseRuntimeState ((toEventGraph setup.program).withMode mode) :=
    { state with current := raw }
  have relaxed := (toEventGraph setup.program).withMode_revealRelaxedOrdered
    (toEventGraph_barrierOrdered setup.program) mode
  obtain ⟨draw, actual⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    trace
  have evidence : raw.native.Invariant draw ∧ image.StoredCheckpoint ∧ image.ReceiptRecord ∧
      (phase.drain raw).OrderedPublicFailures phase.low state.entry.excluded := by
    rcases effect with ⟨message, native, allowed, permitted, handled, rfl⟩ |
        ⟨command, native, allowed, supported, rfl⟩
    · obtain ⟨_bindings, stored, receipts⟩ := phase_inclusion_checkpoint_history runtime leaks
        relaxed plan inputs horizon scheduler trace message native allowed permitted handled
      exact ⟨handle_invariant runtime _ native message actual.active handled, stored, receipts,
        phase_inclusion_failureOrder_history runtime leaks relaxed plan inputs horizon scheduler
          trace phase installed message native permitted handled⟩
    · obtain ⟨_bindings, stored, receipts⟩ := phase_environment_checkpoint_history runtime leaks
        relaxed plan inputs horizon scheduler trace command native allowed supported
      exact ⟨environmentStep_invariant runtime _ native command actual.active supported,
        stored, receipts,
        phase_environment_failureOrder_history runtime leaks relaxed plan inputs horizon scheduler
          trace phase installed command native supported⟩
  obtain ⟨rawValid, stored, receipts, ordered⟩ := evidence
  have member : phase ∈ image.phases.head? := by
    change phase ∈ control.execution.application.phases.head?
    rw [installed]
    exact Option.mem_some_iff.mpr rfl
  have within : raw.native.config.cut.Within phase.low phase.high := by
    have position := receipts.exclusion.frontier.positioned
    cases phases : image.phases with
    | nil => simp only [phases, List.head?_nil, Option.not_mem_none] at member
    | cons current remaining =>
        simp only [phases, List.head?_cons, Option.mem_some_iff] at member
        subst current
        rw [phases] at position
        exact position.2
  have prefixEnd : (phase.drain raw).native.config.cut.IsPrefix (offset + count) := by
    simpa only [high] using phase.finished_prefix (phase.drain raw)
      (phase.drain_within raw within) finished
  have record : SuffixExclusionRecord offset state.entry.excluded (phase.drain raw) := by
    rw [← low]
    exact (receipts.exclusion.installed phase member).phase_drain phase
  have afterAgree : refs.Agrees entry.state (phase.drain raw).native.config.store := by
    intro name cell source
    apply (refs.get source).get?_preserved state.entry.native.config.store _
      (fun field value present => phase.drain_keepsStore raw field value
        (stored field value present)) _ (agree source)
  obtain ⟨final, values, guards, failures, revelations, path, reaches, _word⟩ :=
    sourceRecovery_of_completed_revealPhase setup mode program refs revelations registry
    embedding before offset compiled phase kind low count high (phase.drain raw)
    (phase.drain_invariant raw rawValid).reachable state.entry.excluded record prefixEnd
    (by simpa only [low] using ordered) entry afterAgree guards failures sameRevelations unique
  exact ⟨final, values, guards, failures, revelations, path, reaches⟩

end Vegas
