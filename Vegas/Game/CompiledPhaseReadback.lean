/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledCommitReadback
import Vegas.Pending.PhaseStoredCheckpoint
import Vegas.Compile.EventGraphAssembly
import Vegas.EventGraph.Sequential

/-! # Source attempts at actual drained phase boundaries -/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ Γ Δ : SourceCtx Player L} {wholeOpen O P : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeOpen) (mode : EventGraph.ExecutionMode)
  (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
  {refs : ContextRefs (graphLayout whole) Γ} {revelations : Revelations Γ}
  {registry : Registry Γ}
  (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
    (block.prepend suffix)) {refsBefore : ContextRefsBefore refs embedding} {offset : Nat}
  (compiled : CompiledSuffix whole (block.prepend suffix) refs revelations registry embedding
    refsBefore offset) (positive : 0 < block.length)

/-- Draining a recorded installed phase reconstructs its exact typed source
attempt. The saved source environment is transported through the real immutable
store; neither exclusion equality nor source-attempt existence is assumed. -/
theorem sourceAttempt_of_drained_bindingPhase
    (state : PhaseRuntimeState ((toEventGraph whole).withMode mode))
    (installed : state.phases.head? =
      some (compiledCommitPhase whole mode block suffix embedding compiled positive))
    (valid : state.current.native.BindingInvariant) (receipts : state.ReceiptRecord)
    (stored : state.StoredCheckpoint)
    (entry : SourceProgram.Config Player L Γ)
    (agree : refs.Agrees entry.state state.entry.native.config.store)
    (guards : Registry.FailureExtension entry.registry registry entry.state)
    (finished :
      (compiledCommitPhase whole mode block suffix embedding compiled positive).Finished
        ((compiledCommitPhase whole mode block suffix embedding compiled positive).drain
          state.current)) :
    let phase := compiledCommitPhase whole mode block suffix embedding compiled positive
    ∃ finalSource : SourceProgram.Config Player L Δ,
      Nonempty (block.Attempt entry state.entry.excluded finalSource
        (phase.drain state.current).excluded) ∧
      (commitBlockRefs whole block suffix embedding refs).Agrees finalSource.state
        (phase.drain state.current).native.config.store ∧
      Registry.FailureExtension finalSource.registry (block.guardRegistry registry)
        finalSource.state := by
  let phase := compiledCommitPhase whole mode block suffix embedding compiled positive
  have member : phase ∈ state.phases.head? := by
    rw [installed]
    exact Option.mem_some_iff.mpr rfl
  have within : state.current.native.config.cut.Within phase.low phase.high := by
    have position := receipts.exclusion.frontier.positioned
    cases phases : state.phases with
    | nil => simp only [phases, List.head?_nil, Option.not_mem_none] at member
    | cons current remaining =>
        simp only [phases, List.head?_cons, Option.mem_some_iff] at member
        subst current
        rw [phases] at position
        exact position.2
  have activeAgree : refs.Agrees entry.state (phase.drain state.current).native.config.store := by
    intro name cell source
    apply (refs.get source).get?_preserved state.entry.native.config.store _
      (fun field value present => phase.drain_keepsStore state.current field value
        (stored field value present)) _ (agree source)
  exact sourceAttempt_of_completed_bindings whole mode block suffix embedding compiled positive
    (phase.drain state.current) entry state.entry.excluded
    (phase.drain_bindingInvariant state.current valid)
    ((receipts.ordered phase member rfl).congr (phase.drain_tables state.current).1)
    ((receipts.exclusion.installed phase member).phase_drain phase)
    (phase.drain_within state.current within) finished activeAgree guards

/-- A real permitted binding inclusion, before normalization archives a finished
attempt, supplies its source attempt from the actual initialized trace. -/
theorem sourceAttempt_of_actual_bindingInclusion
    (runtime : EventGraphRuntime ((toEventGraph whole).withMode mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph whole).withMode mode)))
    (plan : RuntimePhasePlan ((toEventGraph whole).withMode mode))
    (inputs : PMF ((toEventGraph whole).withMode mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (message : Message Player (Payload ((toEventGraph whole).withMode mode)))
    (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (authorized : control.execution.application.allows message.payload = true)
    (notExcluded : control.execution.application.current.excludedCall message.payload = false)
    (handled : EventGraphRuntime.handle runtime control.execution.application.current.native
      message = some native)
    (installed : control.execution.application.phases.head? =
      some (compiledCommitPhase whole mode block suffix embedding compiled positive))
    (entry : SourceProgram.Config Player L Γ)
    (agree : refs.Agrees entry.state control.execution.application.entry.native.config.store)
    (guards : Registry.FailureExtension entry.registry registry entry.state)
    (finished :
      (compiledCommitPhase whole mode block suffix embedding compiled positive).Finished
        ((compiledCommitPhase whole mode block suffix embedding compiled positive).drain
          (control.execution.application.current.inclusionResult message.payload native))) :
    let phase := compiledCommitPhase whole mode block suffix embedding compiled positive
    let image := phase.drain
      (control.execution.application.current.inclusionResult message.payload native)
    ∃ finalSource : SourceProgram.Config Player L Δ,
      Nonempty (block.Attempt entry control.execution.application.entry.excluded finalSource
        image.excluded) ∧
      (commitBlockRefs whole block suffix embedding refs).Agrees finalSource.state
        image.native.config.store ∧
      Registry.FailureExtension finalSource.registry (block.guardRegistry registry)
        finalSource.state := by
  let state := control.execution.application
  let image : PhaseRuntimeState ((toEventGraph whole).withMode mode) :=
    { state with current := state.current.inclusionResult message.payload native }
  have binding := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler trace
  have stored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler trace
  have relaxed := (toEventGraph whole).withMode_revealRelaxedOrdered
    (toEventGraph_barrierOrdered whole) mode
  have receipts := phaseReceiptRecord_history runtime leaks relaxed plan inputs horizon
    scheduler trace
  have imageReceipts : image.ReceiptRecord := receipts.inclusionResult runtime state message
    native authorized notExcluded handled relaxed
  have imageValid : image.current.native.BindingInvariant :=
    handle_bindingInvariant runtime _ native message binding.active handled
  have imageStored : image.StoredCheckpoint := by
    intro field value present
    exact handle_store_of_some runtime _ native message handled field value
      (stored field value present)
  exact sourceAttempt_of_drained_bindingPhase whole mode block suffix embedding compiled positive
    image installed imageValid imageReceipts imageStored entry agree guards finished

/-- A genuine permitted clock, chance or expiry result supplies the same exact
readback before phase normalization, including the public-omission branch. -/
theorem sourceAttempt_of_actual_bindingEnvironment
    (runtime : EventGraphRuntime ((toEventGraph whole).withMode mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph whole).withMode mode)))
    (plan : RuntimePhasePlan ((toEventGraph whole).withMode mode))
    (inputs : PMF ((toEventGraph whole).withMode mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (command : EnvironmentCommand ((toEventGraph whole).withMode mode))
    (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (authorized : control.execution.application.commandAllowed command = true)
    (reached : native ∈ (environmentStep runtime
      control.execution.application.current.native command).support)
    (installed : control.execution.application.phases.head? =
      some (compiledCommitPhase whole mode block suffix embedding compiled positive))
    (entry : SourceProgram.Config Player L Γ)
    (agree : refs.Agrees entry.state control.execution.application.entry.native.config.store)
    (guards : Registry.FailureExtension entry.registry registry entry.state)
    (finished :
      (compiledCommitPhase whole mode block suffix embedding compiled positive).Finished
        ((compiledCommitPhase whole mode block suffix embedding compiled positive).drain
          (control.execution.application.current.environmentResult command native))) :
    let phase := compiledCommitPhase whole mode block suffix embedding compiled positive
    let image := phase.drain
      (control.execution.application.current.environmentResult command native)
    ∃ finalSource : SourceProgram.Config Player L Δ,
      Nonempty (block.Attempt entry control.execution.application.entry.excluded finalSource
        image.excluded) ∧
      (commitBlockRefs whole block suffix embedding refs).Agrees finalSource.state
        image.native.config.store ∧
      Registry.FailureExtension finalSource.registry (block.guardRegistry registry)
        finalSource.state := by
  let state := control.execution.application
  let image : PhaseRuntimeState ((toEventGraph whole).withMode mode) :=
    { state with current := state.current.environmentResult command native }
  have binding := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler trace
  have stored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler trace
  have relaxed := (toEventGraph whole).withMode_revealRelaxedOrdered
    (toEventGraph_barrierOrdered whole) mode
  have receipts := phaseReceiptRecord_history runtime leaks relaxed plan inputs horizon
    scheduler trace
  have imageReceipts : image.ReceiptRecord := receipts.environmentResult runtime state command
    native authorized reached
  have imageValid : image.current.native.BindingInvariant :=
    environmentStep_bindingInvariant runtime _ native command binding.active reached
  have imageStored : image.StoredCheckpoint := by
    intro field value present
    exact environmentStep_store_of_some runtime _ native command reached field value
      (stored field value present)
  exact sourceAttempt_of_drained_bindingPhase whole mode block suffix embedding compiled positive
    image installed imageValid imageReceipts imageStored entry agree guards finished

end Vegas
