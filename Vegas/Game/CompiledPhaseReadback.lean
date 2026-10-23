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
      finalSource = (decodeCommitAttempt whole mode block suffix embedding
        (phase.drain state.current).native entry state.entry.excluded).1 ∧
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

end Vegas
