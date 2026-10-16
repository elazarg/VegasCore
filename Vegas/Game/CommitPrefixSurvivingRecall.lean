/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.ExcludedCommitPrefixObservation
import Vegas.Game.CommitPrefixReadyRecall

/-! # Surviving source own words relative to a physical saved checkpoint -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeO) (mode : EventGraph.ExecutionMode)

/-- Readiness identifies the newly executed own actions while retaining an
arbitrary saved source own word. No equality between saved source history and
rolled-back native history is required. -/
theorem fillCommitPrefix_history_extension_of_ready
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (offset : Nat)
    (rank : ∀ index, (embedding.event index).val = offset + index.val)
    (entryNative native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (entry : SourceProgram.Config Player L Γ) (valid : native.BindingInvariant) {inputs}
    (reachable : native.config.Reachable inputs)
    (retained : entryNative.config.history.IsPrefix native.config.history)
    (saved : entryNative.config.cut.IsPrefix offset) (who : Player)
    (actions : ∀ index action, decodeEventAction whole (embedding.event index) action =
      decodeEventAction (block.prepend suffix) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    (selected : Fin (eventCount (block.prepend suffix))) (atEnd : selected.val = block.length)
    (ready : native.config.cut.Ready (embedding.event selected))
    (acting : ((toEventGraph whole).withMode mode).actor? (embedding.event selected) = some who) :
    (fillCommitPrefix whole block suffix embedding native.config.store entry).history who =
      entry.history who ++
        (decodeHistory whole (native.config.history.map
          ((toEventGraph whole).fromModeCompletion mode)) who).drop
          (decodeHistory whole (entryNative.config.history.map
            ((toEventGraph whole).fromModeCompletion mode)) who).length := by
  let nativeWord := decodeHistory whole (entryNative.config.history.map
    ((toEventGraph whole).fromModeCompletion mode))
  let recorded : SourceProgram.Config Player L Γ := { entry with history := nativeWord }
  let emptyWord : SourceProgram.Config Player L Γ := { entry with history := fun _ => [] }
  have current := fillCommitPrefix_history_of_ready whole mode block suffix embedding offset rank
    entryNative native recorded valid reachable retained saved who rfl actions selected atEnd ready
      acting
  have original := fillCommitPrefix_history_prefix whole block suffix embedding native.config.store
    entry emptyWord who (entry.history who) (by simp only [emptyWord, List.append_nil])
  have physical := fillCommitPrefix_history_prefix whole block suffix embedding native.config.store
    recorded emptyWord who (nativeWord who) (by
      simp only [recorded, emptyWord, List.append_nil])
  change (fillCommitPrefix whole block suffix embedding native.config.store recorded).history who =
    _ at current
  have suffixWord : (decodeHistory whole (native.config.history.map
      ((toEventGraph whole).fromModeCompletion mode)) who).drop (nativeWord who).length =
      (fillCommitPrefix whole block suffix embedding native.config.store emptyWord).history who :=
        by
    rw [← current, physical]
    simp
  rw [original]
  exact congrArg (List.append (entry.history who)) suffixWord.symm

end Vegas
