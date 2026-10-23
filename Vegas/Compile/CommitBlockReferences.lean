/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.CommitPhaseLayout
import Vegas.Compile.EventGraphState

/-! # Typed references after an embedded source commitment block -/

noncomputable section

namespace Vegas

open SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeOpen)

/-- Extend exactly the source cells produced by a compiled commitment telescope. -/
def commitBlockRefs : {Γ Δ : SourceCtx Player L} → {O P : Finset VarId} →
    (block : SourceProgram.CommitPrefix Γ O Δ P) →
    (suffix : SourceProgram Player L Δ P) →
    OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) (block.prepend suffix) →
    ContextRefs (graphLayout whole) Γ → ContextRefs (graphLayout whole) Δ
  | _, _, _, _, .nil, _suffix, _embedding, refs => refs
  | _, _, _, _, .commit name _owner _fresh _guard rest, suffix, embedding, refs =>
      let zero : Fin (eventCount ((SourceProgram.CommitPrefix.commit name _owner _fresh _guard
          rest).prepend suffix)) := ⟨0, by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]
        omega⟩
      let laterEmbedding := embedding.tail (rest.prepend suffix) (by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      commitBlockRefs rest suffix laterEmbedding
        (refs.cons (name := name) (cell := .commitment _owner _)
          ⟨.inr (embedding.event zero), by
            simpa only [zero, SourceProgram.CommitPrefix.prepend, outputLayout,
              graphLayout, EventGraph.fieldLayout, cellField, Fin.mk_zero, Fin.cases_zero,
              Sum.elim_inr] using
              embedding.layout_eq zero⟩)

end Vegas
