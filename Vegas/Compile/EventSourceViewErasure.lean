/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.EventSourceView
import Vegas.Source.CommitRecoveryErasure

/-! # Source typed current views without reconstructed private words -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The current compiler decoder needs no remembered private word when its
consumer keeps only the typed current view. This is the same original decoder. -/
theorem decodeEventView?_eraseHistory {Field : Type} {layout : Field → EventField Player L} :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (refs : ContextRefs layout Γ)
      (outputs : ∀ event, FieldRef layout (outputLayout program event)) (who : Player)
      (event : Fin (eventCount program)) (store : Store layout) (past : List (OwnAction Player L)),
      decodeEventView? program refs outputs who event store [] =
        (decodeEventView? program refs outputs who event store past).map
          (ProtocolView.eraseHistory who program) := by
  intro Γ O program
  induction program with
  | ret => intro refs outputs who event; exact Fin.elim0 event
  | sample name fresh law next ih =>
      intro refs outputs who event store past
      refine Fin.cases ?_ ?_ event
      · simp only [decodeEventView?, Fin.cases_zero, Option.map_map, Function.comp_def,
          ProtocolView.eraseHistory, Sum.elim_inl]
      · intro later
        simp only [decodeEventView?, Fin.cases_succ]
        rw [ih _ _ who later store past]
        simp only [Option.map_map, Function.comp_def, ProtocolView.eraseHistory, Sum.elim_inr]
  | commit name owner fresh guard next ih =>
      intro refs outputs who event store past
      refine Fin.cases ?_ ?_ event
      · simp only [decodeEventView?, Fin.cases_zero, Option.map_map, Function.comp_def,
          ProtocolView.eraseHistory, Sum.elim_inl]
      · intro later
        simp only [decodeEventView?, Fin.cases_succ]
        rw [ih _ _ who later store past]
        simp only [Option.map_map, Function.comp_def, ProtocolView.eraseHistory, Sum.elim_inr]
  | reveal published owner name fresh source unresolved next ih =>
      intro refs outputs who event store past
      refine Fin.cases ?_ ?_ event
      · simp only [decodeEventView?, Fin.cases_zero, Option.map_map, Function.comp_def,
          ProtocolView.eraseHistory, Sum.elim_inl]
      · intro later
        simp only [decodeEventView?, Fin.cases_succ]
        rw [ih _ _ who later store past]
        simp only [Option.map_map, Function.comp_def, ProtocolView.eraseHistory, Sum.elim_inr]

end Vegas
