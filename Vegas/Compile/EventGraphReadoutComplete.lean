/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphReadout
import Vegas.EventGraph.Sequential

/-! # Successful terminal decoding implies completed source events

Every source instruction introduces a cell retained in the terminal context.
The terminal decoder therefore needs every compiled event output. Structural
graph configurations already equate output availability with completed events,
so successful decoding proves completion without an execution-policy premise.
-/

noncomputable section

namespace Vegas

open SourceProgram

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem decodeState?_available {Field : Type}
    {layout : Field → EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ)
    (store : EventGraph.Store layout) (decoded : (decodeState? refs store).isSome = true)
    {name : VarId} {cell : CellTy Player L} (ref : HasVar Γ name cell) :
    (store (refs.get ref).field).isSome = true := by
  have availability {kind : EventGraph.EventField Player L}
      (selected : EventGraph.FieldRef layout kind)
      (present : (selected.get? store).isSome = true) :
      (store selected.field).isSome = true := by
    cases selected with
    | mk field same => cases same; exact present
  induction Γ with
  | nil => nomatch ref
  | cons entry Γ ih =>
      obtain ⟨headName, headCell⟩ := entry
      have headPresent : ((refs.get (HasVar.here :
          HasVar ((headName, headCell) :: Γ) headName headCell)).get? store).isSome = true := by
        cases headCell <;>
          cases head : (refs.get HasVar.here).get? store <;>
          simp_all only [decodeState?, bind, Option.bind, Option.isSome_none,
            Bool.false_eq_true, Option.isSome_some]
      have tailPresent : (decodeState? refs.tail store).isSome = true := by
        cases headCell <;>
          cases head : (refs.get HasVar.here).get? store <;>
          cases tail : decodeState? refs.tail store <;>
          simp_all only [decodeState?, bind, Option.bind,
            Option.isSome_none, Bool.false_eq_true, Option.isSome_some, pure]
      cases ref with
      | here => exact availability _ headPresent
      | there earlier => exact ih refs.tail tailPresent earlier

theorem terminalRefsWith_available_context {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (refs : ContextRefs layout Γ)
    (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
    (store : EventGraph.Store layout)
    (decoded : (decodeState? (terminalRefsWith program refs outputs) store).isSome = true)
    {name : VarId} {cell : CellTy Player L} (ref : HasVar Γ name cell) :
    (store (refs.get ref).field).isSome = true := by
  induction program with
  | ret payoffs => exact decodeState?_available refs store decoded ref
  | sample _ _ _ _ ih | commit _ _ _ _ _ ih | reveal _ _ _ _ _ _ _ ih =>
      exact ih _ _ decoded (.there ref)

theorem terminalRefsWith_available_outputs {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (refs : ContextRefs layout Γ)
    (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
    (store : EventGraph.Store layout)
    (decoded : (decodeState? (terminalRefsWith program refs outputs) store).isSome = true)
    (event : Fin (eventCount program)) :
    (store (outputs event).field).isSome = true := by
  induction program with
  | ret payoffs => nomatch event
  | sample _ _ _ next ih | commit _ _ _ _ next ih | reveal _ _ _ _ _ _ next ih =>
      refine Fin.cases ?_ (fun tail => ?_) event
      · exact terminalRefsWith_available_context next _ _ store decoded HasVar.here
      · exact ih _ _ decoded tail

/-- This implication is independent of the graph dependency mode and the
policy that produced the configuration. -/
theorem terminal_decode_complete {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (mode : EventGraph.ExecutionMode)
    (config : ((toEventGraph program).withMode mode).Config)
    (decoded : (decodeState? (terminalRefs program) config.store).isSome = true) :
    config.cut.Terminal := by
  apply Finset.eq_univ_of_forall
  intro event
  apply (config.output_available event).mp
  exact terminalRefsWith_available_outputs program _ _ config.store decoded event

end Vegas
