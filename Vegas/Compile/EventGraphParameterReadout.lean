/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.EventGraphReadoutComplete
import Vegas.Source.InitialState
import Vegas.Source.ValueBinding

/-! # Context agreement of decoded graph states

A source state decoded from a store agrees with that store
(`Vegas.decodeState?_agrees`), and agreement through the terminal references
restricts to the initial source environment
(`Vegas.terminalRefsWith_initial_agrees`).
-/

noncomputable section

namespace Vegas

open SourceProgram

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem decodeState?_agrees {Field : Type}
    {layout : Field → EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ)
    (store : EventGraph.Store layout) (source : State L Γ)
    (decoded : decodeState? refs store = some source) : refs.Agrees source store := by
  induction Γ with
  | nil => intro name cell ref; nomatch ref
  | cons entry Γ ih =>
      obtain ⟨name, cell⟩ := entry
      cases cell <;>
        cases head : (refs.get HasVar.here).get? store <;>
        cases tail : decodeState? refs.tail store <;>
        simp only [decodeState?, head, tail, bind, Option.bind, pure,
          Option.some.injEq, reduceCtorEq] at decoded
      all_goals
        subst source
        intro readName readCell ref
        cases ref with
        | here => exact head
        | there prior => exact ih refs.tail _ tail prior

theorem terminalRefsWith_initial_agrees {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (refs : ContextRefs layout Γ)
    (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
    (store : EventGraph.Store layout) (source : State L program.terminalCtx)
    (agree : (terminalRefsWith program refs outputs).Agrees source store) :
    refs.Agrees (initialState program source) store := by
  induction program with
  | ret payoffs => exact agree
  | sample _ _ _ _ ih | commit _ _ _ _ _ ih | reveal _ _ _ _ _ _ _ ih =>
      intro name cell ref
      exact ih _ _ source agree (.there ref)

end Vegas
