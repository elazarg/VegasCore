/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphReadoutComplete
import Vegas.Source.InitialState
import Vegas.Source.ValueBinding

/-! # Initial parameters and public results of decoded graph states

Full typed decoding retains hidden future bindings. Analysis readout instead
uses the initial source environment and public terminal cells. Equal graph
inputs and public stores suffice for equality of that joint readout, even when
private binding outputs differ.
-/

noncomputable section

namespace Vegas.SourceProgram.EventLowering

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

omit [DecidableEq Player] in
theorem ContextRefs.Agrees.public_eq {graph : Vegas.EventGraph Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs graph.layout Γ)
    (left right : State L Γ) (leftStore rightStore : EventGraph.Store graph.layout)
    (first : refs.Agrees left leftStore) (second : refs.Agrees right rightStore)
    (publicEq : graph.publicStore leftStore = graph.publicStore rightStore) :
    sourcePublicEnv left = sourcePublicEnv right := by
  have equal {name : VarId} {cell : CellTy Player L} (ref : HasVar Γ name cell)
      (visible : (cellField cell).IsPublic) :
      cellValue (left.get ref) = cellValue (right.get ref) := by
    apply Option.some.inj
    rw [← first ref, ← second ref]
    apply (refs.get ref).get?_congr
    have isPublic : graph.fieldPublic (refs.get ref).field := by
      change (graph.layout (refs.get ref).field).IsPublic
      rw [(refs.get ref).layout_eq]
      exact visible
    exact (graph.publicStore_of_public leftStore _ isPublic).symm.trans
      ((congrFun publicEq _).trans (graph.publicStore_of_public rightStore _ isPublic))
  exact sourcePublicEnv_congr left right (fun ref => equal ref trivial)
    (fun ref => equal ref trivial)

theorem terminal_initialState_eq {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (mode : EventGraph.ExecutionMode)
    (left right : ((toEventGraph program).withMode mode).Config)
    (leftSource rightSource : State L program.terminalCtx)
    (first : (terminalRefs program).Agrees leftSource left.store)
    (second : (terminalRefs program).Agrees rightSource right.store)
    (inputs : left.inputs = right.inputs) :
    initialState program leftSource = initialState program rightSource := by
  have firstInitial : (ContextRefs.initial Γ (outputLayout program)).Agrees
      (initialState program leftSource) left.store :=
    terminalRefsWith_initial_agrees program _ _ _ leftSource first
  have secondInitial : (ContextRefs.initial Γ (outputLayout program)).Agrees
      (initialState program rightSource) right.store :=
    terminalRefsWith_initial_agrees program _ _ _ rightSource second
  funext name cell ref
  have fieldEq : ((ContextRefs.initial Γ (outputLayout program)).get ref).get? left.store =
      ((ContextRefs.initial Γ (outputLayout program)).get ref).get? right.store := by
    apply EventGraph.FieldRef.get?_congr
    change some (left.inputs (inputId ref)) = some (right.inputs (inputId ref))
    rw [inputs]
  rw [firstInitial ref, secondInitial ref] at fieldEq
  have same := Option.some.inj fieldEq
  cases cell <;> exact same

/-- The analysis parameter is chosen before play and may read the complete
initial private environment. Future hidden binding values are excluded. -/
theorem decoded_parameterOutcome_eq {Parameter : Type}
    (setup : Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter) (mode : EventGraph.ExecutionMode)
    (left right : (setup.eventGraph.withMode mode).Config)
    (leftSource rightSource : State L setup.program.terminalCtx)
    (first : decodeState? (terminalRefs setup.program) left.store = some leftSource)
    (second : decodeState? (terminalRefs setup.program) right.store = some rightSource)
    (inputs : left.inputs = right.inputs)
    (publicEq : (setup.eventGraph.withMode mode).publicStore left.store =
      (setup.eventGraph.withMode mode).publicStore right.store) :
    setup.parameterOutcome parameter leftSource = setup.parameterOutcome parameter rightSource := by
  have firstAgree : (terminalRefs setup.program).Agrees leftSource left.store :=
    decodeState?_agrees _ _ _ first
  have secondAgree : (terminalRefs setup.program).Agrees rightSource right.store :=
    decodeState?_agrees _ _ _ second
  apply Prod.ext
  · exact congrArg parameter
      (terminal_initialState_eq setup.program mode left right leftSource rightSource
        firstAgree secondAgree inputs)
  · exact ContextRefs.Agrees.public_eq (graph := setup.eventGraph.withMode mode)
      (terminalRefs setup.program)
      leftSource rightSource left.store right.store firstAgree secondAgree publicEq

end Vegas.SourceProgram.EventLowering
