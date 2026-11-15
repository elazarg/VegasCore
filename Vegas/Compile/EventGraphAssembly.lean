module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.EventGraphCompiler
public import Vegas.EventGraph.DependencyRelaxation
public import Vegas.Source.Setup

@[expose] public section

/-! # Assembly of source-ranked event graphs

This module fixes the generic node lowerer to the combined initial/output
layout of one whole source program and carries typed references to terminal
payoff readout. The dataflow graph records exactly declared output reads. The
source information graph additionally retains the complete source rank, which
preserves publicly visible completion and default timing.
-/

noncomputable section

namespace Vegas

open SourceProgram

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- Combined graph field layout for one whole source program. -/
abbrev graphLayout {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) :=
  Vegas.EventGraph.fieldLayout (inputLayout Γ) (outputLayout program)

/-- Canonical reference to one source-ranked event output. -/
def outputRef {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (event : Fin (eventCount program)) :
    Vegas.EventGraph.FieldRef (graphLayout program) (outputLayout program event) where
  field := .inr event
  layout_eq := rfl

/-- Identity embedding of the whole program's source-ranked outputs. -/
def outputEmbedding {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) :
    OutputEmbedding (inputLayout Γ) (outputLayout program) program where
  event := id
  layout_eq _ := rfl
  strictMono := strictMono_id

@[simp] theorem outputEmbedding_ref {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames)
    (event : Fin (eventCount program)) :
    (outputEmbedding program).ref event = outputRef program event := by
  rfl

/-- Initial context references precede every source-ranked event. -/
theorem initialRefsBefore {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) :
    ContextRefsBefore (ContextRefs.initial Γ (outputLayout program))
      (outputEmbedding program) := by
  intro name cell source index
  trivial

/-- Lowered nodes paired with their constructed causal-read certificates. -/
def rankedNodes {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) :=
  compileRankedNodes program (ContextRefs.initial Γ (outputLayout program))
    (Revelations.initial Γ) [] (outputEmbedding program) (initialRefsBefore program)

/-- Executable node table obtained by projecting the jointly constructed
code-and-causality carrier. -/
def nodes {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) :
    ∀ event, Vegas.EventGraph.EventCode (graphLayout program) (outputLayout program event) :=
  fun event => (rankedNodes program event).code

/-- Carry typed source-cell references through the complete source program. -/
def terminalRefsWith {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L} :
    {Γ : SourceCtx Player L} → {openNames : Finset VarId} →
    (program : SourceProgram Player L Γ openNames) → ContextRefs layout Γ →
    (∀ event, Vegas.EventGraph.FieldRef layout (outputLayout program event)) →
      ContextRefs layout program.terminalCtx
  | _, _, .ret _, refs, _ => refs
  | _, _, .sample (payload := payload) _ _ _ next, refs, outputs =>
      let headRef : Vegas.EventGraph.FieldRef layout (.publicData payload) := by
        simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
      terminalRefsWith next (refs.cons headRef)
        (fun tailEvent => outputs (Fin.succ tailEvent))
  | _, _, .commit (payload := payload) _ owner _ _ next, refs, outputs =>
      let headRef : Vegas.EventGraph.FieldRef layout (.binding owner payload) := by
        simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
      terminalRefsWith next (refs.cons headRef)
        (fun tailEvent => outputs (Fin.succ tailEvent))
  | _, _, .reveal (payload := payload) _ _ _ _ _ _ next, refs, outputs =>
      let headRef : Vegas.EventGraph.FieldRef layout (.publication payload) := by
        simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
      terminalRefsWith next (refs.cons headRef)
        (fun tailEvent => outputs (Fin.succ tailEvent))

/-- Terminal source context represented in the fixed whole-program graph
layout. -/
def terminalRefs {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) :
    ContextRefs (graphLayout program) program.terminalCtx :=
  terminalRefsWith program (ContextRefs.initial Γ (outputLayout program))
    (outputRef program)

/-- Terminal payoff expressions lowered against the complete graph layout. -/
def payoffs {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) :
    List (Player × Vegas.EventGraph.PublicExpr (graphLayout program) L.int) :=
  program.terminalPayoffs.map fun payoff =>
    (payoff.1, compilePublicExpr (terminalRefs program) payoff.2)

/-- Compile source code to its declared dataflow dependencies. Initial input
reads need no predecessor; an output read depends directly on its producer.
Node code and its causal-read certificates come from one ranked recursion. -/
def toEventGraph {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) : Vegas.EventGraph Player L where
  inputCount := Γ.length
  order := {
    eventCount := eventCount program
    predecessors := fun event => Finset.univ.filter fun prior =>
      Sum.inr prior ∈ (nodes program event).readFields
    predecessor_lt := by
      intro event prior member
      have read := (Finset.mem_filter.mp member).2
      exact (rankedNodes program event).reads_before (.inr prior) read }
  inputLayout := inputLayout Γ
  outputLayout := outputLayout program
  nodes := nodes program
  reads_available := by
    intro event field member
    cases field with
    | inl => trivial
    | inr producer => exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, member⟩
  payoffs := payoffs program

/-- A compiled dataflow predecessor is exactly a declared output read. -/
@[simp] theorem toEventGraph_mem_predecessors {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames)
    (prior event : (toEventGraph program).EventId) :
    prior ∈ (toEventGraph program).order.predecessors event ↔
      Sum.inr prior ∈ (nodes program event).readFields := by
  simp [toEventGraph]

/-- The source information graph conservatively retains every earlier source
instruction, including the public completion and default metadata. -/
abbrev toInformationGraph {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) : Vegas.EventGraph Player L :=
  (toEventGraph program).sequentialize

/-- Every declared data dependency is retained by the source information order. -/
theorem toEventGraph_predecessors_subset_information {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames)
    (event : (toEventGraph program).EventId) :
    (toEventGraph program).order.predecessors event ⊆
      (toInformationGraph program).order.predecessors event := by
  intro prior member
  exact (EventOrder.sequential.mem_predecessors prior event).mpr
    ((toEventGraph program).order.predecessor_lt member)

/-- Every compiled action is a binding choice, a disclosure, or trivial, so
finite fresh-binding alphabets give finitely many actions at every event. -/
theorem outputLayout_action_finite : {Γ : SourceCtx Player L} → {openNames : Finset VarId} →
    (program : SourceProgram Player L Γ openNames) → program.FiniteBindingTypes →
    ∀ event, Finite (Vegas.EventGraph.EventField.Action (outputLayout program event))
  | _, _, .ret _, _, event => Fin.elim0 event
  | _, _, .sample _ _ _ next, finite, event => by
      refine Fin.cases ?_ (fun later => ?_) event
      · change Finite PUnit
        infer_instance
      · exact outputLayout_action_finite next finite later
  | _, _, .commit (payload := payload) _ _ _ _ next, finite, event => by
      refine Fin.cases ?_ (fun later => ?_) event
      · have := finite.1
        change Finite (Option (PublicationResult (L.Val payload)))
        infer_instance
      · exact outputLayout_action_finite next finite.2 later
  | _, _, .reveal _ _ _ _ _ _ next, finite, event => by
      refine Fin.cases ?_ (fun later => ?_) event
      · change Finite Bool
        infer_instance
      · exact outputLayout_action_finite next finite later

/-- The source information graph contains the public-barrier dependency policy. -/
theorem toInformationGraph_barrierOrdered {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames) :
    (toInformationGraph program).BarrierOrdered :=
  (toEventGraph program).sequentialize_barrierOrdered

/-- The source information order supplies the local strategic information certificate. -/
theorem toInformationGraph_informationDiscipline {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames) :
    (toInformationGraph program).InformationDiscipline
      (toInformationGraph program).prefixSchema :=
  (toInformationGraph_barrierOrdered program).informationDiscipline

/-- The setup-wide graph of exactly declared data dependencies. -/
abbrev _root_.Vegas.SourceProgram.Setup.dataflowGraph
    (source : Setup (Player := Player) (L := L)) : Vegas.EventGraph Player L :=
  toEventGraph source.program

/-- The setup-wide graph retaining the source information order. -/
abbrev _root_.Vegas.SourceProgram.Setup.informationGraph
    (source : Setup (Player := Player) (L := L)) : Vegas.EventGraph Player L :=
  toInformationGraph source.program

/-- The dependency choice retaining the complete source information order. -/
abbrev _root_.Vegas.SourceProgram.Setup.informationDependencies
    (source : Setup (Player := Player) (L := L)) : source.dataflowGraph.Dependencies :=
  source.dataflowGraph.sequentialDependencies

/-- The source information dependencies with independent reveal edges removed. -/
abbrev _root_.Vegas.SourceProgram.Setup.revealDependencies
    (source : Setup (Player := Player) (L := L)) : source.dataflowGraph.Dependencies :=
  source.dataflowGraph.revealDependencies source.informationDependencies

/-- Encode one setup state in the shared static graph input layout. -/
def _root_.Vegas.SourceProgram.Setup.eventInputs
    (source : Setup (Player := Player) (L := L))
    (state : State L source.context) : source.dataflowGraph.Inputs :=
  encodeInputs state

end Vegas

namespace Vegas.SourceProgram.Setup

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The source information graph retains every earlier instruction as a dependency. -/
theorem informationGraph_total (setup : Setup (Player := Player) (L := L))
    (prior event : setup.informationGraph.EventId) (earlier : prior.val < event.val) :
    prior ∈ setup.informationGraph.order.predecessors event :=
  (EventOrder.sequential.mem_predecessors prior event).mpr earlier

end Vegas.SourceProgram.Setup
