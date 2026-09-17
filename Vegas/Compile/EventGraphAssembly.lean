/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphCompiler
import Vegas.EventGraph.BarrierInformation
import Vegas.Source.Setup

/-! # Assembly of source-ranked event graphs

This module fixes the generic node lowerer to the combined initial/output
layout of one whole source program and carries typed references to terminal
payoff readout.
-/

noncomputable section

namespace Vegas.SourceProgram.EventLowering

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
    (program : SourceProgram Player L Γ openNames)
    (unique : (Γ.map Prod.fst).Nodup) :=
  compileRankedNodes program unique (ContextRefs.initial Γ (outputLayout program))
    (Revelations.initial Γ) [] (outputEmbedding program) (initialRefsBefore program)

/-- Executable node table obtained by projecting the jointly constructed
code-and-causality carrier. -/
def nodes {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (unique : (Γ.map Prod.fst).Nodup) :
    ∀ event, Vegas.EventGraph.EventCode (graphLayout program) (outputLayout program event) :=
  fun event => (rankedNodes program unique event).code

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

omit [DecidableEq Player] in
/-- A node with a nonempty read footprint is necessarily public. Binding
nodes are the only private outputs and read no graph fields. -/
private theorem code_isPublic_of_mem_readFields {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {output : Vegas.EventGraph.EventField Player L}
    (code : Vegas.EventGraph.EventCode layout output) {field : Field}
    (member : field ∈ code.readFields) : output.IsPublic := by
  cases code with
  | bind => simp [Vegas.EventGraph.EventCode.readFields] at member
  | resolve | sample => trivial

/-- Compile the complete source language to an executable dependency-driven
event graph. Node code and `reads_available` come from one ranked recursion. -/
def toEventGraph {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (unique : (Γ.map Prod.fst).Nodup) : Vegas.EventGraph Player L where
  inputCount := Γ.length
  order := Vegas.EventGraph.barrierOrder (outputLayout program)
  inputLayout := inputLayout Γ
  outputLayout := outputLayout program
  nodes := nodes program unique
  reads_available := by
    intro event field member
    change field ∈ (rankedNodes program unique event).code.readFields at member
    have before := (rankedNodes program unique event).reads_before field member
    cases field with
    | inl => trivial
    | inr producer =>
        exact Vegas.EventGraph.barrierOrder_public_event (outputLayout program)
          before (code_isPublic_of_mem_readFields _ member)
  payoffs := payoffs program

/-- The compiled graph contains the public-barrier dependency policy. -/
theorem toEventGraph_barrierOrdered {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames)
    (unique : (Γ.map Prod.fst).Nodup) :
    (toEventGraph program unique).BarrierOrdered := by
  intro event
  exact Finset.Subset.rfl

/-- Full source lowering immediately inherits the generic local information
certificate for every ready strategic cut. -/
theorem toEventGraph_informationDiscipline {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames)
    (unique : (Γ.map Prod.fst).Nodup) :
    (toEventGraph program unique).InformationDiscipline
      (toEventGraph program unique).prefixSchema :=
  (toEventGraph_barrierOrdered program unique).informationDiscipline

/-- Entry point for a source program with one concrete initial state. -/
def _root_.Vegas.SourceProgram.Initial.eventGraph
    (source : Initial (Player := Player) (L := L)) : Vegas.EventGraph Player L :=
  toEventGraph source.program source.namesNodup

/-- Encode the concrete initial state separately from its compiled graph. -/
def _root_.Vegas.SourceProgram.Initial.eventInputs
    (source : Initial (Player := Player) (L := L)) : source.eventGraph.Inputs :=
  encodeInputs source.state

/-- Entry point shared by every state in a distributed initial setup law. -/
def _root_.Vegas.SourceProgram.Setup.eventGraph
    (source : Setup (Player := Player) (L := L)) : Vegas.EventGraph Player L :=
  toEventGraph source.program source.namesNodup

/-- Encode one setup state for the single setup-wide compiled graph. -/
def _root_.Vegas.SourceProgram.Setup.eventInputs
    (source : Setup (Player := Player) (L := L))
    (state : State L source.context) : source.eventGraph.Inputs :=
  encodeInputs state

end Vegas.SourceProgram.EventLowering
