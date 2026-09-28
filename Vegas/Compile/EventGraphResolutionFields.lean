/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphAssembly
import Vegas.EventGraph.ResolutionFields

/-! # A compiled commitment has at most one resolution event

Source publication accounting consumes each commitment name once. The lowerer
retains that discipline as a property of graph fields, independently of any
runtime representation of commitment handles or certificates.
-/

noncomputable section

namespace Vegas

open SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

def resolutionName? : {Γ : SourceCtx Player L} → {openNames : Finset VarId} →
    (program : SourceProgram Player L Γ openNames) → Fin (eventCount program) → Option VarId
  | _, _, .ret _, event => Fin.elim0 event
  | _, _, .sample _ _ _ next, event => Fin.cases none (resolutionName? next) event
  | _, _, .commit _ _ _ _ next, event => Fin.cases none (resolutionName? next) event
  | _, _, .reveal _ _ name _ _ _ next, event =>
      Fin.cases (some name) (resolutionName? next) event

theorem resolutionName_available {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (event : Fin (eventCount program))
    (name : VarId) (resolved : resolutionName? program event = some name)
    (inScope : name ∈ Γ.map Prod.fst) : name ∈ openNames := by
  induction program with
  | ret => exact Fin.elim0 event
  | sample introduced fresh law next ih =>
      cases event using Fin.cases with
      | zero => cases resolved
      | succ index => exact ih index resolved (List.mem_cons_of_mem _ inScope)
  | commit introduced owner fresh guard next ih =>
      cases event using Fin.cases with
      | zero => cases resolved
      | succ index =>
          have available := ih index resolved (List.mem_cons_of_mem _ inScope)
          rcases Finset.mem_insert.mp available with same | earlier
          · exact False.elim (fresh (same ▸ inScope))
          · exact earlier
  | reveal published owner selected fresh source unresolved next ih =>
      cases event using Fin.cases with
      | zero =>
          have same : selected = name := Option.some.inj resolved
          exact same ▸ unresolved
      | succ index =>
          exact Finset.mem_of_mem_erase (ih index resolved (List.mem_cons_of_mem _ inScope))

/-- Equality of resolved source names identifies the event itself. -/
theorem resolutionName_injective {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (left right : Fin (eventCount program))
    (name : VarId) (first : resolutionName? program left = some name)
    (second : resolutionName? program right = some name) : left = right := by
  induction program with
  | ret => exact Fin.elim0 left
  | sample introduced fresh law next ih =>
      cases left using Fin.cases with
      | zero => cases first
      | succ left =>
          cases right using Fin.cases with
          | zero => cases second
          | succ right => exact congrArg Fin.succ (ih left right first second)
  | commit introduced owner fresh guard next ih =>
      cases left using Fin.cases with
      | zero => cases first
      | succ left =>
          cases right using Fin.cases with
          | zero => cases second
          | succ right => exact congrArg Fin.succ (ih left right first second)
  | reveal published owner selected fresh source unresolved next ih =>
      have absent (event : Fin (eventCount next)) : resolutionName? next event ≠ some selected := by
        intro resolved
        have impossible := resolutionName_available next event selected resolved
          (List.mem_cons_of_mem _ source.mem_map_fst)
        exact (Finset.mem_erase.mp impossible).1 rfl
      cases left using Fin.cases with
      | zero =>
          have same : selected = name := Option.some.inj first
          cases right using Fin.cases with
          | zero => rfl
          | succ right =>
              exact False.elim (absent right (second.trans (congrArg some same.symm)))
      | succ left =>
          cases right using Fin.cases with
          | zero =>
              have same : selected = name := Option.some.inj second
              exact False.elim (absent left (first.trans (congrArg some same.symm)))
          | succ right => exact congrArg Fin.succ (ih left right first second)

def inputName : (Γ : SourceCtx Player L) → Fin Γ.length → VarId
  | [], index => Fin.elim0 index
  | (name, _) :: Γ, index => Fin.cases name (inputName Γ) index

omit [DecidableEq Player] [IExpr.ResultTypes L] in
@[simp] theorem inputName_inputId {Γ : SourceCtx Player L} {name : VarId}
    {cell : CellTy Player L} (source : HasVar Γ name cell) :
    inputName Γ (inputId source) = name := by
  induction source with
  | here => rfl
  | there source ih => exact ih

def outputName : {Γ : SourceCtx Player L} → {openNames : Finset VarId} →
    (program : SourceProgram Player L Γ openNames) → Fin (eventCount program) → VarId
  | _, _, .ret _, event => Fin.elim0 event
  | _, _, .sample name _ _ next, event => Fin.cases name (outputName next) event
  | _, _, .commit name _ _ _ next, event => Fin.cases name (outputName next) event
  | _, _, .reveal published _ _ _ _ _ next, event =>
      Fin.cases published (outputName next) event

theorem compileRankedNodes_resolution_name {inputCount totalCount : Nat}
    {inputs : Fin inputCount → Vegas.EventGraph.EventField Player L}
    {outputs : Fin totalCount → Vegas.EventGraph.EventField Player L}
    (nameOf : Fin inputCount ⊕ Fin totalCount → VarId) :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames)
      (refs : ContextRefs (Vegas.EventGraph.fieldLayout inputs outputs) Γ)
      (revelations : Revelations Γ) (registry : Registry Γ)
      (embedding : OutputEmbedding inputs outputs program)
      (refsBefore : ContextRefsBefore refs embedding),
      (∀ {name cell} (source : HasVar Γ name cell), nameOf (refs.get source).field = name) →
      (∀ index, nameOf (.inr (embedding.event index)) = outputName program index) →
      ∀ index, ((compileRankedNodes program refs revelations registry embedding refsBefore
        index).code.resolutionField?).map nameOf = resolutionName? program index := by
  intro Γ openNames program
  induction program with
  | ret => intro _ _ _ _ _ _ _ index; exact Fin.elim0 index
  | sample name fresh law next ih =>
      intro refs revelations registry embedding before named outputsNamed index
      cases index using Fin.cases with
      | zero => rfl
      | succ index =>
          apply ih
          · intro readName cell source
            cases source with
            | here => exact outputsNamed ⟨0, Nat.zero_lt_succ _⟩
            | there source => exact named source
          · intro remaining
            exact outputsNamed (Fin.succ remaining)
  | commit name owner fresh guard next ih =>
      intro refs revelations registry embedding before named outputsNamed index
      cases index using Fin.cases with
      | zero => rfl
      | succ index =>
          apply ih
          · intro readName cell source
            cases source with
            | here => exact outputsNamed ⟨0, Nat.zero_lt_succ _⟩
            | there source => exact named source
          · intro remaining
            exact outputsNamed (Fin.succ remaining)
  | reveal published owner name fresh selected unresolved next ih =>
      intro refs revelations registry embedding before named outputsNamed index
      cases index using Fin.cases with
      | zero => exact congrArg some (named selected)
      | succ index =>
          apply ih
          · intro readName cell source
            cases source with
            | here => exact outputsNamed ⟨0, Nat.zero_lt_succ _⟩
            | there source => exact named source
          · intro remaining
            exact outputsNamed (Fin.succ remaining)

def fieldName {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) :
    Fin Γ.length ⊕ Fin (eventCount program) → VarId :=
  Sum.elim (inputName Γ) (outputName program)

theorem nodes_resolution_name {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (event : Fin (eventCount program)) :
    (((toEventGraph program).nodes event).resolutionField?).map (fieldName program) =
      resolutionName? program event := by
  apply compileRankedNodes_resolution_name
  · intro name cell source
    exact inputName_inputId source
  · intro index
    rfl

/-- Two compiled resolution nodes cannot consume the same commitment field.
This holds for the full source language, including guards and fresh bindings. -/
theorem resolution_field_injective {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (left right : Fin (eventCount program))
    (field : (toEventGraph program).Field)
    (first : ((toEventGraph program).nodes left).resolutionField? = some field)
    (second : ((toEventGraph program).nodes right).resolutionField? = some field) :
    left = right := by
  apply resolutionName_injective program left right (fieldName program field)
  · rw [← nodes_resolution_name, first]
    rfl
  · rw [← nodes_resolution_name, second]
    rfl

end Vegas
