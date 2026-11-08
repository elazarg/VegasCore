/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.EventGraphAssembly
import Vegas.Compile.EventGraphPolicy
import Vegas.EventGraph.DefaultFailure

/-! # Every compiled binding is revealed

A source program returns only once every commitment it opened has been
revealed, and a reveal reads the binding of the commitment it names. So every
binding event of a compiled graph is read by a later reveal event of the same
owner.
-/

noncomputable section

namespace Vegas

open Vegas.EventGraph SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [R : IExpr.ResultTypes L]

/-- A name bound once in a context: any two lookups of it agree. -/
def BoundOnce {Ty : Type} (Γ : Ctx Ty) (name : VarId) : Prop :=
  ∀ {first second : Ty} (left : HasVar Γ name first) (right : HasVar Γ name second),
    first = second ∧ HEq left right

theorem HasVar.mem_names {Ty : Type} {Γ : Ctx Ty} {name : VarId} {cell : Ty}
    (source : HasVar Γ name cell) : name ∈ Γ.map Prod.fst := by
  induction source with
  | here => exact List.mem_cons_self
  | there _ ih => exact List.mem_cons_of_mem _ ih

theorem BoundOnce.here {Ty : Type} {Γ : Ctx Ty} {name : VarId} {cell : Ty}
    (fresh : name ∉ Γ.map Prod.fst) : BoundOnce ((name, cell) :: Γ) name := by
  intro first second left right
  cases left with
  | here =>
      cases right with
      | here => exact ⟨rfl, HEq.rfl⟩
      | there source => exact absurd source.mem_names fresh
  | there source => exact absurd source.mem_names fresh

theorem BoundOnce.cons {Ty : Type} {Γ : Ctx Ty} {name other : VarId} {cell : Ty}
    (once : BoundOnce Γ name) (different : other ≠ name) :
    BoundOnce ((other, cell) :: Γ) name := by
  intro first second left right
  cases left with
  | here => exact absurd rfl different
  | there leftSource =>
      cases right with
      | here => exact absurd rfl different
      | there rightSource =>
          obtain ⟨same, sameSource⟩ := once leftSource rightSource
          subst same
          exact ⟨rfl, by rw [eq_of_heq sameSource]⟩

/-- An open commitment bound once is read by a later reveal of its owner. -/
theorem compileRankedNodes_reveals {inputCount totalCount : Nat}
    {inputs : Fin inputCount → EventField Player L}
    {outputs : Fin totalCount → EventField Player L} :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames)
      (refs : ContextRefs (fieldLayout inputs outputs) Γ) (revelations : Revelations Γ)
      (registry : Registry Γ) (embedding : OutputEmbedding inputs outputs program)
      (before : ContextRefsBefore refs embedding) {name : VarId} {owner : Player}
      {payload : L.Ty} (cell : HasVar Γ name (.commitment owner payload)),
      name ∈ openNames → BoundOnce Γ name →
      ∃ index, eventOwner? program index = some owner ∧
        (outputLayout program index).IsPublication ∧
        (refs.get cell).field ∈
          (compileRankedNodes program refs revelations registry embedding before
            index).code.readFields
  | _, _, .ret _, _, _, _, _, _, _, _, _, _, opened, _ => absurd opened (Finset.notMem_empty _)
  | _, _, .sample newName fresh _ next, _, _, _, _, _, name, _, _, cell, opened, once => by
      have different : newName ≠ name := fun same => fresh (by rw [same]; exact cell.mem_names)
      obtain ⟨index, owned, publication, read⟩ := compileRankedNodes_reveals next _ _ _ _ _
        (.there cell) opened (once.cons different)
      exact ⟨index.succ, owned, publication, read⟩
  | _, _, .commit newName _ fresh _ next, _, _, _, _, _, name, _, _, cell, opened, once => by
      have different : newName ≠ name := fun same => fresh (by rw [same]; exact cell.mem_names)
      obtain ⟨index, owned, publication, read⟩ := compileRankedNodes_reveals next _ _ _ _ _
        (.there cell) (Finset.mem_insert_of_mem opened) (once.cons different)
      exact ⟨index.succ, owned, publication, read⟩
  | _, _, .reveal published revealOwner revealName fresh selected _ next, refs, _, _, _, _,
      name, _, _, cell, opened, once => by
      by_cases same : revealName = name
      · subst same
        obtain ⟨cells, sameCell⟩ := once selected cell
        obtain ⟨rfl, rfl⟩ := CellTy.commitment.inj cells
        obtain rfl := eq_of_heq sameCell
        exact ⟨⟨0, Nat.zero_lt_succ _⟩, rfl, trivial, Finset.mem_insert_self _ _⟩
      · have different : published ≠ name := fun same => fresh (by rw [same]; exact cell.mem_names)
        obtain ⟨index, owned, publication, read⟩ := compileRankedNodes_reveals next _ _ _ _ _
          (.there cell) (Finset.mem_erase.mpr ⟨Ne.symm same, opened⟩) (once.cons different)
        exact ⟨index.succ, owned, publication, read⟩

/-- Every binding event is read by a later reveal of its owner. -/
theorem compileRankedNodes_binding_revealed {inputCount totalCount : Nat}
    {inputs : Fin inputCount → EventField Player L}
    {outputs : Fin totalCount → EventField Player L} :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames)
      (refs : ContextRefs (fieldLayout inputs outputs) Γ) (revelations : Revelations Γ)
      (registry : Registry Γ) (embedding : OutputEmbedding inputs outputs program)
      (before : ContextRefsBefore refs embedding) (event : Fin (eventCount program))
      {owner : Player} {payload : L.Ty},
      outputLayout program event = .binding owner payload →
      ∃ index, eventOwner? program index = some owner ∧
        (outputLayout program index).IsPublication ∧
        (embedding.ref event).field ∈
          (compileRankedNodes program refs revelations registry embedding before
            index).code.readFields
  | _, _, .ret _, _, _, _, _, _, event, _, _, _ => nomatch event
  | _, _, .sample _ _ _ next, _, _, _, _, _, event, _, _, binding => by
      cases event using Fin.cases with
      | zero => exact absurd binding (by simp [outputLayout])
      | succ tail =>
          obtain ⟨index, owned, publication, read⟩ :=
            compileRankedNodes_binding_revealed next _ _ _ _ _ tail binding
          exact ⟨index.succ, owned, publication, read⟩
  | _, _, .commit _ _ fresh _ next, _, _, _, _, _, event, _, _, binding => by
      cases event using Fin.cases with
      | zero =>
          obtain ⟨rfl, rfl⟩ := EventField.binding.inj binding
          obtain ⟨index, owned, publication, read⟩ := compileRankedNodes_reveals next _ _ _ _ _
            HasVar.here (Finset.mem_insert_self _ _) (BoundOnce.here fresh)
          exact ⟨index.succ, owned, publication, read⟩
      | succ tail =>
          obtain ⟨index, owned, publication, read⟩ :=
            compileRankedNodes_binding_revealed next _ _ _ _ _ tail binding
          exact ⟨index.succ, owned, publication, read⟩
  | _, _, .reveal _ _ _ _ _ _ next, _, _, _, _, _, event, _, _, binding => by
      cases event using Fin.cases with
      | zero => exact absurd binding (by simp [outputLayout])
      | succ tail =>
          obtain ⟨index, owned, publication, read⟩ :=
            compileRankedNodes_binding_revealed next _ _ _ _ _ tail binding
          exact ⟨index.succ, owned, publication, read⟩

/-- **Compiled bindings are revealed.** -/
theorem toEventGraph_bindingsRevealed {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) :
    (toEventGraph program).BindingsRevealed := by
  intro event owner payload binding
  obtain ⟨index, owned, publication, read⟩ := compileRankedNodes_binding_revealed program
    (ContextRefs.initial Γ (outputLayout program)) (Revelations.initial Γ) []
    (outputEmbedding program) (initialRefsBefore program) event binding
  exact ⟨index, (eventOwner?_eq_actor program index).symm.trans owned, publication, read⟩

end Vegas
