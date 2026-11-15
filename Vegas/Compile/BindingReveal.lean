module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.EventGraphAssembly
public import Vegas.Compile.EventGraphPolicy
public import Vegas.EventGraph.DefaultFailure
public import Vegas.EventGraph.ResolutionFields

@[expose] public section

/-! # Every compiled binding is revealed

A source program returns only once every commitment it opened has been
revealed. Every binding event has a reveal of the same owner that consumes
that exact binding as its subject.
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

/-- A source commitment's actual subject is consumed by some source reveal. -/
private theorem compileRankedNodes_reveals_subject {inputCount totalCount : Nat}
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
        (compileRankedNodes program refs revelations registry embedding before
          index).code.resolutionField? = some (refs.get cell).field
  | _, _, .ret _, _, _, _, _, _, _, _, _, _, opened, _ => absurd opened (Finset.notMem_empty _)
  | _, _, .sample newName fresh _ next, _, _, _, _, _, name, _, _, cell, opened, once => by
      have different : newName ≠ name := fun same => fresh (by rw [same]; exact cell.mem_names)
      obtain ⟨index, owned, publication, subject⟩ := compileRankedNodes_reveals_subject next
        _ _ _ _ _ (.there cell) opened (once.cons different)
      exact ⟨index.succ, owned, publication, subject⟩
  | _, _, .commit newName _ fresh _ next, _, _, _, _, _, name, _, _, cell, opened, once => by
      have different : newName ≠ name := fun same => fresh (by rw [same]; exact cell.mem_names)
      obtain ⟨index, owned, publication, subject⟩ := compileRankedNodes_reveals_subject next
        _ _ _ _ _ (.there cell) (Finset.mem_insert_of_mem opened) (once.cons different)
      exact ⟨index.succ, owned, publication, subject⟩
  | _, _, .reveal published revealOwner revealName fresh selected _ next, refs, _, _, _, _,
      name, _, _, cell, opened, once => by
      by_cases same : revealName = name
      · subst same
        obtain ⟨cells, sameCell⟩ := once selected cell
        obtain ⟨rfl, rfl⟩ := CellTy.commitment.inj cells
        obtain rfl := eq_of_heq sameCell
        exact ⟨⟨0, Nat.zero_lt_succ _⟩, rfl, trivial, rfl⟩
      · have different : published ≠ name := fun same => fresh (by rw [same]; exact cell.mem_names)
        obtain ⟨index, owned, publication, subject⟩ := compileRankedNodes_reveals_subject next
          _ _ _ _ _ (.there cell) (Finset.mem_erase.mpr ⟨Ne.symm same, opened⟩)
            (once.cons different)
        exact ⟨index.succ, owned, publication, subject⟩

/-- Every compiled binding has a reveal that consumes it as its subject. -/
private theorem compileRankedNodes_binding_subject {inputCount totalCount : Nat}
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
        (compileRankedNodes program refs revelations registry embedding before
          index).code.resolutionField? = some (embedding.ref event).field
  | _, _, .ret _, _, _, _, _, _, event, _, _, _ => nomatch event
  | _, _, .sample _ _ _ next, _, _, _, _, _, event, _, _, binding => by
      cases event using Fin.cases with
      | zero => exact absurd binding (by simp [outputLayout])
      | succ tail =>
          obtain ⟨index, owned, publication, subject⟩ :=
            compileRankedNodes_binding_subject next _ _ _ _ _ tail binding
          exact ⟨index.succ, owned, publication, subject⟩
  | _, _, .commit _ _ fresh _ next, _, _, _, _, _, event, _, _, binding => by
      cases event using Fin.cases with
      | zero =>
          obtain ⟨rfl, rfl⟩ := EventField.binding.inj binding
          obtain ⟨index, owned, publication, subject⟩ := compileRankedNodes_reveals_subject next
            _ _ _ _ _ HasVar.here (Finset.mem_insert_self _ _) (BoundOnce.here fresh)
          exact ⟨index.succ, owned, publication, subject⟩
      | succ tail =>
          obtain ⟨index, owned, publication, subject⟩ :=
            compileRankedNodes_binding_subject next _ _ _ _ _ tail binding
          exact ⟨index.succ, owned, publication, subject⟩
  | _, _, .reveal _ _ _ _ _ _ next, _, _, _, _, _, event, _, _, binding => by
      cases event using Fin.cases with
      | zero => exact absurd binding (by simp [outputLayout])
      | succ tail =>
          obtain ⟨index, owned, publication, subject⟩ :=
            compileRankedNodes_binding_subject next _ _ _ _ _ tail binding
          exact ⟨index.succ, owned, publication, subject⟩

/-- The declared-read graph retains every binding's actual subject reveal. -/
theorem withDependencies_binding_subject
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (deps : (toEventGraph program).Dependencies)
    (event : Fin (eventCount program)) {owner : Player} {payload : L.Ty}
    (binding : outputLayout program event = .binding owner payload) :
    ∃ reveal, ((toEventGraph program).withDependencies deps).actor? reveal = some owner ∧
      (outputLayout program reveal).IsPublication ∧
      (((toEventGraph program).withDependencies deps).nodes reveal).resolutionField? =
        some (.inr event) := by
  obtain ⟨reveal, owned, publication, subject⟩ := compileRankedNodes_binding_subject program
    (ContextRefs.initial Γ (outputLayout program)) (Revelations.initial Γ) []
    (outputEmbedding program) (initialRefsBefore program) event binding
  exact ⟨reveal, (eventOwner?_eq_actor program reveal).symm.trans owned, publication, subject⟩

/-- **Compiled bindings are revealed.** -/
theorem toInformationGraph_bindingsRevealed {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) :
    (toInformationGraph program).BindingsRevealed := by
  intro event owner payload binding
  obtain ⟨index, owned, publication, subject⟩ :=
    withDependencies_binding_subject program (toInformationGraph program).dependencies event binding
  exact ⟨index, owned, publication,
    ((toInformationGraph program).nodes index).resolutionField?_mem_readFields _ subject⟩

end Vegas
