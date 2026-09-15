/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.GraphSetup
import Vegas.Graph.BindingDiscipline

/-! # Binding-origin discipline of source-compiled graphs -/

noncomputable section
namespace Vegas.SourceProgram

open Vegas.Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- Recorded graph origins agree with every source private field for which an
origin has been installed. Initial private fields may remain unknown. -/
def OriginsAgree (origins : BindingOrigins L) (Γ : SourceCtx Player L) : Prop :=
  ∀ {name owner payload}, HasVar Γ name (.privateData owner payload) →
    ∀ {origin}, origins name = some origin → origin = payload

omit [DecidableEq Player] R in theorem originsAgree_none (Γ : SourceCtx Player L) :
    OriginsAgree (Player := Player) (BindingOrigins.none (L := L)) Γ := by
  intro name owner payload source origin horigin
  simp [BindingOrigins.none] at horigin

omit [DecidableEq Player] R in theorem OriginsAgree.cons_nonprivate
    {origins : BindingOrigins L} {Γ : SourceCtx Player L}
    (agreement : OriginsAgree (Player := Player) origins Γ)
    (name : VarId) (cell : CellTy Player L)
    (hnonprivate : ∀ owner payload, cell ≠ .privateData owner payload) :
    OriginsAgree origins ((name, cell) :: Γ) := by
  intro queried owner payload source origin horigin
  cases source with
  | here => exact False.elim (hnonprivate owner payload rfl)
  | there source => exact agreement source horigin

omit [DecidableEq Player] R in theorem OriginsAgree.insert_private
    {origins : BindingOrigins L} {Γ : SourceCtx Player L}
    (agreement : OriginsAgree (Player := Player) origins Γ)
    {name : VarId} (owner : Player) (payload : L.Ty) (fresh : name ∉ Γ.map Prod.fst) :
    OriginsAgree (origins.insert name payload) ((name, .privateData owner payload) :: Γ) := by
  intro queried queriedOwner queriedPayload source origin horigin
  cases source with
  | here =>
      rw [BindingOrigins.insert_self] at horigin
      exact (Option.some.inj horigin).symm
  | there source =>
      have hne : queried ≠ name := by
        intro h
        apply fresh
        simpa [h] using source.mem_map_fst
      rw [BindingOrigins.insert_other origins payload hne] at horigin
      exact agreement source horigin

omit [DecidableEq Player] R in theorem OriginsAgree.cons_publicData
    {origins : BindingOrigins L} {Γ : SourceCtx Player L}
    (agreement : OriginsAgree (Player := Player) origins Γ)
    (name : VarId) (payload : L.Ty) :
    OriginsAgree origins ((name, .publicData payload) :: Γ) :=
  OriginsAgree.cons_nonprivate agreement name _ (by intros; simp)

omit [DecidableEq Player] R in theorem OriginsAgree.cons_publication
    {origins : BindingOrigins L} {Γ : SourceCtx Player L}
    (agreement : OriginsAgree (Player := Player) origins Γ)
    (name : VarId) (payload : L.Ty) :
    OriginsAgree origins ((name, .publication payload) :: Γ) :=
  OriginsAgree.cons_nonprivate agreement name _ (by intros; simp)

/-- The source compiler preserves the threaded binding-origin certificate. -/
theorem compileGraph_bindingDiscipline : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) →
    (unique : (Γ.map Prod.fst).Nodup) → (map : PublicationMap (R := R) Γ) →
    (registry : Registry Γ) → (origins : BindingOrigins L) →
    OriginsAgree origins Γ →
    BindingDiscipline origins (compileGraph program unique map registry)
  | _, _, .ret _, _, _, _, _, _ => trivial
  | _, _, .sample name fresh law next, unique, map, registry, origins, agreement =>
      compileGraph_bindingDiscipline next (by simp [fresh, unique]) (weakenMap map)
        registry.weaken origins (agreement.cons_publicData name _)
  | _, _, .commit name owner fresh guard next, unique, map, registry, origins, agreement =>
      compileGraph_bindingDiscipline next (by simp [fresh, unique]) (weakenMap map)
        (_ :: registry.weaken) (origins.insert name _) (agreement.insert_private owner _ fresh)
  | _, _, .reveal published owner name fresh source unresolved next,
      unique, map, registry, origins, agreement =>
      ⟨fun origin horigin => agreement source horigin,
        compileGraph_bindingDiscipline next (by simp [fresh, unique])
          (resolveMap map unique source (published := published)) registry.weaken origins
          (agreement.cons_publication published _)⟩

/-- Every source compiler entry point starts with unknown, verified initial
origins and produces a disciplined graph. -/
theorem Initial.graph_bindingDiscipline (source : Initial (Player := Player) (L := L)) :
    BindingDiscipline BindingOrigins.none source.graph := by
  exact compileGraph_bindingDiscipline source.program source.namesNodup initialMap []
    BindingOrigins.none (originsAgree_none source.context)

/-- Every distributed setup graph starts with unknown, verified initial origins
and preserves the binding payload discipline through its compiled body. -/
theorem Setup.graph_bindingDiscipline (setup : Setup (Player := Player) (L := L)) :
    BindingDiscipline BindingOrigins.none setup.graph := by
  exact compileGraph_bindingDiscipline setup.program setup.namesNodup initialMap []
    BindingOrigins.none (originsAgree_none setup.context)

end Vegas.SourceProgram
