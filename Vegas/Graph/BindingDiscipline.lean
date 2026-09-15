/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.Basic

/-! # Payload origins for graph bindings -/

namespace Vegas.Graph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [R : IExpr.ResultTypes L]

abbrev BindingOrigins (L : IExpr) := VarId → Option L.Ty

def BindingOrigins.none : BindingOrigins L := fun _ => Option.none

def BindingOrigins.insert (origins : BindingOrigins L) (name : VarId) (payload : L.Ty) :
    BindingOrigins L := fun queried => if queried = name then some payload else origins queried

omit R in @[simp] theorem BindingOrigins.insert_self (origins : BindingOrigins L)
    (name : VarId) (payload : L.Ty) : origins.insert name payload name = some payload := by
  simp [BindingOrigins.insert]

omit R in theorem BindingOrigins.insert_other (origins : BindingOrigins L)
    {name queried : VarId} (payload : L.Ty) (hne : queried ≠ name) :
    origins.insert name payload queried = origins queried := by
  simp [BindingOrigins.insert, hne]

/-- Binding payload origins are threaded with the graph cursor. A resolve may
use an unknown initial origin, but every recorded origin must equal its typed
resolve payload. -/
def BindingDiscipline : {Γ Δ : VCtx Player L} → BindingOrigins L →
    Graph Player L Γ Δ → Prop
  | _, _, _, .ret _ => True
  | _, _, origins, .sample _ _ _ next => BindingDiscipline origins next
  | _, _, origins, .bind name _ (payload := payload) _ next =>
      BindingDiscipline (origins.insert name payload) next
  | _, _, origins, .resolve _ _ bindingName (payload := payload) _ _ _ next =>
      (∀ origin, origins bindingName = some origin → origin = payload) ∧
        BindingDiscipline origins next

end Vegas.Graph
