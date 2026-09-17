/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Foundation.Guard

/-! # Failure-aware source language

The source context distinguishes ordinary public data, retained private bindings,
and public publication results. The `Open` index is linear accounting: every
commitment, including an initial private input, is revealed exactly once, and
`ret` is available only after all of them are revealed.

A guard is declared at its subject's commitment, where it constrains the
committing player: it reads public cells and that player's own private cells.
It is checked once, at the reveal that publishes the last of its inputs.
`Revelations` records statically where each private cell has been published.
-/

namespace Vegas

inductive CellTy (Player : Type) (L : IExpr) where
  | publicData (payload : L.Ty)
  | privateData (owner : Player) (payload : L.Ty)
  | publication (payload : L.Ty)

abbrev SourceCtx (Player : Type) (L : IExpr) := Ctx (CellTy Player L)

/-- A private cell holds its binding: the result its owner's disclosure would
publish. A `.failure` binding is unopenable. -/
abbrev CellVal {Player : Type} (L : IExpr) : CellTy Player L → Type
  | .publicData τ => L.Val τ
  | .privateData _ τ => PublicationResult (L.Val τ)
  | .publication τ => PublicationResult (L.Val τ)

abbrev State {Player : Type} (L : IExpr) (Γ : SourceCtx Player L) :=
  Env (CellVal (Player := Player) L) Γ

/-- Where a private cell's result is public: nowhere yet, or in a publication
cell of the context. -/
inductive Revelation {Player : Type} {L : IExpr} (Γ : SourceCtx Player L)
    (payload : L.Ty) where
  | unrevealed
  | revealed {name : VarId} (cell : HasVar Γ name (.publication payload))

namespace Revelation

variable {Player : Type} {L : IExpr} {Γ : SourceCtx Player L} {payload : L.Ty}

def isRevealed : Revelation Γ payload → Bool
  | .unrevealed => false
  | .revealed _ => true

/-- The published result. An unrevealed cell reads as failure only to keep this
function total: a guard is checked only once all of its inputs are revealed. -/
def result (state : State L Γ) : Revelation Γ payload → PublicationResult (L.Val payload)
  | .unrevealed => .failure
  | .revealed cell => state.get cell

def weaken {name : VarId} {cell : CellTy Player L} :
    Revelation Γ payload → Revelation ((name, cell) :: Γ) payload
  | .unrevealed => .unrevealed
  | .revealed published => .revealed (.there published)

@[simp] theorem isRevealed_weaken {name : VarId} {cell : CellTy Player L}
    (revelation : Revelation Γ payload) :
    (revelation.weaken (name := name) (cell := cell)).isRevealed = revelation.isRevealed := by
  cases revelation <;> rfl

@[simp] theorem result_weaken {name : VarId} {cell : CellTy Player L}
    (revelation : Revelation Γ payload) (head : CellVal L cell) (state : State L Γ) :
    (revelation.weaken (name := name)).result (Env.cons head state) =
      revelation.result state := by
  cases revelation <;> rfl

end Revelation

/-- The static publication status of every private cell in scope. -/
abbrev Revelations {Player : Type} {L : IExpr} (Γ : SourceCtx Player L) :=
  ∀ {owner : Player} {payload : L.Ty} {name : VarId},
    HasVar Γ name (.privateData owner payload) → Revelation Γ payload

namespace Revelations

variable {Player : Type} {L : IExpr} {Γ : SourceCtx Player L}

/-- No private cell is revealed. -/
def initial (Γ : SourceCtx Player L) : Revelations Γ := fun _ => .unrevealed

/-- Extend across a new cell. A new private cell is unrevealed. -/
def weaken {name : VarId} {cell : CellTy Player L} (revelations : Revelations Γ) :
    Revelations ((name, cell) :: Γ) :=
  fun h =>
    match h.tail? with
    | none => .unrevealed
    | some h => (revelations h).weaken

/-- Reveal `source` into the publication cell at the head of the context. -/
def reveal {owner : Player} {payload : L.Ty} {name published : VarId}
    (revelations : Revelations Γ) (source : HasVar Γ name (.privateData owner payload)) :
    Revelations ((published, .publication payload) :: Γ) :=
  fun h =>
    match h.tail? with
    | none => .unrevealed
    | some h =>
        match h.sameCell? source with
        | some same => (CellTy.privateData.inj same.down.2).2 ▸ .revealed .here
        | none => (revelations h).weaken

@[simp] theorem weaken_there {name : VarId} {cell : CellTy Player L}
    (revelations : Revelations Γ) {owner : Player} {payload : L.Ty} {private_ : VarId}
    (h : HasVar Γ private_ (.privateData owner payload)) :
    revelations.weaken (name := name) (cell := cell) (.there h) = (revelations h).weaken :=
  rfl

@[simp] theorem reveal_source {owner : Player} {payload : L.Ty} {name published : VarId}
    (revelations : Revelations Γ) (source : HasVar Γ name (.privateData owner payload)) :
    revelations.reveal (published := published) source (.there source) = .revealed .here := by
  simp only [reveal, HasVar.tail?_there, HasVar.sameCell?_self]

theorem reveal_of_ne {owner : Player} {payload : L.Ty} {name published : VarId}
    (revelations : Revelations Γ) (source : HasVar Γ name (.privateData owner payload))
    {readOwner : Player} {readPayload : L.Ty} {readName : VarId}
    (h : HasVar Γ readName (.privateData readOwner readPayload)) (different : readName ≠ name) :
    revelations.reveal (published := published) source (.there h) = (revelations h).weaken := by
  simp only [reveal, HasVar.tail?_there, HasVar.sameCell?_eq_none_of_ne h source different]

end Revelations

/-- A guard input is ordinary public data, a publication result, or the eventual
publication of the guard author's own private cell. It is never a raw binding. -/
inductive SourceGuardRead {Player : Type} {L : IExpr} (Γ : SourceCtx Player L)
    (author : Player) :
    L.Ty → Type where
  | publicData {x τ} (h : HasVar Γ x (.publicData τ)) : SourceGuardRead Γ author τ
  | privateData {x τ} (h : HasVar Γ x (.privateData author τ)) : SourceGuardRead Γ author τ
  | publication {x τ} (h : HasVar Γ x (.publication τ)) : SourceGuardRead Γ author τ

namespace SourceGuardRead

variable {Player : Type} {L : IExpr} {Γ : SourceCtx Player L} {author : Player} {τ : L.Ty}

def revealed (revelations : Revelations Γ) : SourceGuardRead Γ author τ → Bool
  | .publicData _ | .publication _ => true
  | .privateData h => (revelations h).isRevealed

def result (revelations : Revelations Γ) (state : State L Γ) :
    SourceGuardRead Γ author τ → PublicationResult (L.Val τ)
  | .publicData h => .success (state.get h)
  | .privateData h => (revelations h).result state
  | .publication h => state.get h

def weaken {x : VarId} {cell : CellTy Player L} :
    SourceGuardRead Γ author τ → SourceGuardRead ((x, cell) :: Γ) author τ
  | .publicData h => .publicData (.there h)
  | .privateData h => .privateData (.there h)
  | .publication h => .publication (.there h)

@[simp] theorem revealed_weaken {x : VarId} {cell : CellTy Player L}
    (read : SourceGuardRead Γ author τ) (revelations : Revelations Γ) :
    (read.weaken (x := x) (cell := cell)).revealed revelations.weaken =
      read.revealed revelations := by
  cases read <;> simp [revealed, weaken]

@[simp] theorem result_weaken {x : VarId} {cell : CellTy Player L}
    (read : SourceGuardRead Γ author τ) (revelations : Revelations Γ)
    (head : CellVal L cell) (state : State L Γ) :
    (read.weaken (x := x)).result revelations.weaken (Env.cons head state) =
      read.result revelations state := by
  cases read <;> simp [result, weaken]

end SourceGuardRead

/-- A guard retained at a commitment: its code and where each input is read. -/
structure SourceGuard {Player : Type} (L : IExpr) (Γ : SourceCtx Player L)
    (author : Player) (subject : VarId) (payload : L.Ty)
    extends GuardCode L subject payload where
  reads : ∀ {x τ}, HasVar schema x τ → SourceGuardRead Γ author τ

namespace SourceGuard

variable {Player : Type} {L : IExpr} {Γ : SourceCtx Player L}
variable {author : Player} {subject : VarId} {payload : L.Ty}

/-- Whether every input read by the code is published. The subject is tracked
by the obligation that retains the guard. -/
def readsRevealed (guard : SourceGuard L Γ author subject payload)
    (revelations : Revelations Γ) : Bool :=
  guard.allReads fun h => (guard.reads h).revealed revelations

/-- Decide the guard on its subject's result and its inputs' published results. -/
def accepts (guard : SourceGuard L Γ author subject payload)
    (subjectResult : PublicationResult (L.Val payload)) (revelations : Revelations Γ)
    (state : State L Γ) : Bool :=
  guard.toGuardCode.accepts subjectResult fun h _ => (guard.reads h).result revelations state

/-- Extend a guard across a newly introduced source cell. -/
def weaken {name : VarId} {cell : CellTy Player L}
    (guard : SourceGuard L Γ author subject payload) :
    SourceGuard L ((name, cell) :: Γ) author subject payload where
  toGuardCode := guard.toGuardCode
  reads := fun h => (guard.reads h).weaken

@[simp] theorem readsRevealed_weaken {name : VarId} {cell : CellTy Player L}
    (guard : SourceGuard L Γ author subject payload) (revelations : Revelations Γ) :
    (guard.weaken (name := name) (cell := cell)).readsRevealed revelations.weaken =
      guard.readsRevealed revelations := by
  simp only [readsRevealed, weaken, SourceGuardRead.revealed_weaken]

@[simp] theorem accepts_weaken {name : VarId} {cell : CellTy Player L}
    (guard : SourceGuard L Γ author subject payload)
    (subjectResult : PublicationResult (L.Val payload)) (revelations : Revelations Γ)
    (head : CellVal L cell) (state : State L Γ) :
    (guard.weaken (name := name)).accepts subjectResult revelations.weaken
        (Env.cons head state) = guard.accepts subjectResult revelations state := by
  simp only [accepts, weaken, SourceGuardRead.result_weaken]

end SourceGuard

def SourcePublicCtx {Player : Type} (L : IExpr) [R : IExpr.ResultTypes L] :
    SourceCtx Player L → Ctx L.Ty
  | [] => []
  | (x, .publicData τ) :: Γ => (x, τ) :: SourcePublicCtx L Γ
  | (_, .privateData _ _) :: Γ => SourcePublicCtx L Γ
  | (x, .publication τ) :: Γ => (x, R.result τ) :: SourcePublicCtx L Γ

/-- Straight-line source syntax with structural publication accounting. -/
inductive SourceProgram (Player : Type) [DecidableEq Player] (L : IExpr)
    [IExpr.ResultTypes L] : SourceCtx Player L → Finset VarId → Type where
  | ret {Γ} (payoffs : List (Player × L.Expr (SourcePublicCtx L Γ) L.int)) :
      SourceProgram Player L Γ ∅
  | sample {Γ Open} (name : VarId) {payload : L.Ty}
      (fresh : name ∉ Γ.map Prod.fst) (law : L.DistExpr (SourcePublicCtx L Γ) payload)
      (next : SourceProgram Player L ((name, .publicData payload) :: Γ) Open) :
      SourceProgram Player L Γ Open
  | commit {Γ Open} (name : VarId) (owner : Player) {payload : L.Ty}
      (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
      (next : SourceProgram Player L ((name, .privateData owner payload) :: Γ)
        (insert name Open)) : SourceProgram Player L Γ Open
  | reveal {Γ Open} (published : VarId) (owner : Player) (name : VarId) {payload : L.Ty}
      (fresh : published ∉ Γ.map Prod.fst)
      (source : HasVar Γ name (.privateData owner payload))
      (unresolved : name ∈ Open)
      (next : SourceProgram Player L ((published, .publication payload) :: Γ)
        (Open.erase name)) : SourceProgram Player L Γ Open

namespace SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Names of the private cells already present in an initial source context. -/
def privateNames : SourceCtx Player L → Finset VarId
  | [] => ∅
  | (name, .privateData _ _) :: Γ => insert name (privateNames Γ)
  | (_, .publicData _) :: Γ | (_, .publication _) :: Γ => privateNames Γ

/-- A runnable source program together with its typed initial state and exact
accounting for the reveals owed by initial private inputs. -/
structure Initial where
  context : SourceCtx Player L
  namesNodup : (context.map Prod.fst).Nodup
  state : State L context
  obligations : Finset VarId
  program : SourceProgram Player L context obligations
  accounts : obligations = privateNames context

end SourceProgram

end Vegas
