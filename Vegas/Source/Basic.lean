/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.BoundPublication
import Vegas.Foundation.DeferredGuard

/-! # Failure-aware source language

The source context distinguishes ordinary public data, retained private bindings,
and public publication results.  The `Open` index is linear accounting: every
commitment (including an initial private input) has one publication obligation,
and `ret` is available only after all obligations have been discharged.
-/

namespace Vegas

open Interaction

inductive CellTy (Player : Type) (L : IExpr) where
  | publicData (payload : L.Ty)
  | privateData (owner : Player) (payload : L.Ty)
  | publication (payload : L.Ty)

abbrev SourceCtx (Player : Type) (L : IExpr) := Ctx (CellTy Player L)

/-- A private input is already bound; `.unbound` is not a source action. -/
structure BoundValue (A : Type) where
  binding : Binding A
  isBound : binding ≠ .unbound

namespace BoundValue

def unopenable (A : Type) : BoundValue A :=
  ⟨.unopenable, by intro h; cases h⟩
def value {A : Type} (a : A) : BoundValue A :=
  ⟨.value a, by intro h; cases h⟩

/-- A retained binding is either unopenable or contains one value. -/
def resultEquiv (A : Type) : BoundValue A ≃ PublicationResult A where
  toFun value := match hb : value.binding with
    | .unbound => False.elim (value.isBound hb)
    | .unopenable => .failure
    | .value data => .success data
  invFun
    | .failure => .unopenable A
    | .success data => .value data
  left_inv value := by
    rcases value with ⟨binding, bound⟩
    cases binding with
    | unbound => exact False.elim (bound rfl)
    | unopenable => rfl
    | value data => rfl
  right_inv result := by cases result <;> rfl

end BoundValue

def CellVal {Player : Type} (L : IExpr) : CellTy Player L → Type
  | .publicData τ => L.Val τ
  | .privateData _ τ => BoundValue (L.Val τ) × Publication (L.Val τ)
  | .publication τ => PublicationResult (L.Val τ)

abbrev State {Player : Type} (L : IExpr) (Γ : SourceCtx Player L) :=
  Env (CellVal (Player := Player) L) Γ

/-- A guard input is either permanently ordinary public data or the eventual
publication of a private resource.  In particular it is never the raw binding. -/
inductive SourceGuardRead {Player : Type} {L : IExpr} (Γ : SourceCtx Player L)
    (author : Player) :
    L.Ty → Type where
  | publicData {x τ} (h : HasVar Γ x (.publicData τ)) : SourceGuardRead Γ author τ
  | privateData {x τ} (h : HasVar Γ x (.privateData author τ)) : SourceGuardRead Γ author τ
  | publication {x τ} (h : HasVar Γ x (.publication τ)) : SourceGuardRead Γ author τ

namespace SourceGuardRead

def get {Player : Type} {L : IExpr}
    {Γ : SourceCtx Player L} {author : Player} {τ : L.Ty} :
      SourceGuardRead Γ author τ → State L Γ → Publication (L.Val τ)
  | .publicData h, state => .value (state.get h)
  | .privateData h, state => (state.get h).2
  | .publication h, state =>
      match state.get h with
      | .failure => .failed
      | .success value => .value value

def weaken {Player : Type} {L : IExpr} {Γ : SourceCtx Player L} {τ : L.Ty}
    {author : Player} {x : VarId} {cell : CellTy Player L} :
      SourceGuardRead Γ author τ → SourceGuardRead ((x, cell) :: Γ) author τ
  | .publicData h => .publicData (.there h)
  | .privateData h => .privateData (.there h)
  | .publication h => .publication (.there h)

@[simp] theorem get_weaken {Player : Type} {L : IExpr}
    {Γ : SourceCtx Player L} {τ : L.Ty} {author : Player}
    {name : VarId} {cell : CellTy Player L} (read : SourceGuardRead Γ author τ)
    (head : CellVal L cell) (state : State L Γ) :
    read.weaken.get (Env.cons (x := name) head state) = read.get state := by
  cases read <;> rfl

end SourceGuardRead

/-- A retained guard whose executable code is independent of source state. -/
structure SourceGuard {Player : Type} (L : IExpr) (Γ : SourceCtx Player L)
    (author : Player) (subject : VarId) (payload : L.Ty)
    extends DeferredGuardCode L subject payload where
  reads : ∀ {x τ}, HasVar schema x τ → SourceGuardRead Γ author τ

namespace SourceGuard

variable {Player : Type} {L : IExpr}

/-- Evaluate shared deferred-guard code through a source-state read adapter. -/
def check {Γ : SourceCtx Player L} {subject : VarId} {payload : L.Ty}
    {author : Player} (guard : SourceGuard L Γ author subject payload)
    (candidate : Publication (L.Val payload)) (state : State L Γ) :
    PublicationGuard.Verdict :=
  guard.toDeferredGuardCode.check candidate fun h => (guard.reads h).get state

theorem check_congr
    {Γ : SourceCtx Player L} {subject : VarId} {payload : L.Ty}
    {author : Player} (guard : SourceGuard L Γ author subject payload)
    (leftCandidate rightCandidate : Publication (L.Val payload))
    (leftState rightState : State L Γ)
    (candidateEq : leftCandidate = rightCandidate)
    (supportEq : ∀ {x τ} (h : HasVar guard.schema x τ),
      x ∈ L.exprDeps guard.code →
        (guard.reads h).get leftState = (guard.reads h).get rightState) :
    guard.check leftCandidate leftState = guard.check rightCandidate rightState :=
  DeferredGuardCode.check_congr guard.toDeferredGuardCode _ _ _ _ candidateEq supportEq

theorem check_subject_pending_ne_rejected
    {Γ : SourceCtx Player L} {subject : VarId} {payload : L.Ty}
    {author : Player} (guard : SourceGuard L Γ author subject payload)
    (state : State L Γ) : guard.check .pending state ≠ .rejected :=
  DeferredGuardCode.check_subject_pending_ne_rejected guard.toDeferredGuardCode _

@[simp] theorem check_subject_failed
    {Γ : SourceCtx Player L} {subject : VarId} {payload : L.Ty}
    {author : Player} (guard : SourceGuard L Γ author subject payload)
    (state : State L Γ) : guard.check .failed state = .satisfied :=
  DeferredGuardCode.check_subject_failed guard.toDeferredGuardCode _

/-- Extend a guard across a newly introduced source cell. -/
def weaken {Γ : SourceCtx Player L} {subject : VarId} {payload : L.Ty}
    {author : Player} {name : VarId} {cell : CellTy Player L}
    (guard : SourceGuard L Γ author subject payload) :
    SourceGuard L ((name, cell) :: Γ) author subject payload where
  toDeferredGuardCode := guard.toDeferredGuardCode
  reads := fun h => (guard.reads h).weaken

@[simp] theorem check_weaken
    {Γ : SourceCtx Player L} {subject : VarId} {payload : L.Ty}
    {author : Player} {name : VarId} {cell : CellTy Player L}
    (guard : SourceGuard L Γ author subject payload)
    (candidate : Publication (L.Val payload))
    (head : CellVal L cell) (state : State L Γ) :
    guard.weaken.check candidate (Env.cons (x := name) head state) =
      guard.check candidate state := by
  apply DeferredGuardCode.check_congr guard.toDeferredGuardCode <;> try rfl
  intro x τ h _
  exact SourceGuardRead.get_weaken (guard.reads h) head state

theorem check_satisfied_of_failed_read
    {Γ : SourceCtx Player L} {subject : VarId} {payload : L.Ty}
    {author : Player} (guard : SourceGuard L Γ author subject payload)
    (candidate : Publication (L.Val payload)) (state : State L Γ)
    {x : VarId} {τ : L.Ty} (h : HasVar guard.schema x τ)
    (supported : x ∈ L.exprDeps guard.code)
    (failed : (guard.reads h).get state = .failed) :
    guard.check candidate state = .satisfied :=
  DeferredGuardCode.check_satisfied_of_failed_read
    guard.toDeferredGuardCode candidate _ h supported failed

theorem check_ne_pending_of_support_resolved
    {Γ : SourceCtx Player L} {subject : VarId} {payload : L.Ty}
    {author : Player} (guard : SourceGuard L Γ author subject payload)
    (candidate : Publication (L.Val payload)) (state : State L Γ)
    (subjectResolved : candidate ≠ .pending)
    (supportResolved : ∀ {x τ} (h : HasVar guard.schema x τ),
      x ∈ L.exprDeps guard.code → (guard.reads h).get state ≠ .pending) :
    guard.check candidate state ≠ .pending :=
  DeferredGuardCode.check_ne_pending_of_support_resolved
    guard.toDeferredGuardCode candidate _ subjectResolved supportResolved

theorem check_pending
    {Γ : SourceCtx Player L} {subject : VarId} {payload : L.Ty}
    {author : Player} (guard : SourceGuard L Γ author subject payload)
    (candidate : Publication (L.Val payload)) (state : State L Γ)
    (subjectNotFailed : candidate ≠ .failed)
    (supportNotFailed : ∀ {x τ} (h : HasVar guard.schema x τ),
      x ∈ L.exprDeps guard.code → (guard.reads h).get state ≠ .failed)
    (waiting : candidate = .pending ∨
      ∃ (x : VarId) (τ : L.Ty) (h : HasVar guard.schema x τ),
        x ∈ L.exprDeps guard.code ∧ (guard.reads h).get state = .pending) :
    guard.check candidate state = .pending :=
  DeferredGuardCode.check_pending guard.toDeferredGuardCode candidate _
    subjectNotFailed supportNotFailed waiting

theorem check_values
    {Γ : SourceCtx Player L} {subject : VarId} {payload : L.Ty}
    {author : Player} (guard : SourceGuard L Γ author subject payload)
    (subjectValue : L.Val payload) (state : State L Γ)
    (get : (x : VarId) → (σ : L.Ty) → HasVar ((subject, payload) :: guard.schema) x σ →
      x ∈ L.exprDeps guard.code → L.Val σ)
    (subjectEq : ∀ hx, get subject payload .here hx = subjectValue)
    (readsEq : ∀ {x τ} (h : HasVar guard.schema x τ) (hx : x ∈ L.exprDeps guard.code),
      (guard.reads h).get state = .value (get x τ (.there h) hx)) :
    guard.check (.value subjectValue) state =
      if L.toBool (L.evalDeps guard.code get) then .satisfied else .rejected :=
  DeferredGuardCode.check_values guard.toDeferredGuardCode subjectValue _ get subjectEq readsEq

theorem check_compatible
    {Γ : SourceCtx Player L} {subject : VarId} {payload : L.Ty}
    {author : Player} (guard : SourceGuard L Γ author subject payload)
    (candidate : Publication (L.Val payload)) (state : State L Γ)
    (subjectValue : L.Val payload)
    (get : (x : VarId) → (σ : L.Ty) → HasVar ((subject, payload) :: guard.schema) x σ →
      x ∈ L.exprDeps guard.code → L.Val σ)
    (subjectEq : ∀ hx, get subject payload .here hx = subjectValue)
    (subjectAgrees : ∀ value, candidate = .value value → value = subjectValue)
    (readsAgree : ∀ {x τ} (h : HasVar guard.schema x τ)
      (hx : x ∈ L.exprDeps guard.code) (value : L.Val τ),
        (guard.reads h).get state = .value value → value = get x τ (.there h) hx)
    (valid : L.toBool (L.evalDeps guard.code get) = true) :
    guard.check candidate state ≠ .rejected :=
  DeferredGuardCode.check_compatible guard.toDeferredGuardCode candidate _ subjectValue get
    subjectEq subjectAgrees readsAgree valid

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

/-- Initially retained private inputs have not yet been published. -/
def PrivatePending : {Γ : SourceCtx Player L} → State L Γ → Prop
  | [], _ => True
  | (_, .publicData _) :: Γ, state =>
      PrivatePending (Γ := Γ) (fun _ _ h => state.get (.there h))
  | (_, .publication _) :: Γ, state =>
      PrivatePending (Γ := Γ) (fun _ _ h => state.get (.there h))
  | (_, .privateData _ _) :: Γ, state =>
      (state.get .here).2 = .pending ∧
        PrivatePending (Γ := Γ) (fun _ _ h => state.get (.there h))

/-- A runnable source program together with its typed initial state and exact
accounting for the publication obligations contributed by private inputs. -/
structure Initial where
  context : SourceCtx Player L
  namesNodup : (context.map Prod.fst).Nodup
  state : State L context
  privatePending : PrivatePending state
  obligations : Finset VarId
  program : SourceProgram Player L context obligations
  accounts : obligations = privateNames context

end SourceProgram

end Vegas
