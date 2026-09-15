/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.BoundPublication
import Vegas.Foundation.ExprInterface

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

/-- A retained guard and its exact, semantic static read support.  `reads`
interprets the ordinary expression schema through public resolution status. -/
structure SourceGuard {Player : Type} (L : IExpr) (Γ : SourceCtx Player L)
    (author : Player) (subject : VarId) (payload : L.Ty) where
  schema : Ctx L.Ty
  schemaNames : (schema.map Prod.fst).Nodup
  subjectFresh : subject ∉ schema.map Prod.fst
  code : L.Expr ((subject, payload) :: schema) L.bool
  reads : ∀ {x τ}, HasVar schema x τ → SourceGuardRead Γ author τ

namespace SourceGuard

variable {Player : Type} {L : IExpr}

private inductive ReadOutcome (schema : Ctx L.Ty) (deps : Finset VarId) where
  | failed
  | pending
  | ready
      (get : ∀ {x τ}, HasVar schema x τ → x ∈ deps → L.Val τ)

private def collectReads {Γ : SourceCtx Player L} {author : Player}
    (state : State L Γ) (deps : Finset VarId) :
    (schema : Ctx L.Ty) →
      (∀ {x τ}, HasVar schema x τ → SourceGuardRead Γ author τ) →
      ReadOutcome schema deps
  | [], _ => .ready fun h _ => nomatch h
  | (name, τ) :: tail, reads =>
      let rest := collectReads state deps tail (fun h => reads (.there h))
      if member : name ∈ deps then
        match (reads (.here)).get state with
        | .failed => .failed
        | .pending => match rest with | .failed => .failed | _ => .pending
        | .value value =>
            match rest with
            | .failed => .failed
            | .pending => .pending
            | .ready tailGet => .ready fun h _ =>
                match h with
                | .here => value
                | .there h => tailGet h (by simpa using ‹_›)
      else
        match rest with
        | .failed => .failed
        | .pending => .pending
        | .ready tailGet => .ready fun h hx =>
            match h with
            | .here => False.elim (member hx)
            | .there h => tailGet h hx

private theorem collectReads_congr
    {Γ : SourceCtx Player L} {author : Player} (deps : Finset VarId)
    (schema : Ctx L.Ty)
    (reads : ∀ {x τ}, HasVar schema x τ → SourceGuardRead Γ author τ)
    (left right : State L Γ)
    (agree : ∀ {x τ} (h : HasVar schema x τ), x ∈ deps →
      (reads h).get left = (reads h).get right) :
    collectReads left deps schema reads = collectReads right deps schema reads := by
  induction schema with
  | nil => rfl
  | cons entry tail ih =>
      obtain ⟨name, τ⟩ := entry
      have tailAgree : ∀ {x σ} (h : HasVar tail x σ), x ∈ deps →
          (reads (.there h)).get left = (reads (.there h)).get right :=
        fun h hx => agree (.there h) hx
      have tailEq := ih (fun h => reads (.there h)) tailAgree
      by_cases member : name ∈ deps
      · have headEq := agree
          (.here : HasVar ((name, τ) :: tail) name τ) member
        simp only [collectReads, dif_pos member]
        rw [headEq, tailEq]
      · simp only [collectReads, dif_neg member]
        rw [tailEq]

/-- Executable null-vacuous checking over the expression's exact static
support. The subject participates independently, even for constant code. -/
def check {Γ : SourceCtx Player L} {subject : VarId} {payload : L.Ty}
    {author : Player} (guard : SourceGuard L Γ author subject payload)
    (candidate : Publication (L.Val payload)) (state : State L Γ) :
    PublicationGuard.Verdict :=
  match candidate with
  | .failed => .satisfied
  | .pending =>
      match collectReads state (L.exprDeps guard.code) guard.schema guard.reads with
      | .failed => .satisfied
      | .pending | .ready _ => .pending
  | .value subjectValue =>
      match collectReads state (L.exprDeps guard.code) guard.schema guard.reads with
      | .failed => .satisfied
      | .pending => .pending
      | .ready get =>
          let ordinary := L.evalDeps guard.code fun _ _ h hx =>
            match h with
            | .here => subjectValue
            | .there h => get h hx
          if L.toBool ordinary then .satisfied else .rejected

/-- Guard checking depends only on the candidate and the publication statuses
of the expression's declared static support. -/
theorem check_congr
    {Γ : SourceCtx Player L} {subject : VarId} {payload : L.Ty}
    {author : Player} (guard : SourceGuard L Γ author subject payload)
    (leftCandidate rightCandidate : Publication (L.Val payload))
    (leftState rightState : State L Γ)
    (candidateEq : leftCandidate = rightCandidate)
    (supportEq : ∀ {x τ} (h : HasVar guard.schema x τ),
      x ∈ L.exprDeps guard.code →
        (guard.reads h).get leftState = (guard.reads h).get rightState) :
    guard.check leftCandidate leftState = guard.check rightCandidate rightState := by
  subst rightCandidate
  have collected := collectReads_congr (L.exprDeps guard.code) guard.schema
    guard.reads leftState rightState supportEq
  unfold check
  rw [collected]

theorem check_subject_pending_ne_rejected
    {Γ : SourceCtx Player L} {subject : VarId} {payload : L.Ty}
    {author : Player} (guard : SourceGuard L Γ author subject payload)
    (state : State L Γ) : guard.check .pending state ≠ .rejected := by
  simp only [check]
  generalize hresult :
    collectReads state (L.exprDeps guard.code) guard.schema guard.reads = result
  cases result <;> simp

@[simp] theorem check_subject_failed
    {Γ : SourceCtx Player L} {subject : VarId} {payload : L.Ty}
    {author : Player} (guard : SourceGuard L Γ author subject payload)
    (state : State L Γ) : guard.check .failed state = .satisfied := rfl

/-- Extend a guard across a newly introduced source cell. -/
def weaken {Γ : SourceCtx Player L} {subject : VarId} {payload : L.Ty}
    {author : Player} {name : VarId} {cell : CellTy Player L}
    (guard : SourceGuard L Γ author subject payload) :
    SourceGuard L ((name, cell) :: Γ) author subject payload where
  schema := guard.schema
  schemaNames := guard.schemaNames
  subjectFresh := guard.subjectFresh
  code := guard.code
  reads := fun h => (guard.reads h).weaken

private theorem collectReads_weaken
    {Γ : SourceCtx Player L} {author : Player} {name : VarId}
    {cell : CellTy Player L} (head : CellVal L cell) (state : State L Γ)
    (deps : Finset VarId) (schema : Ctx L.Ty)
    (reads : ∀ {x τ}, HasVar schema x τ → SourceGuardRead Γ author τ) :
    collectReads (Env.cons (x := name) head state) deps schema
        (fun h => (reads h).weaken) =
      collectReads state deps schema reads := by
  induction schema with
  | nil => rfl
  | cons entry tail ih =>
      obtain ⟨x, τ⟩ := entry
      simp only [collectReads]
      rw [ih (fun h => reads (.there h))]
      rw [SourceGuardRead.get_weaken]

/-- Guard checking is invariant under extending the source state with a cell
that was not present when the guard was authored. -/
@[simp] theorem check_weaken
    {Γ : SourceCtx Player L} {subject : VarId} {payload : L.Ty}
    {author : Player} {name : VarId} {cell : CellTy Player L}
    (guard : SourceGuard L Γ author subject payload)
    (candidate : Publication (L.Val payload))
    (head : CellVal L cell) (state : State L Γ) :
    guard.weaken.check candidate (Env.cons (x := name) head state) =
      guard.check candidate state := by
  have collected :
      collectReads (Env.cons (x := name) head state) (L.exprDeps guard.code)
          guard.weaken.schema guard.weaken.reads =
        collectReads state (L.exprDeps guard.code) guard.schema guard.reads := by
    exact collectReads_weaken (name := name) head state
      (L.exprDeps guard.code) guard.schema guard.reads
  have normalized :
      collectReads (Env.cons (x := name) head state) (L.exprDeps guard.code)
          guard.schema (fun h => (guard.reads h).weaken) =
        collectReads state (L.exprDeps guard.code) guard.schema guard.reads := by
    simpa only [weaken] using collected
  unfold check
  simp only [weaken]
  rw [normalized]
  cases candidate <;>
    cases collectReads state (L.exprDeps guard.code) guard.schema guard.reads <;>
    try rfl
  dsimp only
  congr 2
  apply congrArg L.toBool
  apply congrArg (L.evalDeps guard.code)
  funext x τ h hx
  cases h <;> rfl

private theorem collectReads_failed_of_failed_read
    {Γ : SourceCtx Player L} {author : Player} (state : State L Γ)
    (deps : Finset VarId) (schema : Ctx L.Ty)
    (reads : ∀ {x τ}, HasVar schema x τ → SourceGuardRead Γ author τ)
    {x : VarId} {τ : L.Ty} (h : HasVar schema x τ) (supported : x ∈ deps)
    (failed : (reads h).get state = .failed) :
    collectReads state deps schema reads = .failed := by
  induction schema with
  | nil => exact nomatch h
  | cons entry tail ih =>
      obtain ⟨name, σ⟩ := entry
      cases h with
      | here => simp [collectReads, supported, failed]
      | there h =>
          have tailFailed := ih (fun h => reads (.there h)) h failed
          by_cases member : name ∈ deps
          · cases hhead : (reads (.here : HasVar ((name, σ) :: tail) name σ)).get state <;>
              simp [collectReads, member, hhead, tailFailed]
          · simp [collectReads, member, tailFailed]

/-- A failed statically supported read discharges a guard vacuously, regardless
of the subject's current status. -/
theorem check_satisfied_of_failed_read
    {Γ : SourceCtx Player L} {subject : VarId} {payload : L.Ty}
    {author : Player} (guard : SourceGuard L Γ author subject payload)
    (candidate : Publication (L.Val payload)) (state : State L Γ)
    {x : VarId} {τ : L.Ty} (h : HasVar guard.schema x τ)
    (supported : x ∈ L.exprDeps guard.code)
    (failed : (guard.reads h).get state = .failed) :
    guard.check candidate state = .satisfied := by
  have collected := collectReads_failed_of_failed_read state
    (L.exprDeps guard.code) guard.schema guard.reads h supported failed
  cases candidate <;> simp [check, collected]

private theorem collectReads_terminal
    {Γ : SourceCtx Player L} {author : Player} (state : State L Γ)
    (deps : Finset VarId) (schema : Ctx L.Ty)
    (reads : ∀ {x τ}, HasVar schema x τ → SourceGuardRead Γ author τ)
    (terminal : ∀ {x τ} (h : HasVar schema x τ), x ∈ deps →
      (reads h).get state ≠ .pending) :
    collectReads state deps schema reads = .failed ∨
      ∃ get, collectReads state deps schema reads = .ready get := by
  induction schema with
  | nil =>
      let get : ∀ {x τ}, HasVar ([] : Ctx L.Ty) x τ → x ∈ deps → L.Val τ :=
        fun h _ => nomatch h
      exact Or.inr ⟨get, rfl⟩
  | cons entry tail ih =>
      obtain ⟨name, τ⟩ := entry
      have tailTerminal : ∀ {x σ} (h : HasVar tail x σ), x ∈ deps →
          (reads (.there h)).get state ≠ .pending :=
        fun h hx => terminal (.there h) hx
      rcases ih (fun h => reads (.there h)) tailTerminal with tailFailed | ⟨tailGet, tailReady⟩
      · exact Or.inl (by
          by_cases member : name ∈ deps
          · cases hhead : (reads (.here : HasVar ((name, τ) :: tail) name τ)).get state <;>
              simp [collectReads, member, hhead, tailFailed]
          · simp [collectReads, member, tailFailed])
      · by_cases member : name ∈ deps
        · have headTerminal := terminal
            (.here : HasVar ((name, τ) :: tail) name τ) member
          cases hhead : (reads (.here : HasVar ((name, τ) :: tail) name τ)).get state with
          | pending => exact False.elim (headTerminal hhead)
          | failed => exact Or.inl (by simp [collectReads, member, hhead])
          | value value =>
              let get : ∀ {x σ}, HasVar ((name, τ) :: tail) x σ →
                  x ∈ deps → L.Val σ := fun h hx => match h with
                | .here => value
                | .there h => tailGet h hx
              refine Or.inr ⟨get, ?_⟩
              simp only [collectReads, dif_pos member, hhead, tailReady]
              apply congrArg ReadOutcome.ready
              funext x σ h hx
              cases h <;> rfl
        · let get : ∀ {x σ}, HasVar ((name, τ) :: tail) x σ →
              x ∈ deps → L.Val σ := fun h hx => match h with
            | .here => False.elim (member hx)
            | .there h => tailGet h hx
          refine Or.inr ⟨get, ?_⟩
          simp only [collectReads, dif_neg member, tailReady]
          apply congrArg ReadOutcome.ready
          funext x σ h hx
          cases h <;> rfl

/-- Once the subject and every statically supported read are terminal, checking
terminates with either satisfaction or rejection. Failures count as terminal
and discharge the guard vacuously. -/
theorem check_ne_pending_of_support_resolved
    {Γ : SourceCtx Player L} {subject : VarId} {payload : L.Ty}
    {author : Player} (guard : SourceGuard L Γ author subject payload)
    (candidate : Publication (L.Val payload)) (state : State L Γ)
    (subjectResolved : candidate ≠ .pending)
    (supportResolved : ∀ {x τ} (h : HasVar guard.schema x τ),
      x ∈ L.exprDeps guard.code → (guard.reads h).get state ≠ .pending) :
    guard.check candidate state ≠ .pending := by
  rcases collectReads_terminal state (L.exprDeps guard.code) guard.schema
    guard.reads supportResolved with failed | ⟨get, ready⟩
  · cases candidate <;> simp_all [check]
  · cases candidate with
    | pending => exact False.elim (subjectResolved rfl)
    | failed => simp [check]
    | value value =>
        simp only [check, ready]
        split <;> decide

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
