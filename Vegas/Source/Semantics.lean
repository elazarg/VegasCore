/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Basic
import GameTheory.Core.Form

/-! # Source policies and exact execution

Observation-local policies choose immutable bindings and disclosure decisions.
Execution follows source order, retains typed guard obligations, and interprets
chance through the exact finite law carried by source syntax.  The game form's
outcome is the detailed terminal state; `evaluatePayoffs` is a separate,
explicit settlement projection and does not itself impose utilities.
-/

noncomputable section
namespace Vegas
open GameTheory GameTheory.Math.Probability Interaction

def sourcePublicEnv {Player : Type} {L : IExpr} [R : IExpr.ResultTypes L] :
    {Γ : SourceCtx Player L} → State L Γ → Env L.Val (SourcePublicCtx L Γ)
  | [], _ => Env.empty L.Val
  | (_, .publicData _) :: _, s => Env.cons (s.get .here)
      (sourcePublicEnv fun _ _ h => s.get (HasVar.there h))
  | (_, .privateData _ _) :: tail, s => sourcePublicEnv (Player := Player) (L := L)
      (R := R) (Γ := tail) (fun _ _ h => s.get (HasVar.there h))
  | (_, .publication τ) :: _, s =>
      Env.cons ((R.valueEquiv τ).symm (s.get .here))
        (sourcePublicEnv fun _ _ h => s.get (HasVar.there h))

def SourceObservationVal {Player : Type} (L : IExpr) :
    CellTy Player L → Type
  | .publicData τ => L.Val τ
  | .publication τ => PublicationResult (L.Val τ)
  | .privateData owner τ => Option (CellVal L (.privateData owner τ))

structure SourceObservation {Player : Type} (L : IExpr) (who : Player)
    (Γ : SourceCtx Player L) where
  cells : Env (SourceObservationVal L) Γ

def sourceObserve {Player : Type} [DecidableEq Player] {L : IExpr} (who : Player) :
    {Γ : SourceCtx Player L} → State L Γ → SourceObservation L who Γ
  | _, s => ⟨fun _ cell h => match cell with
      | .publicData _ => s.get h
      | .publication _ => s.get h
      | .privateData owner _ => if owner = who then some (s.get h) else none⟩

namespace SourceProgram
variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
variable {Γ : SourceCtx Player L} {O : Finset VarId} {name x : VarId} {owner : Player}
variable {payload : L.Ty} {c : CellTy Player L}

inductive OwnAction (Player : Type) (L : IExpr) where
  | commit (owner : Player) (name : VarId) (payload : L.Ty) (choice : BoundValue (L.Val payload))
  | reveal (owner : Player) (name : VarId) (disclose : Bool)

abbrev History (Player : Type) (L : IExpr) := Player → List (OwnAction Player L)
abbrev DecisionView (who : Player) (Γ : SourceCtx Player L) :=
  SourceObservation L who Γ × List (OwnAction Player L)

def BehavioralPolicy (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    SourceProgram Player L Γ O → Type
  | _, _, .ret _ => PUnit
  | _, _, .sample _ _ _ k => BehavioralPolicy who k
  | Γ, _, .commit (payload := payload) _ owner _ _ k =>
      ((owner = who) → DecisionView who Γ →
        FinDist (BoundValue (L.Val payload))) × BehavioralPolicy who k
  | Γ, _, .reveal _ owner _ _ _ _ k =>
      ((owner = who) → DecisionView who Γ → FinDist Bool) ×
        BehavioralPolicy who k

abbrev BehavioralProfile {Γ : SourceCtx Player L} {O : Finset VarId}
    (p : SourceProgram Player L Γ O) := ∀ who, BehavioralPolicy who p

/-- Failure actions make the policy space inhabited without any payload or
guard satisfiability assumption. -/
def failurePolicy (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (p : SourceProgram Player L Γ O) → BehavioralPolicy who p
  | _, _, .ret _ => PUnit.unit
  | _, _, .sample _ _ _ k => failurePolicy who k
  | _, _, .commit _ _ _ _ k =>
      (fun _ _ => FinDist.pure (BoundValue.unopenable _), failurePolicy who k)
  | _, _, .reveal _ _ _ _ _ _ k =>
      (fun _ _ => FinDist.pure false, failurePolicy who k)

def failureProfile (p : SourceProgram Player L Γ O) : BehavioralProfile p :=
  fun who => failurePolicy who p

theorem behavioralProfile_nonempty (p : SourceProgram Player L Γ O) :
    Nonempty (BehavioralProfile p) := ⟨failureProfile p⟩

def afterSample {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst} {law : L.DistExpr (SourcePublicCtx L Γ) payload}
    {k : SourceProgram Player L ((name, .publicData payload) :: Γ) O}
    (p : BehavioralProfile (SourceProgram.sample name (payload := payload) fresh law k)) :
    BehavioralProfile k := fun who => p who
def afterCommit {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} {fresh : name ∉ Γ.map Prod.fst}
    {guard : SourceGuard L Γ owner name payload}
    {k : SourceProgram Player L ((name, .privateData owner payload) :: Γ) (insert name O)}
    (p : BehavioralProfile (SourceProgram.commit name owner (payload := payload) fresh guard k)) :
    BehavioralProfile k := fun who => (p who).2
def afterReveal {Γ : SourceCtx Player L} {O : Finset VarId} {published name : VarId}
    {owner : Player} {payload : L.Ty} {fresh : published ∉ Γ.map Prod.fst}
    {source : HasVar Γ name (.privateData owner payload)} {unresolved : name ∈ O}
    {k : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name)}
    (p : BehavioralProfile
      (SourceProgram.reveal published owner name (payload := payload) fresh source unresolved k)) :
    BehavioralProfile k := fun who => (p who).2

def commitKernel {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} {fresh : name ∉ Γ.map Prod.fst} {g : SourceGuard L Γ owner name payload}
    {k : SourceProgram Player L ((name, .privateData owner payload) :: Γ) (insert name O)}
    (p : BehavioralProfile (SourceProgram.commit name owner fresh g k)) :
    DecisionView owner Γ → FinDist (BoundValue (L.Val payload)) :=
  (p owner).1 rfl

def revealKernel {Γ : SourceCtx Player L} {O : Finset VarId} {published name : VarId}
    {owner : Player} {payload : L.Ty} {fresh : published ∉ Γ.map Prod.fst}
    {source : HasVar Γ name (.privateData owner payload)} {unresolved : name ∈ O}
    {k : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name)}
    (p : BehavioralProfile (SourceProgram.reveal published owner name fresh source unresolved k)) :
    DecisionView owner Γ → FinDist Bool :=
  (p owner).1 rfl

def terminalCtx : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    SourceProgram Player L Γ O → SourceCtx Player L
  | terminal, _, .ret _ => terminal
  | _, _, .sample _ _ _ k => terminalCtx k
  | _, _, .commit _ _ _ _ k => terminalCtx k
  | _, _, .reveal _ _ _ _ _ _ k => terminalCtx k

def terminalPayoffs : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (p : SourceProgram Player L Γ O) →
    List (Player × L.Expr (SourcePublicCtx L (terminalCtx p)) L.int)
  | _, _, .ret u => by simpa [terminalCtx] using u
  | _, _, .sample _ _ _ k => terminalPayoffs k
  | _, _, .commit _ _ _ _ k => terminalPayoffs k
  | _, _, .reveal _ _ _ _ _ _ k => terminalPayoffs k

structure Obligation (Γ : SourceCtx Player L) where
  owner : Player
  subject : VarId
  payload : L.Ty
  source : HasVar Γ subject (.privateData owner payload)
  guard : SourceGuard L Γ owner subject payload

def Obligation.check (o : Obligation (Player := Player) (L := L) Γ) (s : State L Γ) :=
  o.guard.check (s.get o.source |>.2) s

def Obligation.weaken {x c} (o : Obligation (Player := Player) (L := L) Γ) :
    Obligation ((x, c) :: Γ) where
  owner := o.owner; subject := o.subject; payload := o.payload
  source := .there o.source; guard := o.guard.weaken

omit [DecidableEq Player] [IExpr.ResultTypes L] in
@[simp] theorem Obligation.check_weaken {x c}
    (o : Obligation (Player := Player) (L := L) Γ)
    (head : CellVal L c) (s : State L Γ) :
    o.weaken.check (Env.cons (x := x) head s) = o.check s := by
  simp [Obligation.check, Obligation.weaken, SourceGuard.check_weaken]

abbrev Registry (Γ : SourceCtx Player L) := List (Obligation (Player := Player) (L := L) Γ)
def Registry.weaken {x c} (r : Registry (Player := Player) (L := L) Γ) : Registry ((x,c)::Γ) :=
  r.map Obligation.weaken
def Registry.ok (r : Registry (Player := Player) (L := L) Γ) (s : State L Γ) : Bool :=
  r.all fun o => o.check s != .rejected

omit [DecidableEq Player] [IExpr.ResultTypes L] in
@[simp] theorem Registry.ok_weaken {x c} (r : Registry (Player := Player) (L := L) Γ)
    (head : CellVal L c) (s : State L Γ) : r.weaken.ok (Env.cons (x := x) head s) = r.ok s := by
  induction r with
  | nil => rfl
  | cons head tail ih =>
      simp only [Registry.weaken, Registry.ok, List.map_cons, List.all_cons,
        Obligation.check_weaken]
      congr 1

def updatePrivate {owner payload name} : {Γ : SourceCtx Player L} → State L Γ →
    HasVar Γ name (.privateData owner payload) → Publication (L.Val payload) → State L Γ
  | _ :: _, s, .here, v => Env.cons ((s.get .here).1, v) (fun _ _ h => s.get (.there h))
  | _ :: _, s, .there h, v => Env.cons (s.get .here)
      (updatePrivate (fun _ _ h' => s.get (.there h')) h v)

def boundResult {owner payload name} (s : State L Γ)
    (h : HasVar Γ name (.privateData owner payload)) (disclose : Bool) :
    PublicationResult (L.Val payload) :=
  match hb : (s.get h).1.binding with
  | .unbound => False.elim ((s.get h).1.isBound hb)
  | .unopenable => .failure
  | .value a => if disclose then .success a else .failure

/-- Resolving a retained binding either returns its stored result or failure,
according to the disclosure decision. -/
theorem boundResult_eq_resultEquiv {Player : Type} {L : IExpr}
    {Γ : SourceCtx Player L} {owner : Player} {payload : L.Ty} {name : VarId}
    (state : State L Γ)
    (source : HasVar Γ name (.privateData owner payload))
    (disclose : Bool) :
    boundResult state source disclose =
      if disclose then BoundValue.resultEquiv _ (state.get source).1 else .failure := by
  let propose : BoundValue (L.Val payload) → PublicationResult (L.Val payload) :=
    fun value => match hb : value.binding with
      | .unbound => False.elim (value.isBound hb)
      | .unopenable => .failure
      | .value data => if disclose then .success data else .failure
  change propose (state.get source).1 =
    if disclose then BoundValue.resultEquiv _ (state.get source).1 else .failure
  generalize (state.get source).1 = value
  rcases value with ⟨binding, bound⟩
  cases binding with
  | unbound => exact False.elim (bound rfl)
  | unopenable => cases disclose <;> rfl
  | value value => cases disclose <;> rfl

def resultPublication {A : Type} : PublicationResult A → Publication A
  | .failure => .failed
  | .success a => .value a

@[simp] theorem resultPublication_ne_pending {A : Type} (result : PublicationResult A) :
    resultPublication result ≠ .pending := by cases result <;> simp [resultPublication]

def runWith : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (p : SourceProgram Player L Γ O) → BehavioralProfile p → State L Γ →
    Registry Γ → History Player L → FinDist (State L (terminalCtx p))
  | _, _, .ret _, _, s, _, _ => FinDist.pure s
  | _, _, .sample _ _ d k, profile, s, r, history =>
      (L.evalDist d (sourcePublicEnv s)).bind fun a =>
        runWith k (afterSample profile) (Env.cons a s) r.weaken history
  | _, _, .commit name owner _ g k, profile, s, r, history =>
      (commitKernel profile (sourceObserve owner s, history owner)).bind fun b =>
        let s' := Env.cons (b, Publication.pending) s
        let obligation : Obligation _ :=
          { owner := owner, subject := name, payload := _, source := .here, guard := g.weaken }
        let history' := Function.update history owner
          (history owner ++ [OwnAction.commit owner name _ b])
        runWith k (afterCommit profile) s' (obligation :: r.weaken) history'
  | _, _, .reveal _ owner name _ h _ k, profile, s, r, history =>
      (revealKernel profile (sourceObserve owner s, history owner)).bind fun disclose =>
        let proposedResult := boundResult s h disclose
        let proposed := resultPublication proposedResult
        let tentative := updatePrivate s h proposed
        let acceptedResult := if r.ok tentative then proposedResult else PublicationResult.failure
        let accepted := resultPublication acceptedResult
        let resolved := updatePrivate s h accepted
        let history' := Function.update history owner
          (history owner ++ [OwnAction.reveal owner name disclose])
        runWith k (afterReveal profile) (Env.cons acceptedResult resolved) r.weaken history'

def run (p : SourceProgram Player L Γ O) (profile : BehavioralProfile p) (s : State L Γ) :=
  runWith p profile s [] (fun _ => [])

def Initial.run (initial : Initial (Player := Player) (L := L))
    (profile : BehavioralProfile initial.program) :=
  SourceProgram.run initial.program profile initial.state

def gameSignature (p : SourceProgram Player L Γ O) : GameSignature Player where
  Strategy := fun who => BehavioralPolicy who p
  Outcome := State L (terminalCtx p)

def gameForm (p : SourceProgram Player L Γ O) (s : State L Γ) :
    GameForm Player where
  sig := gameSignature p
  play profile := run p profile s

def evaluatePayoffs (p : SourceProgram Player L Γ O)
    (s : State L (terminalCtx p)) : List (Player × Int) :=
  (terminalPayoffs p).map fun e =>
    (e.1, L.toInt (L.eval e.2 (sourcePublicEnv s)))

end SourceProgram
end Vegas
