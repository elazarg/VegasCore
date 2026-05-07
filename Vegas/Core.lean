import Vegas.FWeight

/-!
# Generic protocol interface

This file records the generic value and protocol interface on which the Vegas
development is built.

## Architecture

The file separates **the embedded language** (`IExpr`) from **the protocol
structure** (`VCtx`, `VegasCore`), with **erasure** as the bridge between them.

* `IExpr` packages the concrete expression layer: types, values, expression
  syntax, distribution syntax, evaluation, dependency tracking, and the
  soundness laws that justify treating `exprDeps` as a static
  over-approximation of semantic dependence.

* The visibility-aware protocol structure (`BindTy`, `VCtx`, `VHasVar`,
  `VEnv`) is generic over `IExpr`. Each binding carries an immutable base type
  plus visibility metadata: `.pub τ` is visible to all, while
  `.hidden owner τ` is visible only to its owner.

* Two projections move between contexts: `viewVCtx p Γ` (what `p` can see)
  and `pubVCtx Γ` (the public-only fragment). Each has a matching erasure
  into a plain `Ctx L.Ty` consumed by `IExpr.eval`/`IExpr.evalDist`.

* `VegasCore` (the syntax) and the per-constructor environments encode a
  single design commitment: **two erased contexts.** `letExpr`, `sample`,
  and payoff expressions are typed over `erasePubVCtx Γ` (public state
  only); commit guards and operational kernels are typed over `eraseVCtx Γ`
  (full state). The narrower constraint that a commit guard depends only on
  the *committing player's* view is enforced semantically in `Scope.lean`.

## Notes

* `HasVar` is `Type`, not `Prop`, because `Env` pattern-matches on it. The
  resulting need to handle proof-position equality is paid for once by
  `Env.get_eq_of_nodup`.
* Finiteness is opt-in and program-local. The finite game APIs require
  evidence that the operational domains used by a particular checked program
  are finite; payoff expressions may still return unbounded integers.
-/

namespace Vegas

/-! ## Plain typed contexts -/

/-- Variable identifiers for both plain and visibility-tagged contexts. -/
abbrev VarId : Type := Nat

/-- A plain typed context indexed by variable identifiers. -/
abbrev Ctx (Ty : Type) := List (VarId × Ty)

/-- Typed membership in a plain context. -/
inductive HasVar {Ty : Type} : Ctx Ty → VarId → Ty → Type where
  | here {Γ x τ} : HasVar ((x, τ) :: Γ) x τ
  | there {Γ x y τ τ'} : HasVar Γ x τ → HasVar ((y, τ') :: Γ) x τ

/-- Runtime environments for plain contexts. -/
def Env {Ty : Type} (Val : Ty → Type) : Ctx Ty → Type :=
  fun Γ => ∀ x τ, HasVar Γ x τ → Val τ

/-- A `HasVar` proof witnesses that `x` appears in the context's name list. -/
theorem HasVar.mem_map_fst {Ty : Type} {Γ : Ctx Ty} {x : VarId} {τ : Ty}
    (h : HasVar Γ x τ) : x ∈ Γ.map Prod.fst := by
  induction h with
  | here => simp
  | there _ ih => simp [ih]

/-- In a context with unique names, `HasVar` is a subsingleton:
any two proofs of `HasVar Γ x τ` are equal. -/
theorem HasVar.eq_of_nodup {Ty : Type} {Γ : Ctx Ty} {x : VarId} {τ : Ty}
    (hnodup : (Γ.map Prod.fst).Nodup)
    (h₁ h₂ : HasVar Γ x τ) : h₁ = h₂ := by
  induction h₁ with
  | @here Γ' y σ =>
    cases h₂ with
    | here => rfl
    | @there _ _ _ _ σ' h₂' =>
      have hnd := List.nodup_cons.mp hnodup
      exact absurd h₂'.mem_map_fst hnd.1
  | @there Γ' y z σ σ' h₁' ih =>
    cases h₂ with
    | @here =>
      have hnd := List.nodup_cons.mp hnodup
      exact absurd h₁'.mem_map_fst hnd.1
    | @there _ _ _ _ _ h₂' =>
      have hnd := List.nodup_cons.mp hnodup
      exact congrArg HasVar.there (ih hnd.2 h₂')

/-- In a context with unique names, `HasVar` determines the type:
if `HasVar Γ x τ₁` and `HasVar Γ x τ₂`, then `τ₁ = τ₂`. -/
theorem HasVar.type_unique {Ty : Type} {Γ : Ctx Ty} {x : VarId} {τ₁ τ₂ : Ty}
    (hnodup : (Γ.map Prod.fst).Nodup)
    (h₁ : HasVar Γ x τ₁) (h₂ : HasVar Γ x τ₂) : τ₁ = τ₂ := by
  induction h₁ with
  | here =>
    cases h₂ with
    | here => rfl
    | there h₂' =>
      exact absurd h₂'.mem_map_fst (List.nodup_cons.mp hnodup).1
  | there h₁' ih =>
    cases h₂ with
    | here =>
      exact absurd h₁'.mem_map_fst (List.nodup_cons.mp hnodup).1
    | there h₂' =>
      exact ih (List.nodup_cons.mp hnodup).2 h₂'

/-- In a context with unique names, `Env` lookups are proof-irrelevant:
the value depends only on `x` and `τ`, not on the `HasVar` proof. -/
theorem Env.get_eq_of_nodup {Ty : Type} {Val : Ty → Type} {Γ : Ctx Ty}
    {x : VarId} {τ : Ty}
    (hnodup : (Γ.map Prod.fst).Nodup)
    (env : Env Val Γ) (h₁ h₂ : HasVar Γ x τ) :
    env x τ h₁ = env x τ h₂ := by
  rw [HasVar.eq_of_nodup hnodup h₁ h₂]

/-- Construct a `HasVar` from list membership. Recurses on the context and
case-splits on entry equality at each step, so `[DecidableEq Ty]` is needed
to extract computational data from the `Prop`-valued membership proof. The
sole in-tree call site has `Ty = L.Ty` for `L : IExpr`, where `decEqTy` is
already an instance. -/
def HasVar.ofMem {Ty : Type} [DecidableEq Ty] {Γ : Ctx Ty}
    {x : VarId} {τ : Ty} (h : (x, τ) ∈ Γ) : HasVar Γ x τ := by
  induction Γ with
  | nil => exact absurd h (by simp)
  | cons a Γ' ih =>
    by_cases heq : a = (x, τ)
    · subst heq; exact .here
    · exact .there (ih (List.mem_of_ne_of_mem (Ne.symm heq) h))

namespace Env

def empty {Ty : Type} (Val : Ty → Type) : Env Val ([] : Ctx Ty) :=
  fun _ _ h => nomatch h

def cons {Ty : Type} {Val : Ty → Type} {Γ : Ctx Ty} {x : VarId} {τ : Ty}
    (v : Val τ) (env : Env Val Γ) : Env Val ((x, τ) :: Γ) :=
  fun _ _ h =>
    match h with
    | .here => v
    | .there h' => env _ _ h'

def get {Ty : Type} {Val : Ty → Type} {Γ : Ctx Ty} {x : VarId} {τ : Ty}
    (env : Env Val Γ) (h : HasVar Γ x τ) : Val τ :=
  env x τ h

@[simp] theorem cons_get_here {Ty : Type} {Val : Ty → Type} {Γ : Ctx Ty}
    {x : VarId} {τ : Ty} {v : Val τ} {env : Env Val Γ} :
    (Env.cons v env).get (HasVar.here (x := x)) = v := rfl

@[simp] theorem cons_get_there {Ty : Type} {Val : Ty → Type} {Γ : Ctx Ty}
    {x y : VarId} {τ σ : Ty} {v : Val τ} {env : Env Val Γ}
    {h : HasVar Γ y σ} :
    (Env.cons (x := x) v env).get (HasVar.there h) = env.get h := rfl

theorem cons_ext {Ty : Type} {Val : Ty → Type} {Γ : Ctx Ty}
    {x : VarId} {τ : Ty}
    {v₁ v₂ : Val τ} {env₁ env₂ : Env Val Γ}
    (hv : v₁ = v₂) (henv : env₁ = env₂) :
    cons (x := x) v₁ env₁ = cons (x := x) v₂ env₂ := by
  subst hv; subst henv; rfl

end Env

/-! ## Variable agreement and dependency vocabulary -/

/-- Two environments agree on a set of variable identifiers. The vocabulary
in which `IExpr`'s dependency-soundness laws are phrased: if two environments
agree on `exprDeps e`, then `e` evaluates the same way in both. The
visibility-aware specialization `ObsEq` (defined in `Scope.lean`) restricts
the agreement set to the variables visible to a given player. -/
def AgreesOn {Ty : Type} {Val : Ty → Type} {Γ : Ctx Ty}
    (ρ₁ ρ₂ : Env Val Γ) (xs : Finset VarId) : Prop :=
  ∀ x τ (h : HasVar Γ x τ), x ∈ xs → ρ₁ x τ h = ρ₂ x τ h

/-- Narrowing the agreement set preserves agreement. -/
theorem AgreesOn.mono {Ty : Type} {Val : Ty → Type} {Γ : Ctx Ty}
    {ρ₁ ρ₂ : Env Val Γ} {S T : Finset VarId}
    (h : AgreesOn ρ₁ ρ₂ T) (hST : S ⊆ T) : AgreesOn ρ₁ ρ₂ S :=
  fun x τ hx hm => h x τ hx (hST hm)

/-! ## The expression-language interface `IExpr` -/

/-- Core PL interface for the Vegas layer.

Packages the concrete expression layer: types, values, expression syntax,
distribution syntax, evaluation functions, dependency tracking, and
dependency-soundness laws. Expressions and distributions are typed over plain
`Ctx Ty` (no visibility annotations) — visibility is layered separately by the
`VCtx` family below.

The interface is dimensioned to the metatheory it supports: every field is
exercised by a downstream theorem, and the two structural laws
(`extendAfterHead`, `dropAfterHead`) exist for exactly one family of results
(commit-commit commutativity in `TraceSemantics.lean`). -/
structure IExpr where
  /-- The universe of types in the embedded language. -/
  Ty : Type
  /-- Semantic interpretation: the values inhabiting each type. -/
  Val : Ty → Type
  decEqTy : DecidableEq Ty
  decEqVal : ∀ {τ : Ty}, DecidableEq (Val τ)
  /-- A distinguished Boolean-representing type. Used for commit guards. -/
  bool : Ty
  /-- Project a value of `bool` into Lean's `Bool`. -/
  toBool : Val bool → Bool
  /-- A distinguished integer-representing type. Used for per-player payoffs. -/
  int : Ty
  /-- Project a value of `int` into Lean's `Int`. -/
  toInt : Val int → Int
  /-- Typed expression syntax. -/
  Expr : Ctx Ty → Ty → Type
  /-- Denotational evaluation. -/
  eval : {Γ : Ctx Ty} → {τ : Ty} → Expr Γ τ → Env Val Γ → Val τ
  /-- A static over-approximation of the variables an expression reads.
  Sound by `expr_deps_sound`. -/
  exprDeps : {Γ : Ctx Ty} → {τ : Ty} → Expr Γ τ → Finset VarId
  /-- Weakening: an expression over `(x, τ) :: Γ` can be retyped over
  `(x, τ) :: (y, σ) :: Γ` without changing its meaning. The first of two
  structural laws supporting commit-commit commutativity. -/
  extendAfterHead :
    ∀ {Γ : Ctx Ty} {x y : VarId} {τ σ b : Ty}
      (e : Expr ((x, τ) :: Γ) b),
      ∃ e' : Expr ((x, τ) :: (y, σ) :: Γ) b,
        ∀ (vx : Val τ) (vy : Val σ) (env : Env Val Γ),
          eval e' (Env.cons (x := x) vx (Env.cons (x := y) vy env)) =
            eval e (Env.cons (x := x) vx env)
  /-- Strengthening: an expression that does not depend on `y` can be
  re-expressed without `y` in its context. The companion to
  `extendAfterHead`. -/
  dropAfterHead :
    ∀ {Γ : Ctx Ty} {x y : VarId} {τ σ b : Ty}
      (e : Expr ((x, τ) :: (y, σ) :: Γ) b),
      y ∉ exprDeps e →
      ∃ e' : Expr ((x, τ) :: Γ) b,
        ∀ (vx : Val τ) (vy : Val σ) (env : Env Val Γ),
          eval e' (Env.cons (x := x) vx env) =
            eval e (Env.cons (x := x) vx (Env.cons (x := y) vy env))
  /-- Typed distribution syntax. -/
  DistExpr : Ctx Ty → Ty → Type
  /-- Denotational evaluation of a distribution into `FWeight (Val τ)`. -/
  evalDist : {Γ : Ctx Ty} → {τ : Ty} →
    DistExpr Γ τ → Env Val Γ → @FWeight (Val τ) decEqVal
  /-- Static over-approximation of variables a distribution reads. -/
  distDeps : {Γ : Ctx Ty} → {τ : Ty} → DistExpr Γ τ → Finset VarId
  /-- Soundness of `exprDeps`: if two environments agree on the declared
  dependency set, `eval` produces equal results. The semantic justification
  for treating `exprDeps` as a usable dependency tracker. -/
  expr_deps_sound :
    ∀ {Γ : Ctx Ty} {τ : Ty} (e : Expr Γ τ) (ρ₁ ρ₂ : Env Val Γ),
      AgreesOn ρ₁ ρ₂ (exprDeps e) → eval e ρ₁ = eval e ρ₂
  /-- Soundness of `distDeps`. -/
  dist_deps_sound :
    ∀ {Γ : Ctx Ty} {τ : Ty} (d : DistExpr Γ τ) (ρ₁ ρ₂ : Env Val Γ),
      AgreesOn ρ₁ ρ₂ (distDeps d) → evalDist d ρ₁ = evalDist d ρ₂

-- Promote the `decEqTy` and `decEqVal` interface fields to instances. After
-- this, `DecidableEq (L.Val τ)` is automatically available for any `L : IExpr`,
-- which is what lets `FWeight (L.Val τ)` and similar `Finsupp`-backed
-- constructions type-check downstream.
attribute [instance] IExpr.decEqTy IExpr.decEqVal

/-! ## Visibility-tagged contexts -/

/-- Visibility metadata for a binding.

This is deliberately separate from the binding's base type: reveal-like
operations change visibility, while the type associated with a variable name is
an immutable typing fact. The information model is *owner-or-all*: a secret
either belongs to one player, or it is visible to everyone. There is no
group-visibility constructor. -/
inductive Visibility (Player : Type) where
  | pub
  | hidden (owner : Player)
  deriving DecidableEq

namespace Visibility

/-- Owner recorded in visibility metadata, if the binding is hidden. -/
def owner {Player : Type} : Visibility Player → Option Player
  | .pub => none
  | .hidden owner => some owner

@[simp] theorem owner_pub {Player : Type} :
    owner (.pub : Visibility Player) = none := rfl

@[simp] theorem owner_hidden {Player : Type} (owner : Player) :
    Visibility.owner (.hidden owner) = some owner := rfl

/-- Can player `p` observe this visibility class? -/
def canSee {Player : Type} [DecidableEq Player]
    (p : Player) : Visibility Player → Bool
  | .pub => true
  | .hidden owner => decide (p = owner)

@[simp] theorem canSee_pub {Player : Type} [DecidableEq Player] (p : Player) :
    canSee p (.pub : Visibility Player) = true := rfl

@[simp] theorem canSee_hidden {Player : Type} [DecidableEq Player]
    (p owner : Player) :
    canSee p (.hidden owner : Visibility Player) = decide (p = owner) := rfl

end Visibility

/-- Visibility-aware binding type over an abstract language.

The representation is factored into an immutable `base` type and independent
visibility metadata. Code should construct bindings explicitly as
`⟨base, visibility⟩`, so places that change visibility do not look like they
also changed the underlying type. -/
structure BindTy (Player : Type) (L : IExpr) where
  base : L.Ty
  visibility : Visibility Player
  deriving DecidableEq

namespace BindTy

/-- Smart constructor for a public binding. Keeps call sites close to the old
`.pub τ` shape while preserving the split representation internally. -/
abbrev pub {Player : Type} {L : IExpr} (τ : L.Ty) : BindTy Player L :=
  ⟨τ, Visibility.pub⟩

/-- Smart constructor for a hidden binding owned by `owner`. -/
abbrev hidden {Player : Type} {L : IExpr} (owner : Player) (τ : L.Ty) :
    BindTy Player L :=
  ⟨τ, Visibility.hidden owner⟩

/-- Owner of a binding, if it is hidden. Public bindings have no owner. -/
abbrev owner {Player : Type} {L : IExpr} (τ : BindTy Player L) : Option Player :=
  τ.visibility.owner

/-- Whether a binding is statically public. -/
abbrev isPublic {Player : Type} {L : IExpr} (τ : BindTy Player L) : Prop :=
  τ.visibility = .pub

@[simp] theorem owner_public {Player : Type} {L : IExpr} (τ : L.Ty) :
    (.pub τ : BindTy Player L).owner = none := rfl

@[simp] theorem owner_hidden {Player : Type} {L : IExpr}
    (owner : Player) (τ : L.Ty) :
    (.hidden owner τ : BindTy Player L).owner = some owner := rfl

end BindTy

/-- Visibility-tagged contexts indexed by variable identifiers. -/
abbrev VCtx (Player : Type) (L : IExpr) : Type :=
  List (VarId × BindTy Player L)

/-- Typed membership in a visibility-tagged context. Definitionally
`HasVar Γ x τ` specialized to `Ctx (BindTy Player L)`; the abbreviation
preserves the readable name and the dot-notation namespace. -/
abbrev VHasVar {Player : Type} {L : IExpr}
    (Γ : VCtx Player L) (x : VarId) (τ : BindTy Player L) : Type :=
  HasVar Γ x τ

/-- The "head" position in a visibility context. -/
abbrev VHasVar.here {Player : Type} {L : IExpr} {Γ : VCtx Player L}
    {x : VarId} {τ : BindTy Player L} : VHasVar ((x, τ) :: Γ) x τ :=
  HasVar.here

/-- Skip past a context entry to a position deeper in. -/
abbrev VHasVar.there {Player : Type} {L : IExpr} {Γ : VCtx Player L}
    {x y : VarId} {τ τ' : BindTy Player L}
    (h : VHasVar Γ x τ) : VHasVar ((y, τ') :: Γ) x τ :=
  HasVar.there h

/-- Runtime environments for visibility-tagged contexts. -/
def VEnv {Player : Type} (L : IExpr) : VCtx Player L → Type :=
  fun Γ => ∀ x τ, VHasVar Γ x τ → L.Val τ.base

namespace VEnv

def empty {Player : Type} (L : IExpr) : VEnv (Player := Player) L [] :=
  fun _ _ h => nomatch h

def cons {Player : Type} {L : IExpr} {Γ : VCtx Player L} {x : VarId}
    {τ : BindTy Player L}
    (v : L.Val τ.base) (env : VEnv L Γ) :
    VEnv (Player := Player) L ((x, τ) :: Γ) :=
  fun _ _ h =>
    match h with
    | .here => v
    | .there h' => env _ _ h'

theorem cons_ext {Player : Type} {L : IExpr} {Γ : VCtx Player L}
    {x : VarId} {τ : BindTy Player L}
    {v₁ v₂ : L.Val τ.base} {env₁ env₂ : VEnv L Γ}
    (hv : v₁ = v₂) (henv : env₁ = env₂) :
    cons (x := x) v₁ env₁ = cons (x := x) v₂ env₂ := by
  subst hv; subst henv; rfl

theorem cons_head_eq_of_eq {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} {x : VarId} {τ : BindTy Player L}
    {v₁ v₂ : L.Val τ.base} {env₁ env₂ : VEnv L Γ}
    (h : cons (x := x) v₁ env₁ = cons (x := x) v₂ env₂) :
    v₁ = v₂ := by
  exact congrFun (congrFun (congrFun h x) τ) VHasVar.here

theorem cons_tail_eq_of_eq {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} {x : VarId} {τ : BindTy Player L}
    {v₁ v₂ : L.Val τ.base} {env₁ env₂ : VEnv L Γ}
    (h : cons (x := x) v₁ env₁ = cons (x := x) v₂ env₂) :
    env₁ = env₂ := by
  funext y σ hy
  exact congrFun (congrFun (congrFun h y) σ) (VHasVar.there hy)

def get {Player : Type} {L : IExpr} {Γ : VCtx Player L} {x : VarId}
    {τ : BindTy Player L}
    (env : VEnv L Γ) (h : VHasVar Γ x τ) :
    L.Val τ.base :=
  env x τ h

def tail {Player : Type} {L : IExpr} {Γ : VCtx Player L} {x : VarId}
    {τ : BindTy Player L}
    (env : VEnv L ((x, τ) :: Γ)) : VEnv L Γ :=
  fun y σ h => env y σ (VHasVar.there h)

@[simp] theorem tail_cons {Player : Type} {L : IExpr} {Γ : VCtx Player L}
    {x : VarId} {τ : BindTy Player L}
    {v : L.Val τ.base} {env : VEnv L Γ} :
    tail (x := x) (τ := τ) (cons v env) = env := rfl

@[simp] theorem cons_get_here {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} {x : VarId} {τ : BindTy Player L}
    {v : L.Val τ.base} {env : VEnv L Γ} :
    (VEnv.cons v env).get (VHasVar.here (Γ := Γ) (x := x) (τ := τ)) = v := rfl

@[simp] theorem cons_get_there {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} {x y : VarId} {τ σ : BindTy Player L}
    {v : L.Val τ.base} {env : VEnv L Γ}
    {h : VHasVar Γ y σ} :
    (VEnv.cons (x := x) v env).get (VHasVar.there h) = env.get h := rfl

/-- In a context with unique names, `VEnv.get` is proof-irrelevant:
the value depends only on `x` and `τ`, not on the `VHasVar` proof. The
visibility-aware analogue of `Env.get_eq_of_nodup`. -/
theorem get_eq_of_nodup {Player : Type} {L : IExpr} {Γ : VCtx Player L}
    {x : VarId} {τ : BindTy Player L}
    (hnodup : (Γ.map Prod.fst).Nodup)
    (env : VEnv L Γ) (h₁ h₂ : VHasVar Γ x τ) :
    env.get h₁ = env.get h₂ := by
  rw [HasVar.eq_of_nodup hnodup h₁ h₂]

end VEnv

/-! ## Views and public projection -/

/-- Can player `p` observe a binding of type `τ`? True for public bindings
and for hidden bindings owned by `p`. -/
abbrev canSee {Player : Type} [DecidableEq Player] {L : IExpr}
    (p : Player) (τ : BindTy Player L) : Bool :=
  τ.visibility.canSee p

/-- Player-local visible subcontext. -/
def viewVCtx {Player : Type} [DecidableEq Player] {L : IExpr}
    (p : Player) : VCtx Player L → VCtx Player L
  | [] => []
  | (x, τ) :: Γ =>
      if canSee p τ then (x, τ) :: viewVCtx p Γ else viewVCtx p Γ

/-- The view's name set is contained in the full context's name set: anything
visible to `p` is in the original context. -/
theorem viewVCtx_map_fst_sub {Player : Type} [DecidableEq Player] {L : IExpr}
    {x : VarId} {p : Player} {Γ : VCtx Player L} :
    x ∈ (viewVCtx p Γ).map Prod.fst → x ∈ Γ.map Prod.fst := by
  induction Γ with
  | nil =>
    intro h
    simp [viewVCtx] at h
  | cons hd tl ih =>
    obtain ⟨y, τ⟩ := hd
    cases hsee : canSee (Player := Player) (L := L) p τ with
    | false =>
      intro h
      have hview : viewVCtx p ((y, τ) :: tl) = viewVCtx p tl := by
        simp [viewVCtx, hsee]
      rw [hview] at h
      exact List.mem_cons_of_mem _ (ih h)
    | true =>
      intro h
      have hview : viewVCtx p ((y, τ) :: tl) = (y, τ) :: viewVCtx p tl := by
        simp [viewVCtx, hsee]
      rw [hview] at h
      simp only [List.map, List.mem_cons] at h ⊢
      rcases h with rfl | htl
      · exact Or.inl rfl
      · exact Or.inr (ih htl)

namespace VHasVar

/-- Lift a `VHasVar` proof in `viewVCtx p Γ` to a `VHasVar` in `Γ`. Composes
with `HasVar.toVHasVar` and `VHasVar.toErased` inside `projectViewEnv`
(`Vegas.ViewKernel`) to project a full erased environment to its
view-restricted erased form. -/
def ofViewVCtx {Player : Type} [DecidableEq Player] {L : IExpr}
    {p : Player} {Γ : VCtx Player L} {x : VarId} {τ : BindTy Player L} :
    VHasVar (viewVCtx p Γ) x τ → VHasVar Γ x τ := by
  induction Γ with
  | nil => intro h; exact nomatch h
  | cons hd tl ih =>
    obtain ⟨y, σ⟩ := hd
    simp only [viewVCtx]
    split
    · intro h
      match h with
      | .here => exact .here
      | .there h' => exact .there (ih h')
    · intro h
      exact .there (ih h)

end VHasVar

/-- Public-only fragment of a visibility context. -/
def pubVCtx {Player : Type} {L : IExpr} : VCtx Player L → VCtx Player L
  | [] => []
  | (x, ⟨τ, .pub⟩) :: Γ => (x, ⟨τ, .pub⟩) :: pubVCtx Γ
  | (_, ⟨_, .hidden _⟩) :: Γ => pubVCtx Γ

namespace VHasVar

def ofPubVCtx {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} {x : VarId} {τ : BindTy Player L} :
    VHasVar (pubVCtx Γ) x τ → VHasVar Γ x τ := by
  induction Γ with
  | nil => intro h; exact nomatch h
  | cons hd tl ih =>
    obtain ⟨y, σ⟩ := hd
    match σ with
    | ⟨υ, .pub⟩ =>
      simp only [pubVCtx]
      intro h
      match h with
      | .here => exact .here
      | .there h' => exact .there (ih h')
    | ⟨υ, .hidden q⟩ =>
      simp only [pubVCtx]
      intro h
      exact .there (ih h)

end VHasVar

/-! ## Erasure to plain `Ctx`

Erasure is the bridge to the embedded language: `IExpr.eval` and
`IExpr.evalDist` consume plain `Env Val (Ctx L.Ty)`s, so every Vegas
construct must erase its visibility-annotated context before evaluating
expressions. Two erasures coexist:

* `eraseVCtx` (full): used by commit guards and operational kernels —
  syntactically able to reference any variable. Visibility of guards is
  enforced semantically by `GuardUsesOnly` / `ViewScoped` in `Scope.lean`.
* `erasePubVCtx` (public-only): used by `letExpr`, `sample`, and payoff
  expressions — these may not depend on hidden state.

The composition `eraseVCtx ∘ pubVCtx = erasePubVCtx` is the key
commutation lemma (`eraseVCtx_pubVCtx`) that lets `erasePubVCtx`-shaped
goals be reduced to `eraseVCtx`-shaped reasoning. -/

/-- Erase visibility annotations, keeping variable names and base types. -/
def eraseVCtx {Player : Type} {L : IExpr} :
    VCtx Player L → Ctx L.Ty
  | [] => []
  | (x, τ) :: Γ => (x, τ.base) :: eraseVCtx Γ

@[simp] theorem eraseVCtx_nil {Player : Type} {L : IExpr} :
    @eraseVCtx Player L [] = [] := rfl

@[simp] theorem eraseVCtx_cons {Player : Type} {L : IExpr}
    {x : VarId} {τ : BindTy Player L} {Γ : VCtx Player L} :
    eraseVCtx ((x, τ) :: Γ) = (x, τ.base) :: eraseVCtx Γ := rfl

/-- Erasing visibility annotations preserves the variable-name projection. -/
theorem eraseVCtx_map_fst {Player : Type} {L : IExpr} {Γ : VCtx Player L} :
    (eraseVCtx Γ).map Prod.fst = Γ.map Prod.fst := by
  induction Γ with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨x, τ⟩ := hd
      simp [eraseVCtx, ih]

/-- Erase visibility, keeping only public variables. -/
def erasePubVCtx {Player : Type} {L : IExpr} :
    VCtx Player L → Ctx L.Ty
  | [] => []
  | (x, ⟨τ, .pub⟩) :: Γ => (x, τ) :: erasePubVCtx Γ
  | (_, ⟨_, .hidden _⟩) :: Γ => erasePubVCtx Γ

@[simp] theorem erasePubVCtx_nil {Player : Type} {L : IExpr} :
    @erasePubVCtx Player L [] = [] := rfl

@[simp] theorem erasePubVCtx_cons_pub {Player : Type} {L : IExpr}
    {x : VarId} {τ : L.Ty} {Γ : VCtx Player L} :
    erasePubVCtx ((x, .pub τ) :: Γ) = (x, τ) :: erasePubVCtx Γ := rfl

@[simp] theorem erasePubVCtx_cons_hidden {Player : Type} {L : IExpr}
    {x : VarId} {p : Player} {τ : L.Ty} {Γ : VCtx Player L} :
    erasePubVCtx ((x, .hidden p τ) :: Γ) = erasePubVCtx Γ := rfl

/-- Every name in `erasePubVCtx Γ` also appears in any player's view of `Γ`,
since public bindings are visible to everyone. -/
theorem erasePubVCtx_map_fst_sub_viewVCtx
    {Player : Type} [DecidableEq Player] {L : IExpr}
    {Γ : VCtx Player L} {who : Player} :
    ∀ x, x ∈ (erasePubVCtx Γ).map Prod.fst →
      x ∈ (viewVCtx who Γ).map Prod.fst := by
  induction Γ with
  | nil => simp [erasePubVCtx]
  | cons a Γ' ih =>
    intro x hx
    match a with
    | (y, ⟨b, .pub⟩) =>
      simp only [erasePubVCtx_cons_pub, viewVCtx, canSee,
        Visibility.canSee_pub, if_true, List.map_cons, List.mem_cons] at hx ⊢
      exact hx.elim Or.inl (fun h => Or.inr (ih x h))
    | (y, ⟨b, .hidden p⟩) =>
      simp only [erasePubVCtx_cons_hidden, viewVCtx] at hx ⊢
      by_cases h : canSee who (.hidden p b)
      · simp only [h, ite_true, List.map_cons, List.mem_cons]
        right; exact ih x hx
      · simp only [h]
        exact ih x hx

/-- Erasure of pubVCtx equals erasePubVCtx. -/
theorem eraseVCtx_pubVCtx {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} :
    eraseVCtx (pubVCtx Γ) = erasePubVCtx Γ := by
  induction Γ with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨x, τ⟩ := hd
    match τ with
    | ⟨b, .pub⟩ => simp [pubVCtx, erasePubVCtx, ih]
    | ⟨b, .hidden p⟩ => simp [pubVCtx, erasePubVCtx, ih]

/-- A VHasVar proof induces a HasVar proof in the erased context. -/
def VHasVar.toErased {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} {x : VarId} {τ : BindTy Player L} :
    VHasVar Γ x τ → HasVar (eraseVCtx Γ) x τ.base
  | .here => .here
  | .there h => .there h.toErased

/-- A HasVar in eraseVCtx lifts back to a VHasVar. -/
def HasVar.toVHasVar {Player : Type} {L : IExpr} :
    {Γ : VCtx Player L} → {x : VarId} → {b : L.Ty} →
    HasVar (eraseVCtx Γ) x b →
    (τ : BindTy Player L) × VHasVar Γ x τ × PLift (τ.base = b)
  | (_, τ) :: _, _, _, .here => ⟨τ, .here, ⟨rfl⟩⟩
  | _ :: _, _, _, .there h =>
    let ⟨τ', hv, ⟨hb⟩⟩ := toVHasVar h
    ⟨τ', .there hv, ⟨hb⟩⟩

/-- A `HasVar` in `erasePubVCtx Γ` lifts to a `VHasVar` in `pubVCtx Γ` of the
corresponding `pub` binding. The structural inverse to `VHasVar.toErasedPub`. -/
def HasVar.toVHasVarPub {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} {x : VarId} {τ : L.Ty} :
    HasVar (erasePubVCtx Γ) x τ → VHasVar (pubVCtx Γ) x (.pub τ) := by
  induction Γ with
  | nil => intro h; exact nomatch h
  | cons hd tl ih =>
    obtain ⟨y, σ⟩ := hd
    match σ with
    | ⟨υ, .pub⟩ =>
      simp only [erasePubVCtx, pubVCtx]; intro h
      cases h with
      | here => exact .here
      | there h' => exact .there (ih h')
    | ⟨υ, .hidden p⟩ =>
      simp only [erasePubVCtx, pubVCtx]; intro h; exact ih h

/-- A VHasVar in pubVCtx induces a HasVar in erasePubVCtx. -/
def VHasVar.toErasedPub {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} {x : VarId} {τ : BindTy Player L} :
    VHasVar (pubVCtx Γ) x τ → HasVar (erasePubVCtx Γ) x τ.base := by
  intro h
  have h' := h.toErased
  rw [eraseVCtx_pubVCtx] at h'
  exact h'

/-! ## VEnv projections matching the erasures

Each `VEnv L Γ` admits projections matching the context-level operations
above. `eraseEnv` and `erasePubEnv` are the two consumed by the semantics
(passed to `IExpr.eval`/`evalDist`); the others stay in the `VEnv` world for
intra-Vegas reasoning. -/

namespace VEnv

/-- Erase visibility from a VEnv, producing a plain Env over eraseVCtx. -/
def eraseEnv {Player : Type} {L : IExpr} :
    {Γ : VCtx Player L} → VEnv L Γ →
    Env L.Val (eraseVCtx Γ)
  | [], _ => Env.empty L.Val
  | (_, _) :: _, env =>
    Env.cons (env.get .here) (eraseEnv (fun a b h => env a b (.there h)))

/-- Erase visibility, keeping only public variables. -/
def erasePubEnv {Player : Type} {L : IExpr} :
    {Γ : VCtx Player L} → VEnv L Γ →
    Env L.Val (erasePubVCtx Γ)
  | [], _ => Env.empty L.Val
  | ((_, ⟨_, .pub⟩) :: Γ'), env =>
    Env.cons (env.get .here)
      (erasePubEnv (Γ := Γ') (fun a b h => env a b (VHasVar.there h)))
  | ((_, ⟨_, .hidden _⟩) :: Γ'), env =>
    erasePubEnv (Γ := Γ') (fun a b h => env a b (VHasVar.there h))

/-- Pointwise formula for `erasePubEnv`: looking up at an erased-pub position
equals looking up the original VEnv at the corresponding `pub` binding. -/
@[simp] theorem erasePubEnv_get {Player : Type} {L : IExpr}
    {Γ : VCtx Player L}
    (env : VEnv (Player := Player) L Γ)
    {x : VarId} {τ : L.Ty}
    (hx : HasVar (erasePubVCtx Γ) x τ) :
    erasePubEnv env x τ hx =
      env x (.pub τ) (VHasVar.ofPubVCtx (HasVar.toVHasVarPub hx)) := by
  induction Γ generalizing x τ with
  | nil => exact nomatch hx
  | cons hd tl ih =>
    obtain ⟨y, σ⟩ := hd
    match σ with
    | ⟨υ, .pub⟩ =>
      cases hx with
      | here => rfl
      | there hx' =>
        simpa [VEnv.erasePubEnv, HasVar.toVHasVarPub] using
          (ih (env := fun a b h => env a b (VHasVar.there h)) hx')
    | ⟨υ, .hidden p⟩ =>
      simpa [VEnv.erasePubEnv, HasVar.toVHasVarPub] using
        (ih (env := fun a b h => env a b (VHasVar.there h)) hx)

/-- Pointwise formula for `eraseEnv`: looking up at the erased position
produced by `VHasVar.toErased` equals the original lookup. -/
@[simp] theorem eraseEnv_get_of_erased {Player : Type} {L : IExpr}
    {Γ : VCtx Player L}
    (env : VEnv (Player := Player) L Γ)
    {x : VarId} {τ : BindTy Player L}
    (hx : VHasVar Γ x τ) :
    eraseEnv env x τ.base hx.toErased = env x τ hx := by
  induction hx with
  | here => rfl
  | there hx ih =>
    simpa [VEnv.eraseEnv] using (ih (env := fun a b h => env a b (VHasVar.there h)))

/-- HEq variant of `eraseEnv_get_of_erased`, going through `HasVar.toVHasVar`:
the erased-env lookup at `hx` is HEq to the lookup along the lifted-and-then-
re-erased proof. Useful where dependent typing makes a strict equality
unstatable. -/
theorem eraseEnv_toErased_eq {Player : Type} {L : IExpr} :
    {Γ : VCtx Player L} →
    (env : VEnv (Player := Player) L Γ) →
    {x : VarId} → {b : L.Ty} →
    (hx : HasVar (eraseVCtx Γ) x b) →
    HEq (env.eraseEnv x
        (hx.toVHasVar (Player := Player) (L := L)).1.base
        (hx.toVHasVar (Player := Player) (L := L)).2.1.toErased)
      (env.eraseEnv x b hx)
  | _ :: _, _, _, _, .here => HEq.rfl
  | _ :: _, env, _, _, .there hx =>
      eraseEnv_toErased_eq (fun a b h => env a b (.there h)) hx

/-- Project a VEnv to the visible subcontext of player `p`. -/
def toView {Player : Type} [DecidableEq Player] {L : IExpr} (p : Player)
    {Γ : VCtx Player L} (env : VEnv L Γ) :
    VEnv (Player := Player) L (viewVCtx p Γ) :=
  fun x τ h => env x τ h.ofViewVCtx

/-- Project a VEnv to the public subcontext. -/
def toPub {Player : Type} {L : IExpr} {Γ : VCtx Player L}
    (env : VEnv L Γ) :
    VEnv (Player := Player) L (pubVCtx Γ) :=
  fun x τ h => env x τ h.ofPubVCtx

end VEnv

/-! ## Sampling convention

A naming layer: sample distributions are evaluated in the public-only
subcontext, because nature has no private knowledge — drawing must depend
solely on observable state. The abbreviation `sampleVCtx := pubVCtx`
documents this design choice; the two functions are definitionally equal. -/

/-- Sampling is public nature: distributions are evaluated in the public
context and the sampled result is bound as a fresh public variable. -/
abbrev sampleVCtx {Player : Type} {L : IExpr} (Γ : VCtx Player L) : VCtx Player L :=
  pubVCtx Γ

namespace VEnv

/-- Erase the public fragment of a VEnv for evaluating a sample distribution. -/
def eraseSampleEnv {Player : Type} {L : IExpr}
    {Γ : VCtx Player L}
    (env : VEnv L Γ) :
    Env L.Val (erasePubVCtx Γ) :=
  VEnv.erasePubEnv env

end VEnv

/-! ## Outcomes and payoff/guard evaluation -/

/-- Canonical outcome type: finitely-supported integer payoffs per player.

The `Finsupp` representation is load-bearing: it aggregates per-player
contributions by summing on matching keys, and its decidable equality is
required for `FWeight (Outcome Player)` to type-check. Players absent from
a `.support` default to payoff `0`, which matches the "only named players
are paid" semantics. -/
abbrev Outcome (Player : Type) [DecidableEq Player] := Player →₀ Int

/-- Sum of payoff contributions for player `p` across a payoff list.
Duplicates of `p` in the list are added. Defined recursively so that
`evalPayoffs` can be built without invoking `Finsupp.single` or
`Finsupp.(+)`, which are both `noncomputable` in Mathlib. -/
def payoffAt {Player : Type} [DecidableEq Player]
    (p : Player) : List (Player × Int) → Int
  | [] => 0
  | (q, v) :: rest => (if q = p then v else 0) + payoffAt p rest

/-- Build an `Outcome` directly from a list of `(player, payoff)` entries,
summing duplicates. Sidesteps `Finsupp.single` and `Finsupp.(+)` (which
are noncomputable in Mathlib despite `[DecidableEq]` being available) by
constructing the underlying `Finsupp` record in one shot. -/
def mkOutcome {Player : Type} [DecidableEq Player]
    (entries : List (Player × Int)) : Outcome Player where
  support := (entries.map Prod.fst).toFinset.filter (fun p => payoffAt p entries ≠ 0)
  toFun p := payoffAt p entries
  mem_support_toFun p := by
    rw [Finset.mem_filter]
    refine ⟨fun h => h.2, fun hne => ⟨?_, hne⟩⟩
    simp only [List.mem_toFinset, List.mem_map]
    induction entries with
    | nil => simp [payoffAt] at hne
    | cons hd tl ih =>
        simp only [payoffAt] at hne
        by_cases h : hd.1 = p
        · exact ⟨hd, by simp, h⟩
        · have htail : payoffAt p tl ≠ 0 := by
            intro hzero
            apply hne
            simp [h, hzero]
          rcases ih htail with ⟨entry, hmem, heq⟩
          exact ⟨entry, List.mem_cons_of_mem hd hmem, heq⟩

/-- Evaluate a list of per-player payoff expressions into an outcome. -/
def evalPayoffs {Player : Type} [DecidableEq Player]
    {L : IExpr} {Γ : VCtx Player L}
    (payoffs : List (Player × L.Expr (erasePubVCtx Γ) L.int))
    (env : VEnv L Γ) : Outcome Player :=
  mkOutcome (payoffs.map
    (fun pe => (pe.1, L.toInt (L.eval pe.2 (VEnv.erasePubEnv env)))))

/-- Evaluate a commit guard against a proposed action and the full erased
    environment. Visibility is enforced by dependency constraints on `R`,
    not by restricting the environment type. -/
def evalGuard {Player : Type} [DecidableEq Player] {L : IExpr}
    {Γ : VCtx Player L} {b : L.Ty}
    {x : VarId}
    (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool)
    (a : L.Val b) (env : Env L.Val (eraseVCtx Γ)) : Bool :=
  L.toBool (L.eval R (Env.cons a env))

/-! ## Vegas program syntax -/

/-- Generic Vegas-style protocol syntax over an expression language.

A `VegasCore Player L Γ` is a typed program in context `Γ`. The inductive
is indexed by the visibility context, so every well-formed term is
well-scoped by construction. Strategies do not appear here — the `commit`
constructor holds only its guard, and the choice kernel is supplied
by local strategy carriers in the strategic and machine semantics. The same
program can therefore be evaluated against many strategy profiles.

## Classification

Four of the five constructors are **protocol events** that model
observable activity in a multi-party computation:

* `ret` — the protocol terminates and players collect payoffs.
* `sample` — nature draws from a public distribution; every player sees
  the outcome.
* `commit` — a player chooses a value subject to a guard and seals it
  from the others.
* `reveal` — a previously sealed value is disclosed to everyone. This is
  the only way to make hidden data observable; the timing of the reveal
  is under program control, distinguishing open play from sealed commitment.

The fifth constructor, `letExpr`, is **administrative**: Semantically,
`letExpr x e k` is equivalent to `sample x (Dirac e) k`: if the language
provided a point-mass distribution constructor `Dirac : L.Expr → L.DistExpr`
with `L.evalDist (Dirac e) = FWeight.pure ∘ L.eval e`, then `bind` on a
Dirac distribution reduces by `FWeight.pure_bind` to the direct
extension we do here. The constructor is kept as a distinct form
despite this equivalence, for four reasons:

1. **Smaller interface.** Eliminating `letExpr` would require `IExpr`
    to expose a canonical `Expr → DistExpr` lift (or, equivalently, a
    substitution operation). Keeping it means `IExpr` stays
    dimensioned to its actual metatheory needs.

2. **Linear term size.** Inlining a `let x = e` that is referenced
    `n` times downstream would duplicate `e` into every reference
    site — `n` copies in guards, distributions, and payoffs. The
    named binding keeps the program linear in its surface size, which
    also keeps `exprDeps` accounting local.

3. **View-shape stability.** The public binding `(x, .pub b)` appears
    in every downstream `viewVCtx who Γ'`. Erasing `letExpr` would
    remove `x` from the context, changing the types of every
    behavioral kernel that observed `x`. "A strategy depending on `x`
    equals a strategy recomputing `e` from the earlier public view"
    is true but requires a substitution/transport metatheorem that
    currently isn't needed.

4. **Reader intuition.** `let` and `sample` signal different intent:
    one is bookkeeping, the other introduces randomness. A surface
    reader encountering `sample x ~ Dirac(e)` would rightly ask "why
    is this random?" when nothing stochastic is happening. -/
inductive VegasCore (Player : Type) [DecidableEq Player] (L : IExpr) :
    VCtx Player L → Type where
  /-- Terminate with per-player payoffs. Each payoff expression is over the
  public-only erased context — payoffs cannot depend on hidden state. -/
  | ret {Γ} (payoffs : List (Player × L.Expr (erasePubVCtx Γ) L.int)) :
      VegasCore Player L Γ
  /-- Bind a deterministic expression `e` to a fresh public variable `x`.
  `e` reads only public state. -/
  | letExpr {Γ} (x : VarId) {b : L.Ty}
      (e : L.Expr (erasePubVCtx Γ) b)
      (k : VegasCore Player L ((x, .pub b) :: Γ)) :
      VegasCore Player L Γ
  /-- Sample from `D'` and bind the result as a fresh public variable.
  `D'` reads only public state (nature has no private knowledge); the
  sampled value is observable to all. -/
  | sample {Γ} (x : VarId) {b : L.Ty}
      (D' : L.DistExpr (erasePubVCtx Γ) b)
      (k : VegasCore Player L ((x, .pub b) :: Γ)) :
      VegasCore Player L Γ
  /-- Player `who` commits to a value of type `b`, subject to guard `R`.
  The guard is typed over `(x, b) :: eraseVCtx Γ` (the proposed action on
  top of the *full* erased context). Visibility — that the guard depends
  only on `who`'s view — is enforced semantically in `Scope.lean`. The
  result is bound as `hidden who b`, visible only to `who`. -/
  | commit {Γ} (x : VarId) (who : Player) {b : L.Ty}
      (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool)
      (k : VegasCore Player L ((x, .hidden who b) :: Γ)) :
      VegasCore Player L Γ
  /-- Disclose a previously hidden variable `x` as a fresh public alias `y`.
  The membership witness `hx` must show `x` is currently hidden, owned by
  `who`. -/
  | reveal {Γ} (y : VarId) (who : Player) (x : VarId) {b : L.Ty}
      (hx : VHasVar Γ x (.hidden who b))
      (k : VegasCore Player L ((y, .pub b) :: Γ)) :
      VegasCore Player L Γ

/-! ## Finite operational domains (opt-in)

Finite game construction needs to enumerate runtime environments, player
actions, machine states, and bounded histories. That requirement is
program-local: types that appear in stored program state, samples, commits,
and reveals must be finite. The payoff codomain `L.int` does not need to be
finite merely because terminal utilities are integer-valued.
-/

/-- A finite semantic domain for one expression-language type. Concrete
languages can provide instances for bounded types, while leaving unbounded
types such as payoff integers without an instance. -/
class FiniteType (L : IExpr) (τ : L.Ty) where
  fintype : Fintype (L.Val τ)

noncomputable instance instFintypeOfFiniteType
    (L : IExpr) (τ : L.Ty) [h : FiniteType L τ] :
    Fintype (L.Val τ) :=
  h.fintype

/-- The finite branching factor of a finite expression-language type. -/
noncomputable def finiteDomainSize (L : IExpr) (τ : L.Ty)
    [FiniteType L τ] : Nat :=
  Fintype.card (L.Val τ)

/-- A canonical encoding of finite expression-language values as `Fin`. -/
noncomputable def encodeFiniteType (L : IExpr) (τ : L.Ty)
    [FiniteType L τ] :
    L.Val τ ≃ Fin (finiteDomainSize L τ) :=
  Fintype.equivFin (L.Val τ)

/-- Structural evidence that every value stored in a plain context has a
finite domain. -/
inductive FiniteCtxProof {L : IExpr} : Ctx L.Ty → Type where
  | nil : FiniteCtxProof []
  | cons {x : VarId} {τ : L.Ty} {Γ : Ctx L.Ty}
      (head : FiniteType L τ) (tail : FiniteCtxProof Γ) :
      FiniteCtxProof ((x, τ) :: Γ)

/-- Typeclass wrapper for finite plain contexts. -/
class FiniteCtx {L : IExpr} (Γ : Ctx L.Ty) where
  proof : FiniteCtxProof Γ

instance finiteCtx_nil {L : IExpr} : FiniteCtx ([] : Ctx L.Ty) where
  proof := .nil

instance finiteCtx_cons {L : IExpr} {x : VarId} {τ : L.Ty}
    {Γ : Ctx L.Ty} [FiniteType L τ] [FiniteCtx Γ] :
    FiniteCtx ((x, τ) :: Γ) where
  proof := .cons (inferInstance : FiniteType L τ) (FiniteCtx.proof (Γ := Γ))

namespace FiniteCtxProof

@[reducible] noncomputable def fintypeOfHasVar {L : IExpr} :
    {Γ : Ctx L.Ty} → FiniteCtxProof Γ →
      {x : VarId} → {τ : L.Ty} → HasVar Γ x τ → Fintype (L.Val τ)
  | _, .nil, _, _, h => nomatch h
  | _, .cons head _tail, _, _, .here => head.fintype
  | _, .cons _head tail, _, _, .there h => fintypeOfHasVar tail h

end FiniteCtxProof

namespace FiniteCtx

@[reducible] noncomputable def fintypeOfHasVar {L : IExpr} {Γ : Ctx L.Ty}
    [hΓ : FiniteCtx Γ] {x : VarId} {τ : L.Ty}
    (h : HasVar Γ x τ) : Fintype (L.Val τ) :=
  FiniteCtxProof.fintypeOfHasVar hΓ.proof h

end FiniteCtx

/-- Structural evidence that every value stored in a visibility context has a
finite domain. -/
inductive FiniteVCtxProof {P : Type} {L : IExpr} :
    VCtx P L → Type where
  | nil : FiniteVCtxProof []
  | cons {x : VarId} {τ : BindTy P L} {Γ : VCtx P L}
      (head : FiniteType L τ.base) (tail : FiniteVCtxProof Γ) :
      FiniteVCtxProof ((x, τ) :: Γ)

/-- Typeclass wrapper for finite visibility contexts. -/
class FiniteVCtx {P : Type} {L : IExpr} (Γ : VCtx P L) where
  proof : FiniteVCtxProof Γ

instance finiteVCtx_nil {P : Type} {L : IExpr} :
    FiniteVCtx ([] : VCtx P L) where
  proof := .nil

instance finiteVCtx_cons {P : Type} {L : IExpr} {x : VarId}
    {τ : BindTy P L} {Γ : VCtx P L}
    [FiniteType L τ.base] [FiniteVCtx Γ] :
    FiniteVCtx ((x, τ) :: Γ) where
  proof := .cons (inferInstance : FiniteType L τ.base)
    (FiniteVCtx.proof (Γ := Γ))

namespace FiniteVCtxProof

@[reducible] noncomputable def fintypeOfHasVar {P : Type} {L : IExpr} :
    {Γ : VCtx P L} → FiniteVCtxProof Γ →
      {x : VarId} → {τ : BindTy P L} →
        VHasVar Γ x τ → Fintype (L.Val τ.base)
  | _, .nil, _, _, h => nomatch h
  | _, .cons head _tail, _, _, .here => head.fintype
  | _, .cons _head tail, _, _, .there h => fintypeOfHasVar tail h

def erase {P : Type} {L : IExpr} :
    {Γ : VCtx P L} → FiniteVCtxProof Γ →
      FiniteCtxProof (eraseVCtx Γ)
  | [], .nil => .nil
  | (_x, _τ) :: _Γ, .cons head tail => .cons head tail.erase

def view {P : Type} [DecidableEq P] {L : IExpr} (who : P) :
    {Γ : VCtx P L} → FiniteVCtxProof Γ →
      FiniteVCtxProof (viewVCtx who Γ)
  | [], .nil => .nil
  | (_x, _τ) :: _Γ, .cons head tail => by
      simp only [viewVCtx]
      split
      · exact .cons head (tail.view who)
      · exact tail.view who

end FiniteVCtxProof

namespace FiniteVCtx

@[reducible] noncomputable def fintypeOfHasVar {P : Type} {L : IExpr}
    {Γ : VCtx P L} [hΓ : FiniteVCtx Γ]
    {x : VarId} {τ : BindTy P L}
    (h : VHasVar Γ x τ) : Fintype (L.Val τ.base) :=
  FiniteVCtxProof.fintypeOfHasVar hΓ.proof h

@[reducible] def erase {P : Type} {L : IExpr} {Γ : VCtx P L}
    [hΓ : FiniteVCtx Γ] : FiniteCtx (eraseVCtx Γ) where
  proof := hΓ.proof.erase

@[reducible] def view {P : Type} [DecidableEq P] {L : IExpr}
    {Γ : VCtx P L} [hΓ : FiniteVCtx Γ] (who : P) :
    FiniteVCtx (viewVCtx who Γ) where
  proof := hΓ.proof.view who

end FiniteVCtx

/-- Structural evidence that the operational value domains introduced by a
program are finite. Terminal payoff expressions are intentionally ignored. -/
inductive FiniteProgramProof {P : Type} [DecidableEq P] {L : IExpr} :
    {Γ : VCtx P L} → VegasCore P L Γ → Type where
  | ret {Γ : VCtx P L}
      {payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)} :
      FiniteProgramProof (.ret payoffs)
  | letExpr {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {e : L.Expr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)}
      (head : FiniteType L b) (tail : FiniteProgramProof k) :
      FiniteProgramProof (.letExpr x e k)
  | sample {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {D : L.DistExpr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)}
      (head : FiniteType L b) (tail : FiniteProgramProof k) :
      FiniteProgramProof (.sample x D k)
  | commit {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
      {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
      {k : VegasCore P L ((x, .hidden who b) :: Γ)}
      (head : FiniteType L b) (tail : FiniteProgramProof k) :
      FiniteProgramProof (.commit x who R k)
  | reveal {Γ : VCtx P L} {y : VarId} {who : P}
      {x : VarId} {b : L.Ty}
      {hx : VHasVar Γ x (.hidden who b)}
      {k : VegasCore P L ((y, .pub b) :: Γ)}
      (head : FiniteType L b) (tail : FiniteProgramProof k) :
      FiniteProgramProof (.reveal y who x hx k)

/-- Typeclass wrapper for finite operational domains in a raw program. -/
class FiniteProgram {P : Type} [DecidableEq P] {L : IExpr}
    {Γ : VCtx P L} (p : VegasCore P L Γ) where
  proof : FiniteProgramProof p

instance finiteProgram_ret {P : Type} [DecidableEq P] {L : IExpr}
    {Γ : VCtx P L}
    {payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)} :
    FiniteProgram (.ret payoffs) where
  proof := .ret

instance finiteProgram_letExpr {P : Type} [DecidableEq P] {L : IExpr}
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {e : L.Expr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)}
    [FiniteType L b] [FiniteProgram k] :
    FiniteProgram (.letExpr x e k) where
  proof := .letExpr (inferInstance : FiniteType L b)
    (FiniteProgram.proof (p := k))

instance finiteProgram_sample {P : Type} [DecidableEq P] {L : IExpr}
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {D : L.DistExpr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)}
    [FiniteType L b] [FiniteProgram k] :
    FiniteProgram (.sample x D k) where
  proof := .sample (inferInstance : FiniteType L b)
    (FiniteProgram.proof (p := k))

instance finiteProgram_commit {P : Type} [DecidableEq P] {L : IExpr}
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    [FiniteType L b] [FiniteProgram k] :
    FiniteProgram (.commit x who R k) where
  proof := .commit (inferInstance : FiniteType L b)
    (FiniteProgram.proof (p := k))

instance finiteProgram_reveal {P : Type} [DecidableEq P] {L : IExpr}
    {Γ : VCtx P L} {y : VarId} {who : P}
    {x : VarId} {b : L.Ty}
    {hx : VHasVar Γ x (.hidden who b)}
    {k : VegasCore P L ((y, .pub b) :: Γ)}
    [FiniteType L b] [FiniteProgram k] :
    FiniteProgram (.reveal y who x hx k) where
  proof := .reveal (inferInstance : FiniteType L b)
    (FiniteProgram.proof (p := k))

end Vegas
