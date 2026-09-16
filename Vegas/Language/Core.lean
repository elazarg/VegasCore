/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Foundation.FiniteDomain
import Vegas.Language.Guard

/-!
# Surface-language elaboration target

Intrinsically typed syntax produced by the surface-language prototype. This
representation has no verified elaboration into the failure-aware `SourceProgram`.
Its declarations retain guards as syntax; the separate `Legal` predicate
requires a satisfying value in every visible environment. These are prototype
side conditions, not the deferred failure semantics of `SourceProgram`.
-/

namespace Vegas

/-! ## Typed surface core -/

/-- Generic Vegas-style protocol syntax over an expression language.

A `SurfaceCore Player L Γ` is a typed program in context `Γ`. The inductive
is indexed by the visibility context, so every well-formed term is
well-scoped by construction. Constructors retain the expressions, guards, and
distribution syntax needed by elaboration; this module supplies syntax and
finite-domain evidence, not an execution or strategic correspondence theorem.

## Classification

The constructors are **protocol events** that model observable activity in a
multi-party computation:

* `ret` — the protocol terminates and players collect payoffs.
* `sample` — nature draws from a public distribution; every player sees
  the outcome.
* `commit` — a player chooses a value subject to a guard and seals it
  from the others.
* `reveal` — a previously sealed value is disclosed to everyone. This is
  the only way to make sealed data observable; the timing of the reveal
  is under program control, distinguishing open play from sealed commitment.

Administrative deterministic bindings are substituted by `VegasLang.lower`
when it constructs this representation. -/
inductive SurfaceCore (Player : Type) [DecidableEq Player] (L : IExpr) :
    VCtx Player L → Type where
  /-- Terminate with per-player payoffs. Each payoff expression is over the
  public-only erased context — payoffs cannot depend on sealed state. -/
  | ret {Γ} (payoffs : List (Player × L.Expr (erasePubVCtx Γ) L.int)) :
      SurfaceCore Player L Γ
  /-- Sample from `D'` and bind the result as a fresh public variable.
  `D'` reads only public state (nature has no private knowledge); the
  sampled value is observable to all. -/
  | sample {Γ} (x : VarId) {b : L.Ty}
      (D' : L.DistExpr (erasePubVCtx Γ) b)
      (k : SurfaceCore Player L ((x, .pub b) :: Γ)) :
      SurfaceCore Player L Γ
  /-- Player `who` commits to a value of type `b`, subject to guard `R`.
  The guard is typed over the proposed action together with `who`'s current
  view. The result is bound as `sealed who b`, visible only to `who`. -/
  | commit {Γ} (x : VarId) (who : Player) {b : L.Ty}
      (R : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool)
      (k : SurfaceCore Player L ((x, .sealed who b) :: Γ)) :
      SurfaceCore Player L Γ
  /-- Disclose a previously sealed variable `x` as a fresh public alias `y`.
  The membership witness `hx` must show `x` is currently sealed, owned by
  `who`. -/
  | reveal {Γ} (y : VarId) (who : Player) (x : VarId) {b : L.Ty}
      (hx : VHasVar Γ x (.sealed who b))
      (k : SurfaceCore Player L ((y, .pub b) :: Γ)) :
      SurfaceCore Player L Γ

/-! ## Finite operational domains for surface programs

Value and context evidence is shared through `Vegas.Foundation.FiniteDomain`;
the following evidence concerns only this surface elaboration target.
-/

/-- Structural evidence that the operational value domains introduced by a
program are finite. Terminal payoff expressions are intentionally ignored. -/
inductive FiniteProgramProof {P : Type} [DecidableEq P] {L : IExpr} :
    {Γ : VCtx P L} → SurfaceCore P L Γ → Type where
  | ret {Γ : VCtx P L}
      {payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)} :
      FiniteProgramProof (.ret payoffs)
  | sample {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {D : L.DistExpr (erasePubVCtx Γ) b}
      {k : SurfaceCore P L ((x, .pub b) :: Γ)}
      (head : FiniteType L b) (tail : FiniteProgramProof k) :
      FiniteProgramProof (.sample x D k)
  | commit {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
      {R : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool}
      {k : SurfaceCore P L ((x, .sealed who b) :: Γ)}
      (head : FiniteType L b) (tail : FiniteProgramProof k) :
      FiniteProgramProof (.commit x who R k)
  | reveal {Γ : VCtx P L} {y : VarId} {who : P}
      {x : VarId} {b : L.Ty}
      {hx : VHasVar Γ x (.sealed who b)}
      {k : SurfaceCore P L ((y, .pub b) :: Γ)}
      (head : FiniteType L b) (tail : FiniteProgramProof k) :
      FiniteProgramProof (.reveal y who x hx k)

/-- Typeclass wrapper for finite operational domains in a raw program. -/
class FiniteProgram {P : Type} [DecidableEq P] {L : IExpr}
    {Γ : VCtx P L} (p : SurfaceCore P L Γ) where
  proof : FiniteProgramProof p

instance finiteProgram_ret {P : Type} [DecidableEq P] {L : IExpr}
    {Γ : VCtx P L}
    {payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)} :
    FiniteProgram (.ret payoffs) where
  proof := .ret

instance finiteProgram_sample {P : Type} [DecidableEq P] {L : IExpr}
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {D : L.DistExpr (erasePubVCtx Γ) b}
    {k : SurfaceCore P L ((x, .pub b) :: Γ)}
    [FiniteType L b] [FiniteProgram k] :
    FiniteProgram (.sample x D k) where
  proof := .sample (inferInstance : FiniteType L b)
    (FiniteProgram.proof (p := k))

instance finiteProgram_commit {P : Type} [DecidableEq P] {L : IExpr}
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {k : SurfaceCore P L ((x, .sealed who b) :: Γ)}
    [FiniteType L b] [FiniteProgram k] :
    FiniteProgram (.commit x who R k) where
  proof := .commit (inferInstance : FiniteType L b)
    (FiniteProgram.proof (p := k))

instance finiteProgram_reveal {P : Type} [DecidableEq P] {L : IExpr}
    {Γ : VCtx P L} {y : VarId} {who : P}
    {x : VarId} {b : L.Ty}
    {hx : VHasVar Γ x (.sealed who b)}
    {k : SurfaceCore P L ((y, .pub b) :: Γ)}
    [FiniteType L b] [FiniteProgram k] :
    FiniteProgram (.reveal y who x hx k) where
  proof := .reveal (inferInstance : FiniteType L b)
    (FiniteProgram.proof (p := k))

end Vegas
