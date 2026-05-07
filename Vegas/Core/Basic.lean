import Vegas.Base.Basic

/-!
# Vegas core syntax

Generic Vegas protocol syntax and finite operational-domain evidence.
-/

namespace Vegas

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
