import Vegas.VegasLang

/-!
# Nullable compilation

This file exposes the `VegasLang` nullable-yield lowering as a named compiler.

The compiler lives at the `VegasLang → VegasCore simpleExpr` boundary. That is
the point where nullable public moves become backend-safe core commits: a
surface `yield` lowers to an internal `option T` commitment followed by a
public reveal of the same optional value.
-/

namespace Vegas

variable {P : Type} [DecidableEq P]

namespace VegasLang

/-- Compile the surface language into backend-safe core syntax with nullable
public yields. This is intentionally definitionally equal to `lower`; the name
records the semantic role needed by the theorem surface. -/
def compileNullable :
    {Γ : VCtx P simpleExpr} → VegasLang P Γ → VegasCore P simpleExpr Γ :=
  lower

@[simp] theorem compileNullable_eq_lower
    {Γ : VCtx P simpleExpr}
    (p : VegasLang P Γ) :
    compileNullable p = lower p := rfl

@[simp] theorem compileNullable_ret
    {Γ : VCtx P simpleExpr}
    (payoffs : List (P × Expr (erasePubVCtx Γ) .int)) :
    compileNullable (VegasLang.ret (P := P) payoffs) =
      VegasCore.ret payoffs := rfl

@[simp] theorem compileNullable_letExpr
    {Γ : VCtx P simpleExpr} (x : VarId) {b : BaseTy}
    (e : Expr (erasePubVCtx Γ) b)
    (k : VegasLang P ((x, .pub b) :: Γ)) :
    compileNullable (VegasLang.letExpr x e k) =
      VegasCore.letExpr x e (compileNullable k) := rfl

@[simp] theorem compileNullable_sample
    {Γ : VCtx P simpleExpr} (x : VarId) {b : BaseTy}
    (D : DistExpr (erasePubVCtx Γ) b)
    (k : VegasLang P ((x, .pub b) :: Γ)) :
    compileNullable (VegasLang.sample x D k) =
      VegasCore.sample x D (compileNullable k) := rfl

@[simp] theorem compileNullable_commit
    {Γ : VCtx P simpleExpr} (x : VarId) (who : P) {b : BaseTy}
    [CommitPayloadTy b]
    (R : Expr ((x, b) :: eraseVCtx Γ) .bool)
    (k : VegasLang P ((x, .hidden who b) :: Γ)) :
    compileNullable (VegasLang.commit x who R k) =
      VegasCore.commit x who R (compileNullable k) := rfl

@[simp] theorem compileNullable_yield
    {Γ : VCtx P simpleExpr}
    (secret pubVar : VarId) (who : P) {b : BaseTy}
    [CommitPayloadTy b] [DefaultVal b]
    (R : Expr ((secret, b) :: eraseVCtx Γ) .bool)
    (k : VegasLang P
      ((pubVar, .pub (BaseTy.option b)) ::
        (secret, .hidden who (BaseTy.option b)) :: Γ)) :
    compileNullable (VegasLang.yield secret pubVar who R k) =
      VegasCore.commit secret who (b := BaseTy.option b)
        (Expr.nullableCommitGuard R)
        (VegasCore.reveal pubVar who secret VHasVar.here
          (compileNullable k)) := rfl

@[simp] theorem compileNullable_reveal
    {Γ : VCtx P simpleExpr} (y : VarId) (who : P) (x : VarId)
    {b : BaseTy}
    (hx : VHasVar Γ x (.hidden who b))
    (k : VegasLang P ((y, .pub b) :: Γ)) :
    compileNullable (VegasLang.reveal y who x hx k) =
      VegasCore.reveal y who x hx (compileNullable k) := rfl

@[simp] theorem compileNullable_simultaneous
    {Γ Δ : VCtx P simpleExpr}
    (phase : VegasYieldPhase P Γ [] Δ)
    (hactors : phase.DistinctActors)
    (k : VegasLang P Δ) :
    compileNullable (VegasLang.simultaneous phase hactors k) =
      VegasYieldPhase.lowerWith phase (compileNullable k) := rfl

/-- The nullable action synthesized by compilation is always guard-legal:
choosing `none` satisfies the compiled guard independently of the source guard.
-/
theorem compileNullable_none_guard_legal
    {Γ : VCtx P simpleExpr} {secret : VarId} {b : BaseTy}
    [DefaultVal b]
    (R : Expr ((secret, b) :: eraseVCtx Γ) .bool)
    (env : Env Val (eraseVCtx Γ)) :
    evalGuard (Player := P) (L := simpleExpr)
      (Expr.nullableCommitGuard R) Option.none env = true := by
  change evalExpr (Expr.nullableCommitGuard R)
      (Env.cons (x := secret) Option.none env) = true
  exact evalExpr_nullableCommitGuard_none R env

/-- On ordinary source values, the compiled nullable guard agrees with the
original guard. -/
theorem compileNullable_some_guard_eq
    {Γ : VCtx P simpleExpr} {secret : VarId} {b : BaseTy}
    [DefaultVal b]
    (R : Expr ((secret, b) :: eraseVCtx Γ) .bool)
    (v : Val b) (env : Env Val (eraseVCtx Γ)) :
    evalGuard (Player := P) (L := simpleExpr)
        (Expr.nullableCommitGuard R) (some v) env =
      evalGuard (Player := P) (L := simpleExpr) R v env := by
  change evalExpr (Expr.nullableCommitGuard R)
      (Env.cons (x := secret) (some v) env) =
    evalExpr R (Env.cons (x := secret) v env)
  exact evalExpr_nullableCommitGuard_some R v env

/-- Every compiled nullable guard has at least one legal action in every
environment, namely `none`. -/
theorem compileNullable_guard_satisfiable
    {Γ : VCtx P simpleExpr} {secret : VarId} {b : BaseTy}
    [DefaultVal b]
    (R : Expr ((secret, b) :: eraseVCtx Γ) .bool) :
    ∀ env : Env Val (eraseVCtx Γ),
      ∃ a : Val (.option b),
        evalGuard (Player := P) (L := simpleExpr)
          (Expr.nullableCommitGuard R) a env = true := by
  exact nullableCommitGuard_satisfiable R

/-- Replacing a surface yield by its compiled nullable core action preserves
legality assuming the continuation is legal. -/
theorem compileNullable_yield_legal_of_continuation
    {Γ : VCtx P simpleExpr}
    (secret pubVar : VarId) (who : P) {b : BaseTy}
    [CommitPayloadTy b] [DefaultVal b]
    (R : Expr ((secret, b) :: eraseVCtx Γ) .bool)
    (k : VegasLang P
      ((pubVar, .pub (BaseTy.option b)) ::
        (secret, .hidden who (BaseTy.option b)) :: Γ))
    (hk : Legal (compileNullable k)) :
    Legal (compileNullable (VegasLang.yield secret pubVar who R k)) := by
  exact ⟨compileNullable_guard_satisfiable R, hk⟩

end VegasLang

end Vegas
