import Vegas.NullableCompile

/-!
# Nullable Compilation Theorems

Project-facing names for the nullable compilation boundary. The strategic
strict-domination statements still need the equilibrium/penalty transport
definitions, but the compiler and its guard semantics are now ordinary Lean
declarations rather than theorem-backlog prose.
-/

namespace Vegas

/-- Nullable compilation is the named surface-to-core lowering pass. -/
theorem nullableCompile_eq_lower
    {P : Type} [DecidableEq P]
    {Γ : VCtx P simpleExpr}
    (p : VegasLang P Γ) :
    VegasLang.compileNullable p = VegasLang.lower p := rfl

/-- A surface yield lowers to an optional hidden commit followed by a public
reveal of that optional value. -/
theorem nullableCompile_yield_lowers_to_nullable_commit
    {P : Type} [DecidableEq P]
    {Γ : VCtx P simpleExpr}
    (secret pubVar : VarId) (who : P) {b : BaseTy}
    [CommitPayloadTy b] [DefaultVal b]
    (R : Expr ((secret, b) :: eraseVCtx Γ) .bool)
    (k : VegasLang P
      ((pubVar, .pub (BaseTy.option b)) ::
        (secret, .hidden who (BaseTy.option b)) :: Γ)) :
    VegasLang.compileNullable
        (VegasLang.yield secret pubVar who R k) =
      VegasCore.commit secret who (b := BaseTy.option b)
        (Expr.nullableCommitGuard R)
        (VegasCore.reveal pubVar who secret VHasVar.here
          (VegasLang.compileNullable k)) :=
  VegasLang.compileNullable_yield secret pubVar who R k

/-- The synthesized nullable abort action is always legal at the compiled
guard. -/
theorem nullableCompile_none_guard_legal
    {P : Type} [DecidableEq P]
    {Γ : VCtx P simpleExpr} {secret : VarId} {b : BaseTy}
    [DefaultVal b]
    (R : Expr ((secret, b) :: eraseVCtx Γ) .bool)
    (env : Env Val (eraseVCtx Γ)) :
    evalGuard (Player := P) (L := simpleExpr)
      (Expr.nullableCommitGuard R) Option.none env = true :=
  VegasLang.compileNullable_none_guard_legal R env

/-- Honest, non-null source actions keep exactly the source guard semantics
after nullable compilation. -/
theorem nullableCompile_preserves_honest_guard
    {P : Type} [DecidableEq P]
    {Γ : VCtx P simpleExpr} {secret : VarId} {b : BaseTy}
    [DefaultVal b]
    (R : Expr ((secret, b) :: eraseVCtx Γ) .bool)
    (v : Val b) (env : Env Val (eraseVCtx Γ)) :
    evalGuard (Player := P) (L := simpleExpr)
        (Expr.nullableCommitGuard R) (some v) env =
      evalGuard (Player := P) (L := simpleExpr) R v env :=
  VegasLang.compileNullable_some_guard_eq R v env

/-- The compiled nullable guard never deadlocks: `none` is a legal witness in
every environment. -/
theorem nullableCompile_guard_satisfiable
    {P : Type} [DecidableEq P]
    {Γ : VCtx P simpleExpr} {secret : VarId} {b : BaseTy}
    [DefaultVal b]
    (R : Expr ((secret, b) :: eraseVCtx Γ) .bool) :
    ∀ env : Env Val (eraseVCtx Γ),
      ∃ a : Val (.option b),
        evalGuard (Player := P) (L := simpleExpr)
          (Expr.nullableCommitGuard R) a env = true :=
  VegasLang.compileNullable_guard_satisfiable R

/-- A compiled yield is legal as soon as its continuation is legal. The new
commit site obtains its legal witness constructively from `none`. -/
theorem nullableCompile_yield_legal_of_continuation
    {P : Type} [DecidableEq P]
    {Γ : VCtx P simpleExpr}
    (secret pubVar : VarId) (who : P) {b : BaseTy}
    [CommitPayloadTy b] [DefaultVal b]
    (R : Expr ((secret, b) :: eraseVCtx Γ) .bool)
    (k : VegasLang P
      ((pubVar, .pub (BaseTy.option b)) ::
        (secret, .hidden who (BaseTy.option b)) :: Γ))
    (hk : Legal (VegasLang.compileNullable k)) :
    Legal (VegasLang.compileNullable
      (VegasLang.yield secret pubVar who R k)) :=
  VegasLang.compileNullable_yield_legal_of_continuation
    secret pubVar who R k hk

/- Strategic theorem targets, now stateable once payoff-penalty and
equilibrium-transport definitions are added:

theorem nullableCompile_none_strictly_dominated ...

Synthesized nullable abort moves are strictly dominated under the compiler's
penalty scheme.

theorem nullableCompile_equilibria_are_honest ...

Equilibrium/rationalizable behavior in the nullable game is honest: abort
moves have no strategic role after compilation.

theorem nullableCompile_no_honest_disadvantage ...

Backend abortability introduced by nullable compilation does not make honest
source players worse off.
-/


end Vegas
