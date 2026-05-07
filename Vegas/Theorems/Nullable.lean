import Vegas.Lang.Nullable
import Vegas.Strategy

/-!
# Nullable Compilation Theorems

Project-facing names for the nullable compilation boundary and for strategy
claims that can be stated over any checked nullable backend game. The strategic
claims are parameterized by the semantic facts that identify abort moves and
prove the relevant repair/dominance property.
-/

namespace Vegas

open GameTheory

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

/-- If a strategy using a nullable abort is marked bad by a strict-domination
repair, then the repaired strategy strictly dominates it. The repair object is
where a particular program proves that its abort penalty makes aborting
unprofitable. -/
theorem nullableCompile_none_strictly_dominated
    {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}
    {g : WFProgram P L} [FiniteDomains g] {who : P}
    (R : StrictDominationRepair g who)
    {s : Strategy g who}
    (hbad : R.Bad s) :
    StrictlyDominates g who (R.repair s) s :=
  R.dominates_bad s hbad

/-- Pure-strategy counterpart of
`nullableCompile_none_strictly_dominated`. -/
theorem nullableCompile_none_strictly_dominated_pure
    {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}
    {g : WFProgram P L} [FiniteDomains g] {who : P}
    (R : PureStrictDominationRepair g who)
    {s : pureStrategyAt g who}
    (hbad : R.Bad s) :
    PureStrictlyDominates g who (R.repair s) s :=
  R.dominates_bad s hbad

/-- If each player's nullable-abort-using strategies are exactly the bad
strategies of a strict-domination repair, then every Nash profile avoids
nullable abort moves. -/
theorem nullableCompile_equilibria_are_honest
    {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}
    {g : WFProgram P L} [FiniteDomains g]
    (Abort :
      ∀ who, StrategyInfoState g who → StrategyMove g who → Prop)
    (Repair : ∀ who, StrictDominationRepair g who)
    (hbad :
      ∀ who s,
        (Repair who).Bad s ↔
          ¬ BehavioralStrategyAvoids g who (Abort who) s)
    {σ : StrategyProfile g}
    (hN : IsNash g σ) :
    BehavioralProfileAvoids g Abort σ := by
  intro who
  by_contra habort
  exact (Repair who).nash_avoids_bad hN ((hbad who (σ who)).mpr habort)

/-- Pure-strategy counterpart of `nullableCompile_equilibria_are_honest`. -/
theorem nullableCompile_pure_equilibria_are_honest
    {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}
    {g : WFProgram P L} [FiniteDomains g]
    (Abort :
      ∀ who, StrategyInfoState g who → StrategyMove g who → Prop)
    (Repair : ∀ who, PureStrictDominationRepair g who)
    (hbad :
      ∀ who s,
        (Repair who).Bad s ↔
          ¬ PureStrategyAvoids g who (Abort who) s)
    {σ : pureProfileAt g}
    (hN : IsPureNash g σ) :
    PureProfileAvoids g Abort σ := by
  intro who
  by_contra habort
  exact (Repair who).nash_avoids_bad hN ((hbad who (σ who)).mpr habort)

/-- An EU-preserving strategy morphism from a source game into a nullable
backend game says that honest compiled play preserves source expected utility.
-/
theorem nullableCompile_preserves_honest_profile_eu
    {P : Type} [DecidableEq P] [Fintype P] {L₁ L₂ : IExpr}
    {source : WFProgram P L₁} [FiniteDomains source]
    {target : WFProgram P L₂} [FiniteDomains target]
    (F : BehavioralStrategyMorphism source target)
    (σ : StrategyProfile source) (who : P) :
    eu target (F.mapProfile σ) who = eu source σ who :=
  F.mapProfile_eu_eq σ who

/-- Honest compiled play is never worse for any player when the honest
embedding is EU-preserving. This is the weak-preference form of
`nullableCompile_preserves_honest_profile_eu`. -/
theorem nullableCompile_no_honest_disadvantage
    {P : Type} [DecidableEq P] [Fintype P] {L₁ L₂ : IExpr}
    {source : WFProgram P L₁} [FiniteDomains source]
    {target : WFProgram P L₂} [FiniteDomains target]
    (F : BehavioralStrategyMorphism source target)
    (σ : StrategyProfile source) (who : P) :
    eu target (F.mapProfile σ) who ≥ eu source σ who := by
  rw [F.mapProfile_eu_eq σ who]

/-- Pure-strategy version of honest-profile EU preservation. -/
theorem nullableCompile_preserves_honest_pure_profile_eu
    {P : Type} [DecidableEq P] [Fintype P] {L₁ L₂ : IExpr}
    {source : WFProgram P L₁} [FiniteDomains source]
    {target : WFProgram P L₂} [FiniteDomains target]
    (F : PureStrategyMorphism source target)
    (σ : pureProfileAt source) (who : P) :
    (pureKernelGame target).eu (F.mapProfile σ) who =
      (pureKernelGame source).eu σ who :=
  F.mapProfile_eu_eq σ who

/-- Pure-strategy weak-preference form of no honest disadvantage. -/
theorem nullableCompile_no_honest_pure_disadvantage
    {P : Type} [DecidableEq P] [Fintype P] {L₁ L₂ : IExpr}
    {source : WFProgram P L₁} [FiniteDomains source]
    {target : WFProgram P L₂} [FiniteDomains target]
    (F : PureStrategyMorphism source target)
    (σ : pureProfileAt source) (who : P) :
    (pureKernelGame target).eu (F.mapProfile σ) who ≥
      (pureKernelGame source).eu σ who := by
  rw [F.mapProfile_eu_eq σ who]



end Vegas
