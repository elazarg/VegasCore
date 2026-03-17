import distilled.Vegas
import Math.Probability
import GameTheory.Core.KernelGame
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Monadic bridge: FDist → PMF

Vegas's `outcomeDist` produces `FDist Outcome` — a Finsupp-based weighted
distribution over outcomes. This file connects them to probability theory
via `FDist.toPMF`.

Note: constructing a valid `PMF` from an `FDist` requires the weights to sum
to 1 (as `ℝ≥0∞`). The `outcomeDist_totalWeight_eq_one` theorem guarantees this
when all distributions are normalized.
-/

-- ============================================================================
-- § 1. NNRat → NNReal cast
-- ============================================================================

/-- Canonical embedding ℚ≥0 → ℝ≥0. -/
noncomputable def NNRat.toNNReal (q : ℚ≥0) : NNReal :=
  ⟨((q : ℚ) : ℝ), by exact_mod_cast q.coe_nonneg⟩

-- ============================================================================
-- § 2. NNRat.toNNReal preserves algebraic structure
-- ============================================================================

theorem NNRat.toNNReal_one : NNRat.toNNReal 1 = 1 := by
  unfold NNRat.toNNReal; ext; push_cast; ring

theorem NNRat.toNNReal_zero : NNRat.toNNReal 0 = 0 := by
  unfold NNRat.toNNReal; ext; push_cast; ring

theorem NNRat.toNNReal_add (a b : ℚ≥0) :
    NNRat.toNNReal (a + b) = NNRat.toNNReal a + NNRat.toNNReal b := by
  unfold NNRat.toNNReal; ext; push_cast; ring

theorem NNRat.toNNReal_mul (a b : ℚ≥0) :
    NNRat.toNNReal (a * b) = NNRat.toNNReal a * NNRat.toNNReal b := by
  unfold NNRat.toNNReal; ext; push_cast; ring

theorem NNRat.toNNReal_coe_real (q : ℚ≥0) :
    ((NNRat.toNNReal q : NNReal) : ℝ) = (q : ℝ) := by
  rfl

theorem NNRat.toNNReal_finset_sum {α : Type} (s : Finset α) (f : α → ℚ≥0) :
    NNRat.toNNReal (s.sum f) = s.sum (fun a => NNRat.toNNReal (f a)) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [NNRat.toNNReal_zero]
  · intro a s ha hs
    simp [Finset.sum_insert, ha, NNRat.toNNReal_add, hs]

-- ============================================================================
-- § 3. FDist → PMF (sketch, requires normalization proof)
-- ============================================================================

/-- Convert a normalized finitely-supported distribution into a `PMF`. -/
noncomputable def FDist.toPMF {α : Type} [DecidableEq α]
    (d : FDist α) (h : d.totalWeight = 1) : PMF α :=
  PMF.ofFinset
    (fun a => (NNRat.toNNReal (d a) : ENNReal))
    d.support
    (by
      have hsum : d.support.sum (fun a => d a) = 1 := by
        simpa [FDist.totalWeight, Finsupp.sum] using h
      calc
        d.support.sum (fun a => ((NNRat.toNNReal (d a) : NNReal) : ENNReal))
            = ((d.support.sum fun a => NNRat.toNNReal (d a) : NNReal) : ENNReal) := by
                rw [← ENNReal.coe_finset_sum]
        _ = (NNRat.toNNReal (d.support.sum fun a => d a) : ENNReal) := by
              rw [NNRat.toNNReal_finset_sum]
        _ = 1 := by simp [hsum, NNRat.toNNReal_one])
    (by
      intro a ha
      have hz : d a = 0 := by
        simpa [Finsupp.mem_support_iff] using ha
      simp [hz, NNRat.toNNReal_zero])

-- ============================================================================
-- § 3a. toPMF monad homomorphism lemmas
-- ============================================================================

/-- `toPMF` applied at a point equals the cast of the original weight. -/
theorem FDist.toPMF_apply {α : Type} [DecidableEq α]
    (d : FDist α) (h : d.totalWeight = 1) (a : α) :
    (d.toPMF h) a = (NNRat.toNNReal (d a) : ENNReal) := by
  simp [FDist.toPMF, PMF.ofFinset_apply]

/-- `toPMF` converts `FDist.pure` to `PMF.pure`. -/
theorem FDist.toPMF_pure [DecidableEq α] (a : α) :
    (FDist.pure a).toPMF (FDist.totalWeight_pure a) = PMF.pure a := by
  ext b
  rw [toPMF_apply]
  simp only [FDist.pure, PMF.pure_apply]
  rw [Finsupp.single_apply]
  split
  · next h => subst h; simp [NNRat.toNNReal_one]
  · next h => simp [NNRat.toNNReal_zero, Ne.symm h]

/-- `toPMF` converts `FDist.map` to `PMF.map`. -/
theorem FDist.toPMF_map [DecidableEq α] [DecidableEq β]
    (d : FDist α) (f : α → β) (h : d.totalWeight = 1)
    (hmap : (d.map f).totalWeight = 1) :
    (d.map f).toPMF hmap = (d.toPMF h).map f := by
  ext b
  rw [toPMF_apply]
  simp only [PMF.map_apply, toPMF_apply]
  rw [FDist.map_apply]
  -- Collapse tsum to finite sum over d.support
  rw [tsum_eq_sum (s := d.support) (fun a ha => by
    have hz : d a = 0 := by simpa [Finsupp.mem_support_iff] using ha
    simp [hz, NNRat.toNNReal_zero])]
  -- LHS: ↑(∑ a, if f a = b then d a else 0).toNNReal
  -- RHS: ∑ a, if b = f a then ↑(d a).toNNReal else 0
  -- Push NNRat.toNNReal through the sum, then cast to ENNReal
  have hlhs : ((∑ a ∈ d.support, if f a = b then d a else 0).toNNReal : ENNReal) =
      ∑ a ∈ d.support, ((if f a = b then d a else 0).toNNReal : ENNReal) := by
    rw [NNRat.toNNReal_finset_sum, ENNReal.coe_finset_sum]
  rw [hlhs]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hfab : f a = b
  · simp [hfab]
  · simp [hfab, Ne.symm hfab, NNRat.toNNReal_zero]

/-- Pointwise `toPMF` of `FDist.bind`: the weight at `b` is the finite sum
of products `d(a) * f(a)(b)`, cast to `ℝ≥0∞`. This is the core bridge lemma
for converting `FDist.bind` chains to `PMF` computations. -/
theorem FDist.toPMF_bind_apply [DecidableEq α] [DecidableEq β]
    (d : FDist α) (f : α → FDist β)
    (hbind : (d.bind f).totalWeight = 1) (b : β) :
    ((d.bind f).toPMF hbind) b =
    d.support.sum (fun a =>
      (NNRat.toNNReal (d a) : ENNReal) * (NNRat.toNNReal ((f a) b) : ENNReal)) := by
  rw [toPMF_apply, bind_apply]
  -- LHS: ↑(∑ a ∈ d.support, d a * (f a) b).toNNReal
  -- RHS: ∑ a ∈ d.support, ↑(d a).toNNReal * ↑((f a) b).toNNReal
  rw [show ((d.support.sum fun a => d a * (f a) b).toNNReal : ENNReal) =
      d.support.sum (fun a => ((d a * (f a) b).toNNReal : ENNReal)) from by
    rw [NNRat.toNNReal_finset_sum, ENNReal.coe_finset_sum]]
  apply Finset.sum_congr rfl
  intro a _
  rw [NNRat.toNNReal_mul, ENNReal.coe_mul]

/-- `toPMF` commutes with `bind` when `f` is normalized everywhere.

When `f` is normalized only on `d.support`, one would need a guard in the RHS
(or collapse the tsum to a finite sum). But when `f a` has totalWeight 1 for
all `a`, the conversion is clean. -/
theorem FDist.toPMF_bind [DecidableEq α] [DecidableEq β]
    (d : FDist α) (f : α → FDist β)
    (hd : d.totalWeight = 1)
    (hf : ∀ a, FDist.totalWeight (f a) = 1)
    (hbind : (FDist.bind d f).totalWeight = 1) :
    (FDist.bind d f).toPMF hbind =
      (d.toPMF hd).bind (fun a => (f a).toPMF (hf a)) := by
  ext b
  rw [toPMF_bind_apply]
  -- RHS: ∑' a, (d.toPMF hd) a * ((f a).toPMF (hf a)) b
  simp only [PMF.bind_apply, toPMF_apply]
  -- Collapse tsum to sum over d.support
  rw [tsum_eq_sum (s := d.support) (fun a ha => by
    have hz : d a = 0 := by simpa [Finsupp.mem_support_iff] using ha
    simp [hz, NNRat.toNNReal_zero])]

-- ============================================================================
-- § 4. Vegas outcome kernel (statement)
-- ============================================================================

/-- A player's Vegas strategy component, bundled with normalization. -/
structure PlayerStrategy (who : Player) where
  commit : {Γ : Ctx} → {b : BaseTy} → (x : VarId) →
    (acts : List (Val b)) →
    (R : Expr ((x, .pub b) :: flattenCtx (viewCtx who Γ)) .bool) →
    CommitKernel who Γ b
  normalized : {Γ : Ctx} → {b : BaseTy} → (x : VarId) →
    (acts : List (Val b)) →
    (R : Expr ((x, .pub b) :: flattenCtx (viewCtx who Γ)) .bool) →
    (view : Env (viewCtx who Γ)) →
    FDist.totalWeight (commit x acts R view) = 1

/-- Assemble per-player strategy components into a Vegas `Profile`. -/
def toProfile (σ : ∀ who, PlayerStrategy who) : Profile where
  commit := fun who x acts R view => (σ who).commit x acts R view

/-- Bundled player strategies are normalized on every Vegas program. -/
theorem toProfile_normalizedOn (σ : ∀ who, PlayerStrategy who) (p : Prog Γ) :
    (toProfile σ).NormalizedOn p := by
  induction p with
  | ret u =>
      trivial
  | letExpr x e k ih =>
      exact ih
  | sample x τ m D k ih =>
      exact ih
  | commit x who acts R k ih =>
      exact ⟨(fun view => (σ who).normalized x acts R view), ih⟩
  | reveal y who x hx k ih =>
      exact ih

/-- Expectation under `FDist.toPMF` reduces to a finite sum over support. -/
theorem FDist.expect_toPMF_eq_sum {α : Type} [DecidableEq α]
    (d : FDist α) (h : d.totalWeight = 1) (f : α → ℝ) :
    Math.Probability.expect (d.toPMF h) f =
      d.support.sum (fun a => ((NNRat.toNNReal (d a) : NNReal) : ℝ) * f a) := by
  unfold Math.Probability.expect
  rw [tsum_eq_sum (s := d.support)]
  · refine Finset.sum_congr rfl ?_
    intro a ha
    simp [FDist.toPMF]
  · intro a ha
    have hz : d a = 0 := by
      simpa [Finsupp.mem_support_iff] using ha
    simp [FDist.toPMF, hz, NNRat.toNNReal_zero]

namespace Vegas

/-- Vegas denotational semantics as a `KernelGame`, over normalized strategies. -/
noncomputable def toKernelGame (p : Prog Γ) (env : Env Γ)
    (hd : NormalizedDists p) : GameTheory.KernelGame Player where
  Strategy := PlayerStrategy
  Outcome := Outcome
  utility := fun o i => (payoffKit.payoff o i : ℝ)
  outcomeKernel := fun σ =>
    let prof := toProfile σ
    (outcomeDist prof p env).toPMF (outcomeDist_totalWeight_eq_one hd (toProfile_normalizedOn σ p))

/-- Expected utility in the restricted kernel game matches Vegas expected payoff. -/
theorem toKernelGame_eu (p : Prog Γ) (env : Env Γ) (hd : NormalizedDists p)
    (σ : ∀ who, PlayerStrategy who) (who : Player) :
    (toKernelGame p env hd).eu σ who =
      (outcomeDist (toProfile σ) p env).sum
        (fun o w => (w : ℝ) * (payoffKit.payoff o who : ℝ)) := by
  let hnorm :=
    outcomeDist_totalWeight_eq_one (env := env) hd (toProfile_normalizedOn σ p)
  simpa [GameTheory.KernelGame.eu, toKernelGame, hnorm, NNRat.toNNReal_coe_real] using
    (FDist.expect_toPMF_eq_sum
      (d := outcomeDist (toProfile σ) p env)
      (h := hnorm)
      (f := fun o => (payoffKit.payoff o who : ℝ)))

end Vegas

