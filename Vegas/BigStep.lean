import Vegas.WF

/-!
# Big-step semantics for Vegas

The canonical denotational semantics of Vegas programs, together with the
normalization theorem used by the strategic and backend bridges.
-/

namespace Vegas

noncomputable def outcomeDist {P : Type} [DecidableEq P]
    {L : Vegas.IExpr}
    (σ : Vegas.OmniscientOperationalProfile P L) :
    {Γ : Vegas.VCtx P L} →
      Vegas.VegasCore P L Γ →
      Vegas.VEnv (Player := P) L Γ →
      FDist (Outcome P)
  | _, .ret payoffs, env =>
      FDist.pure (evalPayoffs payoffs env)
  | _, .letExpr x e k, env =>
      outcomeDist σ k <|
        Vegas.VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
          (L.eval e (VEnv.erasePubEnv env)) env
  | _, .sample x D' k, env =>
      FDist.bind
        (L.evalDist D' (VEnv.eraseSampleEnv env))
        (fun v =>
          outcomeDist σ k
            (Vegas.VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _) v env))
  | _, .commit x who R k, env =>
      FDist.bind
        (σ.commit who x R (Vegas.VEnv.eraseEnv env))
        (fun v =>
          outcomeDist σ k
            (Vegas.VEnv.cons (Player := P) (L := L) (x := x)
              (τ := .hidden who _) v env))
  | _, .reveal y _who _x (b := b) hx k, env =>
      let v : L.Val b := Vegas.VEnv.get (Player := P) (L := L) env hx
      outcomeDist σ k
        (Vegas.VEnv.cons (Player := P) (L := L) (x := y) (τ := .pub b) v env)

theorem outcomeDist_totalWeight_eq_one {P : Type} [DecidableEq P]
    {L : Vegas.IExpr}
    {Γ : Vegas.VCtx P L} {σ : Vegas.OmniscientOperationalProfile P L}
    {p : Vegas.VegasCore P L Γ} {env : Vegas.VEnv (Player := P) L Γ}
    (hd : NormalizedDists p) (hσ : σ.NormalizedOn p) :
    (outcomeDist σ p env).totalWeight = 1 := by
  induction p with
  | ret u =>
      simp [outcomeDist, FDist.totalWeight_pure]
  | letExpr x e k ih =>
      exact ih hd hσ
  | sample x D' k ih =>
      simp only [outcomeDist]
      exact FDist.totalWeight_bind_of_normalized (hd.1 _) (fun _ _ => ih hd.2 hσ)
  | commit x who R k ih =>
      simp only [outcomeDist]
      exact FDist.totalWeight_bind_of_normalized (hσ.1 _) (fun _ _ => ih hd hσ.2)
  | reveal y who x hx k ih =>
      exact ih hd hσ

/-! ## Order-independence of independent commits and reveals

Independent commit/reveal pairs commute under `outcomeDist`. This is a
direct property of the big-step semantics; no auxiliary trace formulation
is needed. -/

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Two adjacent commits with independent strategies produce the same
outcome distribution regardless of order. Independence is expressed
directly as pointwise equality of strategy outputs on the swapped
environments. -/
theorem outcomeDist_comm_commit
    {Γ : VCtx P L} {σ : OmniscientOperationalProfile P L} {env : VEnv L Γ}
    {x₁ : VarId} {who₁ : P} {b₁ : L.Ty}
    {R₁ : L.Expr ((x₁, b₁) :: eraseVCtx Γ) L.bool}
    {x₂ : VarId} {who₂ : P} {b₂ : L.Ty}
    {R₂ : L.Expr ((x₂, b₂) :: eraseVCtx
      ((x₁, .hidden who₁ b₁) :: Γ)) L.bool}
    {k : VegasCore P L
      ((x₂, .hidden who₂ b₂) :: (x₁, .hidden who₁ b₁) :: Γ)}
    {R₂' : L.Expr ((x₂, b₂) :: eraseVCtx Γ) L.bool}
    {R₁' : L.Expr ((x₁, b₁) :: eraseVCtx
      ((x₂, .hidden who₂ b₂) :: Γ)) L.bool}
    {k' : VegasCore P L
      ((x₁, .hidden who₁ b₁) :: (x₂, .hidden who₂ b₂) :: Γ)}
    (hk_eq : ∀ (v₁ : L.Val b₁) (v₂ : L.Val b₂)
        (e : VEnv L Γ),
      outcomeDist σ k (VEnv.cons v₂ (VEnv.cons v₁ e)) =
      outcomeDist σ k' (VEnv.cons v₁ (VEnv.cons v₂ e)))
    (hσ₁ : ∀ (v₂ : L.Val b₂) (e : VEnv L Γ),
      σ.commit who₁ x₁ R₁ (VEnv.eraseEnv e) =
      σ.commit who₁ x₁ R₁'
        (VEnv.eraseEnv (VEnv.cons (τ := .hidden who₂ b₂) v₂ e)))
    (hσ₂ : ∀ (v₁ : L.Val b₁) (e : VEnv L Γ),
      σ.commit who₂ x₂ R₂
        (VEnv.eraseEnv (VEnv.cons (τ := .hidden who₁ b₁) v₁ e)) =
      σ.commit who₂ x₂ R₂' (VEnv.eraseEnv e)) :
    outcomeDist σ
      (.commit x₁ who₁ R₁
        (.commit x₂ who₂ R₂ k)) env =
    outcomeDist σ
      (.commit x₂ who₂ R₂'
        (.commit x₁ who₁ R₁' k')) env := by
  simp only [outcomeDist]
  simp_rw [hσ₂ _ env]
  rw [FDist.bind_comm]
  congr 1; funext v₂
  rw [hσ₁ v₂ env]
  congr 1; funext v₁
  exact hk_eq v₁ v₂ env

/-- Two adjacent reveals of distinct hidden variables produce the same
outcome distribution regardless of order. -/
theorem outcomeDist_comm_reveal
    {Γ : VCtx P L} {σ : OmniscientOperationalProfile P L} {env : VEnv L Γ}
    {y₁ : VarId} {who₁ : P} {x₁ : VarId} {b₁ : L.Ty}
    {hx₁ : VHasVar (L := L) Γ x₁ (.hidden who₁ b₁)}
    {y₂ : VarId} {who₂ : P} {x₂ : VarId} {b₂ : L.Ty}
    {hx₂ : VHasVar (L := L) Γ x₂ (.hidden who₂ b₂)}
    {k : VegasCore P L ((y₂, .pub b₂) :: (y₁, .pub b₁) :: Γ)}
    {k' : VegasCore P L ((y₁, .pub b₁) :: (y₂, .pub b₂) :: Γ)}
    (hk_eq : ∀ (v₁ : L.Val b₁) (v₂ : L.Val b₂)
        (e : VEnv L Γ),
      outcomeDist σ k (VEnv.cons v₂ (VEnv.cons v₁ e)) =
      outcomeDist σ k' (VEnv.cons v₁ (VEnv.cons v₂ e))) :
    outcomeDist σ
      (.reveal y₁ who₁ x₁ hx₁
        (.reveal y₂ who₂ x₂ hx₂.there k)) env =
    outcomeDist σ
      (.reveal y₂ who₂ x₂ hx₂
        (.reveal y₁ who₁ x₁ hx₁.there k')) env := by
  simp only [outcomeDist]
  exact hk_eq (VEnv.get env hx₁) (VEnv.get env hx₂) env

end Vegas
