import Vegas.Protocol.WF

/-!
# Big-step semantics for Vegas

The canonical denotational semantics of Vegas programs, together with the
normalization theorem used by the strategic and backend bridges.
-/

noncomputable def outcomeDist {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [E : Vegas.VisExprKit P L]
    [D : Vegas.VisDistKit P L]
    [U : Vegas.VisPayoffKit P L]
    (σ : Vegas.Profile P L) :
    {Γ : Vegas.VisCtx P L} →
      Vegas.Prog P L Γ →
      Vegas.VisEnv (Player := P) L Γ →
      FDist U.Outcome
  | _, .ret u, env =>
      FDist.pure (U.eval u env)
  | _, .letExpr x e k, env =>
      outcomeDist σ k <|
        Vegas.VisEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
          (E.eval e env) env
  | _, .sample x τ m D' k, env =>
      FDist.bind
        (D.eval D' (Vegas.VisEnv.projectDist (Player := P) (L := L) τ m env))
        (fun v =>
          outcomeDist σ k
            (Vegas.VisEnv.cons (Player := P) (L := L) (x := x) (τ := τ) v env))
  | _, .commit x who acts R k, env =>
      FDist.bind
        (σ.commit who x acts R (Vegas.VisEnv.toView (Player := P) (L := L) who env))
        (fun v =>
          outcomeDist σ k
            (Vegas.VisEnv.cons (Player := P) (L := L) (x := x) (τ := .hidden who _) v env))
  | _, .reveal y _who _x (b := b) hx k, env =>
      let v : L.Val b := Vegas.VisEnv.get (Player := P) (L := L) env hx
      outcomeDist σ k (Vegas.VisEnv.cons (Player := P) (L := L) (x := y) (τ := .pub b) v env)

theorem outcomeDist_totalWeight_eq_one {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [E : Vegas.VisExprKit P L]
    [D : Vegas.VisDistKit P L]
    [U : Vegas.VisPayoffKit P L]
    {Γ : Vegas.VisCtx P L} {σ : Vegas.Profile P L}
    {p : Vegas.Prog P L Γ} {env : Vegas.VisEnv (Player := P) L Γ}
    (hd : NormalizedDists p) (hσ : σ.NormalizedOn p) :
    (outcomeDist σ p env).totalWeight = 1 := by
  induction p with
  | ret u =>
      simp [outcomeDist, FDist.totalWeight_pure]
  | letExpr x e k ih =>
      exact ih hd hσ
  | sample x τ m D' k ih =>
      simp only [outcomeDist]
      exact FDist.totalWeight_bind_of_normalized (hd.1 _) (fun _ _ => ih hd.2 hσ)
  | commit x who acts R k ih =>
      simp only [outcomeDist]
      exact FDist.totalWeight_bind_of_normalized (hσ.1 _) (fun _ _ => ih hd hσ.2)
  | reveal y who x hx k ih =>
      exact ih hd hσ
