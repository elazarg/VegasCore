import Vegas.Syntax.Strategy.PMF

/-!
# Fixed-program PMF behavioral outcome semantics

This module contains the syntax-recursive PMF outcome evaluator for PMF-valued
behavioral strategy profiles. It intentionally stays below the strategic
`KernelGame` packaging so observed-kernel and protocol-event-law code can
depend on the evaluator without importing the legacy strategic API.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Evaluate a fixed-program PMF behavioral profile directly, threading the
continuation profile through the program structure. At sample nodes, the FDist
from nature is converted to a PMF via `NormalizedDists`. -/
noncomputable def behavioralOutcomePMF :
    {Γ : VCtx P L} →
      (p : VegasCore P L Γ) →
      NormalizedDists p →
      ProgramBehavioralProfilePMF p →
      VEnv (Player := P) L Γ →
      PMF (Outcome P)
  | _, .ret payoffs, _, _, env =>
      PMF.pure (evalPayoffs payoffs env)
  | _, .letExpr x e k, hd, σ, env =>
      behavioralOutcomePMF k hd (fun w => match σ w with | .letExpr tail => tail) <|
        VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
          (L.eval e (VEnv.erasePubEnv env)) env
  | _, .sample x D' k, hd, σ, env =>
      ((L.evalDist D' (VEnv.eraseSampleEnv env)).toPMF (hd.1 env)).bind
        (fun v =>
          behavioralOutcomePMF k hd.2
            (fun w => match σ w with | .sample tail => tail)
            (VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _) v env))
  | _, .commit x who (b := b) _ k, hd, σ, env =>
      (ProgramBehavioralStrategyPMF.headKernel (σ who)
        (projectViewEnv who (VEnv.eraseEnv env))).bind
        (fun v =>
          behavioralOutcomePMF k hd
            (ProgramBehavioralProfilePMF.tail σ)
            (VEnv.cons (Player := P) (L := L) (x := x)
              (τ := .hidden who b) v env))
  | _, .reveal y _who _x (b := b) hx k, hd, σ, env =>
      let v : L.Val b := VEnv.get (Player := P) (L := L) env hx
      behavioralOutcomePMF k hd (fun w => match σ w with | .reveal tail => tail)
        (VEnv.cons (Player := P) (L := L) (x := y) (τ := .pub b) v env)

/-- At a commit node, `behavioralOutcomePMF` depends only on `headKernel` at
the current view and the tail's outcome distribution. -/
theorem behavioralOutcomePMF_commit_congr
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (hd : NormalizedDists (.commit x who R k))
    (σ₁ σ₂ : ProgramBehavioralProfilePMF (.commit x who R k))
    (env : VEnv (Player := P) L Γ)
    (hkernel :
      ProgramBehavioralStrategyPMF.headKernel (σ₁ who)
        (projectViewEnv who (VEnv.eraseEnv env)) =
      ProgramBehavioralStrategyPMF.headKernel (σ₂ who)
        (projectViewEnv who (VEnv.eraseEnv env)))
    (htail : ∀ v,
      behavioralOutcomePMF k hd
        (ProgramBehavioralProfilePMF.tail σ₁)
        (VEnv.cons (Player := P) (L := L) (x := x) (τ := .hidden who b) v env) =
      behavioralOutcomePMF k hd
        (ProgramBehavioralProfilePMF.tail σ₂)
        (VEnv.cons (Player := P) (L := L) (x := x) (τ := .hidden who b) v env)) :
    behavioralOutcomePMF (.commit x who R k) hd σ₁ env =
      behavioralOutcomePMF (.commit x who R k) hd σ₂ env := by
  simp only [behavioralOutcomePMF]
  rw [hkernel]; congr 1; funext v; exact htail v

end Vegas
