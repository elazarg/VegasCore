import GameTheory.Core.KernelGame
import Vegas.BigStep
import Vegas.Strategy.Behavioral

/-!
# Strategic semantics bridge

Vegas's `outcomeDist` produces `FDist (Outcome P)` — a Finsupp-based weighted
distribution over outcomes. The fixed-program behavioral carrier lives in
`Vegas.Strategy.Behavioral`; this file keeps the legacy evaluator and packages
that carrier as a `KernelGame`.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace OmniscientOperationalProfile

/-- An omniscient operational profile agrees with a fixed-program behavioral
profile at every commit site of `p`.

The raw evaluator consumes full erased environments. A behavioral profile
consumes player views. This predicate says that, along `p`, the raw full-state
kernel is exactly the behavioral kernel after projecting the full environment
to the active player's view.

This is a strong extensional condition over all environments, including
unreachable ones. A weaker reachable-environment version would need a
reachability-indexed profile agreement relation and is intentionally not
folded into this basic bridge. -/
def ExtendsBehavioralProfile (σ : OmniscientOperationalProfile P L) :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
      ProgramBehavioralProfile p → Prop
  | _, .ret _, _ => True
  | _, .letExpr _ _ k, β =>
      ExtendsBehavioralProfile σ k β
  | _, .sample _ _ k, β =>
      ExtendsBehavioralProfile σ k β
  | Γ, .commit x who R k, β =>
      (∀ ρ : Env L.Val (eraseVCtx Γ),
        σ.commit who x R ρ =
          ProgramBehavioralStrategy.headKernel (β who)
            (projectViewEnv who ρ)) ∧
      ExtendsBehavioralProfile σ k (ProgramBehavioralProfile.tail β)
  | _, .reveal _ _ _ _ k, β =>
      ExtendsBehavioralProfile σ k β

end OmniscientOperationalProfile

/-- Evaluate a fixed-program behavioral profile directly, threading the
continuation profile through the program structure. -/
noncomputable def outcomeDistBehavioral :
    {Γ : VCtx P L} →
      (p : VegasCore P L Γ) →
      ProgramBehavioralProfile p →
      VEnv (Player := P) L Γ →
      FDist (Outcome P)
  | _, .ret payoffs, _, env =>
      FDist.pure (evalPayoffs payoffs env)
  | _, .letExpr x e k, σ, env =>
      outcomeDistBehavioral k σ <|
        VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
          (L.eval e (VEnv.erasePubEnv env)) env
  | _, .sample x D' k, σ, env =>
      FDist.bind
        (L.evalDist D' (VEnv.eraseSampleEnv env))
        (fun v =>
          outcomeDistBehavioral k σ
            (VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _) v env))
  | _, .commit x who (b := b) _ k, σ, env =>
      let κ := ProgramBehavioralStrategy.headKernel (σ who)
      FDist.bind
        (κ (projectViewEnv who (VEnv.eraseEnv env)))
        (fun v =>
          outcomeDistBehavioral k (ProgramBehavioralProfile.tail σ)
            (VEnv.cons (Player := P) (L := L) (x := x)
              (τ := .hidden who b) v env))
  | _, .reveal y _who _x (b := b) hx k, σ, env =>
      let v : L.Val b := VEnv.get (Player := P) (L := L) env hx
      outcomeDistBehavioral k σ
        (VEnv.cons (Player := P) (L := L) (x := y) (τ := .pub b) v env)

/-- If an omniscient operational profile extends a fixed behavioral profile,
the raw denotational evaluator and the fixed-program behavioral evaluator
produce the same outcome distribution. -/
theorem outcomeDist_eq_outcomeDistBehavioral_of_extends
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    (σ : OmniscientOperationalProfile P L)
    (β : ProgramBehavioralProfile p)
    (env : VEnv (Player := P) L Γ)
    (hβ : σ.ExtendsBehavioralProfile p β) :
    outcomeDist σ p env = outcomeDistBehavioral p β env := by
  induction p with
  | ret payoffs =>
      rfl
  | letExpr x e k ih =>
      exact ih β
        (VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
          (L.eval e (VEnv.erasePubEnv env)) env) hβ
  | sample x D k ih =>
      simp only [outcomeDist, outcomeDistBehavioral]
      congr
      funext v
      exact ih β
        (VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _) v env) hβ
  | commit x who R k ih =>
      simp only [outcomeDist, outcomeDistBehavioral]
      rw [hβ.1 (VEnv.eraseEnv env)]
      congr
      funext v
      exact ih (ProgramBehavioralProfile.tail β)
        (VEnv.cons (Player := P) (L := L) (x := x)
          (τ := .hidden who _) v env) hβ.2
  | @reveal Γ y who x b hx k ih =>
      exact ih β
        (VEnv.cons (Player := P) (L := L) (x := y) (τ := .pub b)
          (show L.Val b from
            VEnv.get (Player := P) (L := L) (x := x)
              (τ := .hidden who b) env hx) env) hβ

/-- If a program is propositionally equal to `ret`, its behavioral outcome
distribution is the corresponding point mass. The strategy argument is
dependent on the program, so this lemma is often easier to use than rewriting
inside `outcomeDistBehavioral` directly. -/
theorem outcomeDistBehavioral_of_eq_ret
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    {payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)}
    (hp : p = VegasCore.ret payoffs)
    (σ : ProgramBehavioralProfile p)
    (env : VEnv (Player := P) L Γ) :
    outcomeDistBehavioral p σ env = FDist.pure (evalPayoffs payoffs env) := by
  cases hp
  rfl

theorem outcomeDistBehavioral_totalWeight_eq_one
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    {σ : ProgramBehavioralProfile p}
    {env : VEnv (Player := P) L Γ}
    (hd : NormalizedDists p) :
    (outcomeDistBehavioral p σ env).totalWeight = 1 := by
  induction p with
  | ret u =>
      simp [outcomeDistBehavioral, FDist.totalWeight_pure]
  | letExpr x e k ih =>
      exact ih hd
  | sample x D' k ih =>
      simp only [outcomeDistBehavioral]
      exact FDist.totalWeight_bind_of_normalized (hd.1 _) (fun _ _ => ih hd.2)
  | commit x who R k ih =>
      simp only [outcomeDistBehavioral]
      exact FDist.totalWeight_bind_of_normalized
        (ProgramBehavioralStrategy.headKernel_normalized (σ who) _)
        (fun _ _ => ih (σ := ProgramBehavioralProfile.tail σ) hd)
  | reveal y who x hx k ih =>
      exact ih hd

/-- Vegas denotational semantics as a `KernelGame` whose strategies are the
fixed program's local *guard-legal* behavioral strategies.

Consumes a `WFProgram` bundle. The `Strategy` field is the legal subtype
`LegalProgramBehavioralStrategy g`, so game-theoretic solution concepts
(Nash, dominance, etc.) applied to the resulting `KernelGame` quantify
only over strategies that respect every commit guard. `wf`, `normalized`,
and `legal` together carry the side conditions the Vegas protocol
requires; `normalized` is what proves the outcome kernel sums to `1`. -/
noncomputable def toKernelGame (g : WFProgram P L) : GameTheory.KernelGame P where
  Strategy := LegalProgramBehavioralStrategy g
  Outcome := Outcome P
  utility := fun o i => (o i : ℝ)
  outcomeKernel := fun σ =>
    (outcomeDistBehavioral g.prog (fun i => (σ i).val) g.env).toPMF
      (outcomeDistBehavioral_totalWeight_eq_one
        (p := g.prog) (σ := fun i => (σ i).val) g.normalized)

@[simp] theorem toKernelGame_outcomeKernel
    (g : WFProgram P L)
    (σ : LegalProgramBehavioralProfile g) :
    (toKernelGame g).outcomeKernel σ =
      (outcomeDistBehavioral g.prog (fun i => (σ i).val) g.env).toPMF
        (outcomeDistBehavioral_totalWeight_eq_one
          (p := g.prog) (σ := fun i => (σ i).val)
          g.normalized) := rfl

@[simp] theorem toKernelGame_udist
    (g : WFProgram P L)
    (σ : LegalProgramBehavioralProfile g) :
    (toKernelGame g).udist σ =
      ((outcomeDistBehavioral g.prog (fun i => (σ i).val) g.env).toPMF
        (outcomeDistBehavioral_totalWeight_eq_one
          (p := g.prog) (σ := fun i => (σ i).val)
          g.normalized)).bind
        (fun o => PMF.pure (fun i => (o i : ℝ))) := rfl

/-- Expected utility in the kernel game matches Vegas expected payoff. -/
theorem toKernelGame_eu
    (g : WFProgram P L)
    (σ : LegalProgramBehavioralProfile g) (who : P) :
    (toKernelGame g).eu σ who =
      (outcomeDistBehavioral g.prog (fun i => (σ i).val) g.env).sum
        (fun o w => (w : ℝ) * (o who : ℝ)) := by
  let hnorm :=
    outcomeDistBehavioral_totalWeight_eq_one
      (p := g.prog) (σ := fun i => (σ i).val) (env := g.env)
      g.normalized
  simpa [GameTheory.KernelGame.eu, toKernelGame, hnorm,
    NNRat.toNNReal_coe_real] using
    (FDist.expect_toPMF_eq_sum
      (d := outcomeDistBehavioral g.prog (fun i => (σ i).val) g.env)
      (h := hnorm)
      (f := fun o => (o who : ℝ)))

end Vegas
