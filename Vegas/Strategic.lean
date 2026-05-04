import GameTheory.Core.KernelGame
import Vegas.Protocol.Strategic
import Vegas.Strategy.Behavioral

/-!
# Strategic semantics bridge

The fixed-program behavioral carrier lives in `Vegas.Strategy.Behavioral`;
this file keeps the legacy behavioral evaluator for compatibility. The public
`toKernelGame` constructor is machine-backed.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

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

This is the public behavioral strategic form. Its outcome kernel is the
checked graph-machine kernel at the program bundle's context proof. -/
noncomputable def toKernelGame (g : WFProgram P L) : GameTheory.KernelGame P :=
  toMachineKernelGame g g.wctx

@[simp] theorem toKernelGame_outcomeKernel
    (g : WFProgram P L)
    (σ : LegalProgramBehavioralProfile g) :
    (toKernelGame g).outcomeKernel σ =
      (graphMachine g g.wctx).outcomeKernel
        (lawOfBehavioral σ g.wctx).val (syntaxSteps g.prog) := rfl

@[simp] theorem toKernelGame_udist
    (g : WFProgram P L)
    (σ : LegalProgramBehavioralProfile g) :
    (toKernelGame g).udist σ =
      ((graphMachine g g.wctx).outcomeKernel
        (lawOfBehavioral σ g.wctx).val (syntaxSteps g.prog)).bind
        (fun o : Outcome P => PMF.pure (fun i => (o i : ℝ))) := rfl

/-- `toKernelGame` is the machine-native behavioral kernel at `g.wctx`. -/
theorem toKernelGame_eu
    (g : WFProgram P L)
    (σ : LegalProgramBehavioralProfile g) (who : P) :
    (toKernelGame g).eu σ who =
      (toMachineKernelGame g g.wctx).eu σ who := rfl

end Vegas
