import Vegas.PureStrategic
import Vegas.Strategic
import Vegas.Strategy.Conversions
import Vegas.Strategy.PMF

/-!
# PMF Behavioral Strategic Semantics

This file mirrors `Vegas.Strategic` and `Vegas.PureStrategic` but uses `PMF`
(Mathlib's probability mass functions) instead of `FDist` (rational Finsupp
distributions). The PMF layer is needed for theorem backends that produce
real-valued behavioral strategies.

The PMF strategy carrier lives in `Vegas.Strategy.PMF`; carrier conversions
live in `Vegas.Strategy.Conversions`. This file keeps the PMF outcome evaluator
and legacy syntax-recursive PMF kernel-game packaging.

Key agreement theorems:
* `outcomeDistBehavioralPMF_toBehavioralPMF_eq` — pure lift through PMF layer
  agrees with `outcomeDistPure.toPMF`
* `outcomeDistBehavioralPMF_toPMFProfile_eq` — FDist behavioral converted to
  PMF agrees with `outcomeDistBehavioral.toPMF`
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-! ## PMF behavioral outcome distribution -/

/-- Evaluate a fixed-program PMF behavioral profile directly, threading the
continuation profile through the program structure. At sample nodes, the FDist
from nature is converted to a PMF via `NormalizedDists`. -/
noncomputable def outcomeDistBehavioralPMF :
    {Γ : VCtx P L} →
      (p : VegasCore P L Γ) →
      NormalizedDists p →
      ProgramBehavioralProfilePMF p →
      VEnv (Player := P) L Γ →
      PMF (Outcome P)
  | _, .ret payoffs, _, _, env =>
      PMF.pure (evalPayoffs payoffs env)
  | _, .letExpr x e k, hd, σ, env =>
      outcomeDistBehavioralPMF k hd (fun w => match σ w with | .letExpr tail => tail) <|
        VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
          (L.eval e (VEnv.erasePubEnv env)) env
  | _, .sample x D' k, hd, σ, env =>
      ((L.evalDist D' (VEnv.eraseSampleEnv env)).toPMF (hd.1 env)).bind
        (fun v =>
          outcomeDistBehavioralPMF k hd.2
            (fun w => match σ w with | .sample tail => tail)
            (VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _) v env))
  | _, .commit x who (b := b) _ k, hd, σ, env =>
      (ProgramBehavioralStrategyPMF.headKernel (σ who)
        (projectViewEnv who (VEnv.eraseEnv env))).bind
        (fun v =>
          outcomeDistBehavioralPMF k hd
            (ProgramBehavioralProfilePMF.tail σ)
            (VEnv.cons (Player := P) (L := L) (x := x)
              (τ := .hidden who b) v env))
  | _, .reveal y _who _x (b := b) hx k, hd, σ, env =>
      let v : L.Val b := VEnv.get (Player := P) (L := L) env hx
      outcomeDistBehavioralPMF k hd (fun w => match σ w with | .reveal tail => tail)
        (VEnv.cons (Player := P) (L := L) (x := y) (τ := .pub b) v env)

/-- At a commit node, `outcomeDistBehavioralPMF` depends only on `headKernel` at
the current view and the tail's outcome distribution. -/
theorem outcomeDistBehavioralPMF_commit_congr
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
      outcomeDistBehavioralPMF k hd
        (ProgramBehavioralProfilePMF.tail σ₁)
        (VEnv.cons (Player := P) (L := L) (x := x) (τ := .hidden who b) v env) =
      outcomeDistBehavioralPMF k hd
        (ProgramBehavioralProfilePMF.tail σ₂)
        (VEnv.cons (Player := P) (L := L) (x := x) (τ := .hidden who b) v env)) :
    outcomeDistBehavioralPMF (.commit x who R k) hd σ₁ env =
      outcomeDistBehavioralPMF (.commit x who R k) hd σ₂ env := by
  simp only [outcomeDistBehavioralPMF]
  rw [hkernel]; congr 1; funext v; exact htail v

/-! ## Agreement: pure lift through PMF = outcomeDistPure.toPMF -/

/-- Running the PMF behavioral lift of a pure profile yields the same outcome
distribution as `outcomeDistPure.toPMF`. -/
theorem outcomeDistBehavioralPMF_toBehavioralPMF_eq
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    (σ : ProgramPureProfile p)
    (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p) :
    outcomeDistBehavioralPMF p hd
      (ProgramPureProfile.toBehavioralPMF p σ) env =
      (outcomeDistPure p σ env).toPMF
        (outcomeDistPure_totalWeight_eq_one hd) := by
  induction p with
  | ret u =>
      simp [outcomeDistBehavioralPMF, outcomeDistPure, FDist.toPMF_pure]
  | letExpr x e k ih =>
      simpa [outcomeDistBehavioralPMF, outcomeDistPure,
        ProgramPureProfile.toBehavioralPMF] using ih σ _ hd
  | sample x D' k ih =>
      simp only [outcomeDistBehavioralPMF, outcomeDistPure]
      rw [FDist.toPMF_bind (L.evalDist D' (VEnv.eraseSampleEnv env))
        (fun v => outcomeDistPure k σ (VEnv.cons (Player := P) (L := L)
          (x := x) (τ := .pub _) v env))
        (hd.1 env)
        (fun v => outcomeDistPure_totalWeight_eq_one hd.2)]
      congr 1; funext v
      exact ih σ _ hd.2
  | commit x who R k ih =>
      simp only [outcomeDistBehavioralPMF, outcomeDistPure]
      have hhead :
          ProgramBehavioralStrategyPMF.headKernel
            ((ProgramPureProfile.toBehavioralPMF
              (.commit x who R k) σ) who)
            (projectViewEnv who (VEnv.eraseEnv env)) =
          PMF.pure
            ((ProgramPureStrategy.headKernel (σ who))
              (projectViewEnv who (VEnv.eraseEnv env))) := by
        simp [ProgramPureProfile.toBehavioralPMF, ProgramBehavioralStrategyPMF.headKernel,
          ProgramBehavioralKernelPMF.ofPure, ProgramPureStrategy.headKernel]
      rw [hhead, PMF.pure_bind]
      rw [ProgramPureProfile.tail_toBehavioralPMF]
      exact ih (ProgramPureProfile.tail σ)
        (VEnv.cons (Player := P) (L := L) (x := x) (τ := .hidden who _)
          ((ProgramPureStrategy.headKernel (σ who))
            (projectViewEnv who (VEnv.eraseEnv env))) env) hd
  | reveal y who x hx k ih =>
      simpa [outcomeDistBehavioralPMF, outcomeDistPure,
        ProgramPureProfile.toBehavioralPMF] using ih σ _ hd

/-! ## Agreement: FDist behavioral converted to PMF = outcomeDistBehavioral.toPMF -/

/-- Running the PMF conversion of an FDist behavioral profile yields the same
outcome distribution as `outcomeDistBehavioral.toPMF`. -/
theorem outcomeDistBehavioralPMF_toPMFProfile_eq
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    (σ : ProgramBehavioralProfile p)
    (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p) :
    outcomeDistBehavioralPMF p hd
      (ProgramBehavioralProfile.toPMFProfile p σ) env =
      (outcomeDistBehavioral p σ env).toPMF
        (outcomeDistBehavioral_totalWeight_eq_one hd) := by
  induction p with
  | ret u =>
      simp [outcomeDistBehavioralPMF, outcomeDistBehavioral, FDist.toPMF_pure]
  | letExpr x e k ih =>
      simpa [outcomeDistBehavioralPMF, outcomeDistBehavioral,
        ProgramBehavioralProfile.toPMFProfile] using ih σ _ hd
  | sample x D' k ih =>
      simp only [outcomeDistBehavioralPMF, outcomeDistBehavioral]
      rw [FDist.toPMF_bind (L.evalDist D' (VEnv.eraseSampleEnv env))
        (fun v => outcomeDistBehavioral k σ (VEnv.cons (Player := P) (L := L)
          (x := x) (τ := .pub _) v env))
        (hd.1 env)
        (fun v => outcomeDistBehavioral_totalWeight_eq_one hd.2)]
      congr 1; funext v
      exact ih σ _ hd.2
  | commit x who R k ih =>
      simp only [outcomeDistBehavioralPMF, outcomeDistBehavioral]
      -- The head kernel of the PMF profile is toPMF of the FDist head kernel
      have hhead :
          ProgramBehavioralStrategyPMF.headKernel
            ((ProgramBehavioralProfile.toPMFProfile
              (.commit x who R k) σ) who)
            (projectViewEnv who (VEnv.eraseEnv env)) =
          (ProgramBehavioralStrategy.headKernel (σ who)
            (projectViewEnv who (VEnv.eraseEnv env))).toPMF
          (ProgramBehavioralStrategy.headKernel_normalized (σ who)
            (projectViewEnv who (VEnv.eraseEnv env))) := by
        simp [ProgramBehavioralProfile.toPMFProfile,
          ProgramBehavioralStrategyPMF.headKernel,
          ProgramBehavioralKernelPMF.ofFDist,
          ProgramBehavioralStrategy.headKernel]
      rw [hhead]
      rw [FDist.toPMF_bind
        (ProgramBehavioralStrategy.headKernel (σ who)
          (projectViewEnv who (VEnv.eraseEnv env)))
        (fun v => outcomeDistBehavioral k
          (ProgramBehavioralProfile.tail σ)
          (VEnv.cons (Player := P) (L := L) (x := x) (τ := .hidden who _) v env))
        (ProgramBehavioralStrategy.headKernel_normalized (σ who)
          (projectViewEnv who (VEnv.eraseEnv env)))
        (fun v => outcomeDistBehavioral_totalWeight_eq_one
          (σ := ProgramBehavioralProfile.tail σ) hd)]
      congr 1; funext v
      rw [ProgramBehavioralProfile.tail_toPMFProfile]
      exact ih (ProgramBehavioralProfile.tail σ) _ hd
  | reveal y who x hx k ih =>
      simpa [outcomeDistBehavioralPMF, outcomeDistBehavioral,
        ProgramBehavioralProfile.toPMFProfile] using ih σ _ hd

/-! ## Syntax-recursive PMF behavioral kernel game -/

/-- PMF-valued syntax-recursive behavioral kernel game for a checked Vegas
program.

Unlike `toKernelGame`, this game uses `PMF` behavioral strategies directly.
That matters for Kuhn mixed-to-behavioral results: an arbitrary mixed strategy
over pure profiles can induce real-valued behavioral probabilities, which need
not be representable by Vegas' rational `FDist` kernels.

This is a syntax presentation. The primary checked-program PMF behavioral
carrier is the machine-derived `LegalProgramBehavioralProfilePMF` in
`Vegas.FOSG`; syntax-facing client APIs should be related to that IR carrier by
explicit equivalence theorems. -/
noncomputable def toKernelGamePMF (g : WFProgram P L) : GameTheory.KernelGame P where
  Strategy := SyntaxLegalProgramBehavioralStrategyPMF g
  Outcome := Outcome P
  utility := fun o i => (o i : ℝ)
  outcomeKernel := fun σ =>
    outcomeDistBehavioralPMF g.prog g.normalized (fun i => (σ i).val) g.env

@[simp] theorem toKernelGamePMF_outcomeKernel
    (g : WFProgram P L) (σ : SyntaxLegalProgramBehavioralProfilePMF g) :
    (toKernelGamePMF g).outcomeKernel σ =
      outcomeDistBehavioralPMF g.prog g.normalized (fun i => (σ i).val) g.env := rfl

@[simp] theorem toKernelGamePMF_udist
    (g : WFProgram P L) (σ : SyntaxLegalProgramBehavioralProfilePMF g) :
    (toKernelGamePMF g).udist σ =
      PMF.map (fun o : Outcome P => fun i => (o i : ℝ))
        (outcomeDistBehavioralPMF g.prog g.normalized
          (fun i => (σ i).val) g.env) := by
  rfl

/-- The PMF conversion of an FDist behavioral profile has the same outcome
kernel as the original FDist-valued kernel game profile. -/
theorem toKernelGamePMF_outcomeKernel_toPMFProfile_eq_toKernelGame
    (g : WFProgram P L)
    (σ : LegalProgramBehavioralProfile g) :
    (toKernelGamePMF g).outcomeKernel
        (LegalProgramBehavioralProfile.toPMFProfile σ) =
      (toKernelGame g).outcomeKernel σ := by
  let raw : ProgramBehavioralProfile g.prog := fun i => (σ i).val
  have heq :
      outcomeDistBehavioralPMF g.prog g.normalized
          (fun i =>
            ((LegalProgramBehavioralProfile.toPMFProfile σ) i).val)
          g.env =
        (outcomeDistBehavioral g.prog raw g.env).toPMF
          (outcomeDistBehavioral_totalWeight_eq_one
            (p := g.prog) (σ := raw) g.normalized) := by
    simpa [raw, LegalProgramBehavioralProfile.toPMFProfile] using
      outcomeDistBehavioralPMF_toPMFProfile_eq
        (p := g.prog) (σ := raw) (env := g.env) (hd := g.normalized)
  simpa [toKernelGamePMF_outcomeKernel, toKernelGame_outcomeKernel, raw]
    using heq

/-- The PMF behavioral lift of a legal pure profile has the same outcome
kernel as the fixed-program pure strategic form. -/
theorem toKernelGamePMF_outcomeKernel_eq_toStrategicKernelGame_toBehavioralPMF
    (g : WFProgram P L)
    (σ : LegalProgramPureProfile g) :
    (toKernelGamePMF g).outcomeKernel
        (LegalProgramPureProfile.toBehavioralPMF σ) =
      (toStrategicKernelGame g).outcomeKernel σ := by
  have heq :
      outcomeDistBehavioralPMF g.prog g.normalized
          (fun i => ((LegalProgramPureProfile.toBehavioralPMF (g := g) σ) i).val)
          g.env =
        (outcomeDistPure g.prog (fun i => (σ i).val) g.env).toPMF
          (outcomeDistPure_totalWeight_eq_one
            (p := g.prog) (σ := fun i => (σ i).val)
            g.normalized) :=
    outcomeDistBehavioralPMF_toBehavioralPMF_eq
      (p := g.prog)
      (σ := fun i => (σ i).val) (env := g.env) (hd := g.normalized)
  simp only [toKernelGamePMF_outcomeKernel, toStrategicKernelGame_outcomeKernel,
    heq]

end Vegas
