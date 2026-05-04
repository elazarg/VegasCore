import Vegas.PureStrategic
import Vegas.Strategic
import Vegas.Strategy.Conversions
import Vegas.Strategy.PMFSemantics

/-!
# PMF Behavioral Strategic Semantics

This file mirrors `Vegas.Strategic` and `Vegas.PureStrategic` but uses `PMF`
(Mathlib's probability mass functions) instead of `FDist` (rational Finsupp
distributions). The PMF layer is needed for theorem backends that produce
real-valued behavioral strategies.

The PMF strategy carrier lives in `Vegas.Strategy.PMF`; the syntax-recursive
PMF evaluator lives in `Vegas.Strategy.PMFSemantics`; carrier conversions live
in `Vegas.Strategy.Conversions`. This file keeps the agreement theorems and
the PMF behavioral `KernelGame` presentation, whose public kernel is
machine-backed.

Key agreement theorems:
* `outcomeDistBehavioralPMF_toBehavioralPMF_eq` — pure lift through PMF layer
  agrees with `outcomeDistPure.toPMF`
* `outcomeDistBehavioralPMF_toPMFProfile_eq` — FDist behavioral converted to
  PMF agrees with `outcomeDistBehavioral.toPMF`
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

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

/-! ## PMF behavioral kernel game -/

/-- PMF-valued behavioral kernel game for a checked Vegas program.

Unlike `toKernelGame`, this game uses `PMF` behavioral strategies directly.
That matters for Kuhn mixed-to-behavioral results: an arbitrary mixed strategy
over pure profiles can induce real-valued behavioral probabilities, which need
not be representable by Vegas' rational `FDist` kernels.

The outcome kernel is the checked graph-machine kernel at the bundle's context
proof. -/
noncomputable def toKernelGamePMF (g : WFProgram P L) : GameTheory.KernelGame P :=
  toMachineKernelGamePMF g g.wctx

@[simp] theorem toKernelGamePMF_outcomeKernel
    (g : WFProgram P L) (σ : SyntaxLegalProgramBehavioralProfilePMF g) :
    (toKernelGamePMF g).outcomeKernel σ =
      (graphMachine g g.wctx).outcomeKernel
        (lawOfBehavioralPMF σ g.wctx).val (syntaxSteps g.prog) := rfl

@[simp] theorem toKernelGamePMF_udist
    (g : WFProgram P L) (σ : SyntaxLegalProgramBehavioralProfilePMF g) :
    (toKernelGamePMF g).udist σ =
      ((graphMachine g g.wctx).outcomeKernel
        (lawOfBehavioralPMF σ g.wctx).val (syntaxSteps g.prog)).bind
        (fun o : Outcome P => PMF.pure (fun i => (o i : ℝ))) := rfl

/-- The PMF conversion of an FDist behavioral profile has the same outcome
kernel as the original FDist-valued kernel game profile. -/
theorem toKernelGamePMF_outcomeKernel_toPMFProfile_eq_toKernelGame
    (g : WFProgram P L)
    (σ : LegalProgramBehavioralProfile g) :
    (toKernelGamePMF g).outcomeKernel
        (LegalProgramBehavioralProfile.toPMFProfile σ) =
      (toKernelGame g).outcomeKernel σ := by
  rfl

/-- The PMF behavioral lift of a legal pure profile has the same outcome
kernel as the fixed-program pure strategic form. -/
theorem toKernelGamePMF_outcomeKernel_eq_toStrategicKernelGame_toBehavioralPMF
    (g : WFProgram P L)
    (σ : LegalProgramPureProfile g) :
    (toKernelGamePMF g).outcomeKernel
        (LegalProgramPureProfile.toBehavioralPMF σ) =
      (toStrategicKernelGame g).outcomeKernel σ := by
  rfl

end Vegas
