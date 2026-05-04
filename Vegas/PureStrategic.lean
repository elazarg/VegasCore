import GameTheory.Core.KernelGame
import GameTheory.Concepts.SolutionConcepts
import GameTheory.Core.GameProperties
import Vegas.Finite
import Vegas.Strategic
import Vegas.Strategy.Conversions
import Vegas.Strategy.Pure

/-!
# Fixed-Program Pure Strategic Form

This file defines the pure strategic form for a fixed Vegas program.

Unlike a global policy space over all contexts and guards, `ProgramPureStrategy
who p` contains one deterministic choice rule for each commit site of the fixed
program `p` owned by `who`. The carrier itself lives in `Vegas.Strategy.Pure`.
This file keeps the legacy pure outcome evaluator for compatibility; the public
pure `KernelGame` constructor is machine-backed.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Evaluate a fixed-program pure profile directly, threading the continuation
profile through the program structure. -/
noncomputable def outcomeDistPure :
    {Γ : VCtx P L} →
      (p : VegasCore P L Γ) →
      ProgramPureProfile p →
      VEnv (Player := P) L Γ →
      FDist (Outcome P)
  | _, .ret payoffs, _, env =>
      FDist.pure (evalPayoffs payoffs env)
  | _, .letExpr x e k, σ, env =>
      outcomeDistPure k σ <|
        VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
          (L.eval e (VEnv.erasePubEnv env)) env
  | _, .sample x D' k, σ, env =>
      FDist.bind
        (L.evalDist D' (VEnv.eraseSampleEnv env))
        (fun v =>
          outcomeDistPure k σ
            (VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _) v env))
  | _, .commit x who (b := b) _ k, σ, env =>
      let s := ProgramPureStrategy.headKernel (σ who)
      let v := s (projectViewEnv who (VEnv.eraseEnv env))
      outcomeDistPure k (ProgramPureProfile.tail σ)
        (VEnv.cons (Player := P) (L := L) (x := x)
          (τ := .hidden who b) v env)
  | _, .reveal y _who _x (b := b) hx k, σ, env =>
      let v : L.Val b := VEnv.get (Player := P) (L := L) env hx
      outcomeDistPure k σ
        (VEnv.cons (Player := P) (L := L) (x := y) (τ := .pub b) v env)

theorem outcomeDistPure_totalWeight_eq_one
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    {σ : ProgramPureProfile p}
    {env : VEnv (Player := P) L Γ}
    (hd : NormalizedDists p) :
    (outcomeDistPure p σ env).totalWeight = 1 := by
  induction p with
  | ret u =>
      simp [outcomeDistPure, FDist.totalWeight_pure]
  | letExpr x e k ih =>
      exact ih hd
  | sample x D' k ih =>
      simp only [outcomeDistPure]
      exact FDist.totalWeight_bind_of_normalized (hd.1 _) (fun _ _ => ih hd.2)
  | commit x who R k ih =>
      simpa [outcomeDistPure] using
        ih (σ := ProgramPureProfile.tail σ) hd
  | reveal y who x hx k ih =>
      exact ih hd

/-- Running the local behavioral lift of a fixed-program pure profile yields
the same outcome distribution as the pure strategic semantics. -/
theorem outcomeDistBehavioral_toBehavioral_eq_outcomeDistPure
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    (σ : ProgramPureProfile p)
    (env : VEnv (Player := P) L Γ) :
    outcomeDistBehavioral p (ProgramPureProfile.toBehavioral p σ) env =
      outcomeDistPure p σ env := by
  induction p with
  | ret u =>
      rfl
  | letExpr x e k ih =>
      simpa [outcomeDistBehavioral, outcomeDistPure, ProgramPureProfile.toBehavioral] using
        ih σ _
  | sample x D' k ih =>
      simp only [outcomeDistBehavioral, outcomeDistPure]
      congr
      funext v
      exact ih σ _
  | commit x who R k ih =>
      simp only [outcomeDistBehavioral, outcomeDistPure]
      have hhead :
          ProgramBehavioralStrategy.headKernel
              ((ProgramPureProfile.toBehavioral
                  (.commit x who R k) σ) who)
              (projectViewEnv who (VEnv.eraseEnv env)) =
            FDist.pure
              ((ProgramPureStrategy.headKernel (σ who))
                (projectViewEnv who (VEnv.eraseEnv env))) := by
        simp [ProgramPureProfile.toBehavioral, ProgramBehavioralStrategy.headKernel,
          ProgramBehavioralKernel.ofPure, ProgramPureStrategy.headKernel]
      rw [hhead, FDist.pure_bind]
      simpa [ProgramPureProfile.tail_toBehavioral] using
        ih (ProgramPureProfile.tail σ)
          (VEnv.cons (Player := P) (L := L) (x := x) (τ := .hidden who _)
            ((ProgramPureStrategy.headKernel (σ who))
              (projectViewEnv who (VEnv.eraseEnv env))) env)
  | reveal y who x hx k ih =>
      simpa [outcomeDistBehavioral, outcomeDistPure, ProgramPureProfile.toBehavioral] using
        ih σ _

/-- Fixed-program pure strategic form of a Vegas program.

The outcome kernel is the checked graph-machine kernel at the bundle's context
proof. -/
noncomputable def toStrategicKernelGame (g : WFProgram P L) :
    GameTheory.KernelGame P :=
  toMachineStrategicKernelGame g g.wctx

@[simp] theorem toStrategicKernelGame_outcomeKernel
    (g : WFProgram P L)
    (σ : LegalProgramPureProfile g) :
    (toStrategicKernelGame g).outcomeKernel σ =
      (graphMachine g g.wctx).outcomeKernel
        (lawOfPure σ g.wctx).val (syntaxSteps g.prog) := rfl

@[simp] theorem toStrategicKernelGame_Strategy (g : WFProgram P L) :
    (toStrategicKernelGame g).Strategy = LegalProgramPureStrategy g := rfl

/-- `toStrategicKernelGame` is the machine-native pure kernel at `g.wctx`. -/
theorem toStrategicKernelGame_eu
    (g : WFProgram P L)
    (σ : LegalProgramPureProfile g) (who : P) :
    (toStrategicKernelGame g).eu σ who =
      (toMachineStrategicKernelGame g g.wctx).eu σ who := rfl

/-- The legal behavioral lift of a legal pure profile has the same outcome
kernel as the fixed-program pure strategic form. -/
theorem toKernelGame_outcomeKernel_eq_toStrategicKernelGame_toBehavioral
    (g : WFProgram P L)
    (σ : LegalProgramPureProfile g) :
    (toKernelGame g).outcomeKernel
        (LegalProgramPureProfile.toBehavioral σ) =
      (toStrategicKernelGame g).outcomeKernel σ := by
  change (graphMachine g g.wctx).outcomeKernel
        (lawOfBehavioralPMF
          (LegalProgramBehavioralProfile.toPMFProfile
            (LegalProgramPureProfile.toBehavioral σ)) g.wctx).val
        (syntaxSteps g.prog) =
      (graphMachine g g.wctx).outcomeKernel
        (lawOfBehavioralPMF
          (LegalProgramPureProfile.toBehavioralPMF σ) g.wctx).val
        (syntaxSteps g.prog)
  congr 2
  ext cfg
  rw [show
      LegalProgramBehavioralProfile.toPMFProfile
          (LegalProgramPureProfile.toBehavioral σ) =
        LegalProgramPureProfile.toBehavioralPMF σ by
      funext who
      apply Subtype.ext
      simpa [LegalProgramBehavioralProfile.toPMFProfile,
        LegalProgramPureProfile.toBehavioral,
        LegalProgramPureProfile.toBehavioralPMF] using
        congrFun
          (ProgramBehavioralProfile.toPMFProfile_toBehavioral_eq_toBehavioralPMF
            g.prog (fun i => (σ i).val)) who]

/-- The legal behavioral lift of a legal pure profile has the same expected
utility as the fixed-program pure strategic form. -/
theorem toKernelGame_eu_eq_toStrategicKernelGame_toBehavioral
    (g : WFProgram P L)
    (σ : LegalProgramPureProfile g) (who : P) :
    (toKernelGame g).eu
        (LegalProgramPureProfile.toBehavioral σ) who =
      (toStrategicKernelGame g).eu σ who := by
  unfold GameTheory.KernelGame.eu
  rw [toKernelGame_outcomeKernel_eq_toStrategicKernelGame_toBehavioral]
  rfl

/-- Pure Nash equilibrium of the fixed-program Vegas strategic form. -/
def IsPureNash (g : WFProgram P L) (σ : LegalProgramPureProfile g) : Prop :=
  (toStrategicKernelGame g).IsNash σ

/-- Pure dominant strategy in the fixed-program Vegas strategic form. -/
def IsPureDominant (g : WFProgram P L)
    (who : P) (s : LegalProgramPureStrategy g who) : Prop :=
  (toStrategicKernelGame g).IsDominant who s

/-- Pure best response in the fixed-program Vegas strategic form. -/
def IsPureBestResponse (g : WFProgram P L)
    (who : P) (σ : LegalProgramPureProfile g)
    (s : LegalProgramPureStrategy g who) : Prop :=
  (toStrategicKernelGame g).IsBestResponse who σ s

/-- Pure strict Nash equilibrium of the fixed-program Vegas strategic form. -/
def IsPureStrictNash (g : WFProgram P L)
    (σ : LegalProgramPureProfile g) : Prop :=
  (toStrategicKernelGame g).IsStrictNash σ

/-- Exact potential for the fixed-program Vegas strategic form. -/
def IsPureExactPotential (g : WFProgram P L)
    (Φ : LegalProgramPureProfile g → ℝ) : Prop :=
  (toStrategicKernelGame g).IsExactPotential Φ

/-- Ordinal potential for the fixed-program Vegas strategic form. -/
def IsPureOrdinalPotential (g : WFProgram P L)
    (Φ : LegalProgramPureProfile g → ℝ) : Prop :=
  (toStrategicKernelGame g).IsOrdinalPotential Φ

end Vegas
