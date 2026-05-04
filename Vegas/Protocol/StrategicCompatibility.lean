import Vegas.Protocol.Strategic
import Vegas.StrategicPMF

/-!
# Compatibility between machine-native and legacy strategic kernels

The primary strategic kernel definitions live in `Vegas.Protocol.Strategic`.
This module contains the temporary comparison theorems against the
syntax-recursive legacy kernels. Keeping these lemmas here prevents the
low-level event-law and machine-strategic modules from importing the legacy
strategic API.
-/

namespace Vegas

open GameTheory
open FOSGBridge

namespace GraphEventLaw

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {g : WFProgram P L}

/-- PMF behavioral profiles have the same outcome kernel through the
graph-machine event law as through the legacy syntax PMF kernel. -/
theorem lawOfBehavioralPMF_outcomeKernel_eq_toKernelGamePMF
    (σ : SyntaxLegalProgramBehavioralProfilePMF g)
    (hctx : WFCtx g.Γ) :
    (graphMachine g hctx).outcomeKernel
        (lawOfBehavioralPMF σ hctx).val (syntaxSteps g.prog) =
      (toKernelGamePMF g).outcomeKernel σ := by
  rw [lawOfBehavioralPMF_outcomeKernel_eq_cursorVegasOutcomeKernelPMF]
  simp [Observed.cursorVegasOutcomeKernelPMF,
    CursorCheckedWorld.initial, CursorWorldData.prog,
    CursorWorldData.suffix, ProgramCursor.toSuffix,
    ProgramCursor.toSuffixFrom, ProgramSuffix.behavioralProfilePMF,
    ProgramCursor.prog]
  rfl

/-- FDist-valued legal behavioral profiles have the same outcome kernel
through the graph-machine event law as through the legacy behavioral kernel. -/
theorem lawOfBehavioral_outcomeKernel_eq_toKernelGame
    (σ : LegalProgramBehavioralProfile g)
    (hctx : WFCtx g.Γ) :
    (graphMachine g hctx).outcomeKernel
        (lawOfBehavioral σ hctx).val (syntaxSteps g.prog) =
      (toKernelGame g).outcomeKernel σ := by
  rw [lawOfBehavioral]
  rw [lawOfBehavioralPMF_outcomeKernel_eq_toKernelGamePMF]
  exact toKernelGamePMF_outcomeKernel_toPMFProfile_eq_toKernelGame g σ

/-- Pure profiles have the same outcome kernel through the graph-machine event
law as through the legacy pure strategic kernel. -/
theorem lawOfPure_outcomeKernel_eq_toStrategicKernelGame
    (σ : LegalProgramPureProfile g)
    (hctx : WFCtx g.Γ) :
    (graphMachine g hctx).outcomeKernel
        (lawOfPure σ hctx).val (syntaxSteps g.prog) =
      (toStrategicKernelGame g).outcomeKernel σ := by
  rw [lawOfPure]
  rw [lawOfBehavioralPMF_outcomeKernel_eq_toKernelGamePMF]
  exact toKernelGamePMF_outcomeKernel_eq_toStrategicKernelGame_toBehavioralPMF
    g σ

/-- Direct pure-strategy bridge, stated in terms of the legacy
`outcomeDistPure` expression. -/
theorem outcomeDistPure_eq_machine_outcomeKernel
    (σ : LegalProgramPureProfile g)
    (hctx : WFCtx g.Γ) :
    (outcomeDistPure g.prog (fun i => (σ i).val) g.env).toPMF
        (outcomeDistPure_totalWeight_eq_one
          (p := g.prog) (σ := fun i => (σ i).val)
          g.normalized) =
      (graphMachine g hctx).outcomeKernel
        (lawOfPure σ hctx).val (syntaxSteps g.prog) := by
  rw [← toStrategicKernelGame_outcomeKernel (g := g) σ]
  exact (lawOfPure_outcomeKernel_eq_toStrategicKernelGame
    (g := g) σ hctx).symm

/-- The machine-native pure kernel agrees with the legacy pure kernel. -/
theorem toMachineStrategicKernelGame_outcomeKernel_eq_toStrategicKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g) :
    (toMachineStrategicKernelGame g hctx).outcomeKernel σ =
      (toStrategicKernelGame g).outcomeKernel σ :=
  lawOfPure_outcomeKernel_eq_toStrategicKernelGame σ hctx

/-- Expected utilities are unchanged by replacing the legacy pure kernel with
the machine-native pure kernel. -/
theorem toMachineStrategicKernelGame_eu_eq_toStrategicKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g) (who : P) :
    (toMachineStrategicKernelGame g hctx).eu σ who =
      (toStrategicKernelGame g).eu σ who := by
  unfold GameTheory.KernelGame.eu
  rw [toMachineStrategicKernelGame_outcomeKernel_eq_toStrategicKernelGame]
  simp [toMachineStrategicKernelGame, toStrategicKernelGame]

/-- Utility distributions are unchanged by replacing the legacy pure kernel
with the machine-native pure kernel. -/
theorem toMachineStrategicKernelGame_udist_eq_toStrategicKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g) :
    (toMachineStrategicKernelGame g hctx).udist σ =
      (toStrategicKernelGame g).udist σ := by
  unfold GameTheory.KernelGame.udist
  rw [toMachineStrategicKernelGame_outcomeKernel_eq_toStrategicKernelGame]
  simp [toMachineStrategicKernelGame, toStrategicKernelGame]

/-- Binding a distribution over pure profiles through the machine-native pure
kernel gives the same outcome distribution as binding through the legacy pure
kernel. -/
theorem bind_toMachineStrategicKernelGame_outcomeKernel_eq_toStrategicKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (μ : PMF (LegalProgramPureProfile g)) :
    μ.bind (fun σ => (toMachineStrategicKernelGame g hctx).outcomeKernel σ) =
      μ.bind (fun σ => (toStrategicKernelGame g).outcomeKernel σ) := by
  refine Math.ProbabilityMassFunction.bind_congr_on_support μ _ _ ?_
  intro σ _
  exact toMachineStrategicKernelGame_outcomeKernel_eq_toStrategicKernelGame
    g hctx σ

/-- The machine-native PMF behavioral kernel agrees with the legacy PMF
behavioral kernel. -/
theorem toMachineKernelGamePMF_outcomeKernel_eq_toKernelGamePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : SyntaxLegalProgramBehavioralProfilePMF g) :
    (toMachineKernelGamePMF g hctx).outcomeKernel σ =
      (toKernelGamePMF g).outcomeKernel σ :=
  lawOfBehavioralPMF_outcomeKernel_eq_toKernelGamePMF σ hctx

/-- Expected utilities are unchanged by replacing the legacy PMF behavioral
kernel with the machine-native PMF behavioral kernel. -/
theorem toMachineKernelGamePMF_eu_eq_toKernelGamePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : SyntaxLegalProgramBehavioralProfilePMF g) (who : P) :
    (toMachineKernelGamePMF g hctx).eu σ who =
      (toKernelGamePMF g).eu σ who := by
  unfold GameTheory.KernelGame.eu
  rw [toMachineKernelGamePMF_outcomeKernel_eq_toKernelGamePMF]
  simp [toMachineKernelGamePMF, toKernelGamePMF]

/-- Utility distributions are unchanged by replacing the legacy PMF behavioral
kernel with the machine-native PMF behavioral kernel. -/
theorem toMachineKernelGamePMF_udist_eq_toKernelGamePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : SyntaxLegalProgramBehavioralProfilePMF g) :
    (toMachineKernelGamePMF g hctx).udist σ =
      (toKernelGamePMF g).udist σ := by
  unfold GameTheory.KernelGame.udist
  rw [toMachineKernelGamePMF_outcomeKernel_eq_toKernelGamePMF]
  simp [toMachineKernelGamePMF, toKernelGamePMF]

/-- Binding a distribution over PMF behavioral profiles through the
machine-native PMF behavioral kernel gives the same outcome distribution as
binding through the legacy PMF behavioral kernel. -/
theorem bind_toMachineKernelGamePMF_outcomeKernel_eq_toKernelGamePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (μ : PMF (SyntaxLegalProgramBehavioralProfilePMF g)) :
    μ.bind (fun σ => (toMachineKernelGamePMF g hctx).outcomeKernel σ) =
      μ.bind (fun σ => (toKernelGamePMF g).outcomeKernel σ) := by
  refine Math.ProbabilityMassFunction.bind_congr_on_support μ _ _ ?_
  intro σ _
  exact toMachineKernelGamePMF_outcomeKernel_eq_toKernelGamePMF g hctx σ

/-- The machine-native FDist behavioral kernel agrees with the legacy FDist
behavioral kernel. -/
theorem toMachineKernelGame_outcomeKernel_eq_toKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) :
    (toMachineKernelGame g hctx).outcomeKernel σ =
      (toKernelGame g).outcomeKernel σ :=
  lawOfBehavioral_outcomeKernel_eq_toKernelGame σ hctx

/-- Expected utilities are unchanged by replacing the legacy FDist behavioral
kernel with the machine-native FDist behavioral kernel. -/
theorem toMachineKernelGame_eu_eq_toKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) (who : P) :
    (toMachineKernelGame g hctx).eu σ who =
      (toKernelGame g).eu σ who := by
  unfold GameTheory.KernelGame.eu
  rw [toMachineKernelGame_outcomeKernel_eq_toKernelGame]
  simp [toMachineKernelGame, toKernelGame]

/-- Utility distributions are unchanged by replacing the legacy FDist
behavioral kernel with the machine-native FDist behavioral kernel. -/
theorem toMachineKernelGame_udist_eq_toKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) :
    (toMachineKernelGame g hctx).udist σ =
      (toKernelGame g).udist σ := by
  unfold GameTheory.KernelGame.udist
  rw [toMachineKernelGame_outcomeKernel_eq_toKernelGame]
  simp [toMachineKernelGame, toKernelGame]

/-- Binding a distribution over FDist behavioral profiles through the
machine-native FDist behavioral kernel gives the same outcome distribution as
binding through the legacy FDist behavioral kernel. -/
theorem bind_toMachineKernelGame_outcomeKernel_eq_toKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (μ : PMF (LegalProgramBehavioralProfile g)) :
    μ.bind (fun σ => (toMachineKernelGame g hctx).outcomeKernel σ) =
      μ.bind (fun σ => (toKernelGame g).outcomeKernel σ) := by
  refine Math.ProbabilityMassFunction.bind_congr_on_support μ _ _ ?_
  intro σ _
  exact toMachineKernelGame_outcomeKernel_eq_toKernelGame g hctx σ

end GraphEventLaw

export GraphEventLaw
  (lawOfBehavioralPMF_outcomeKernel_eq_toKernelGamePMF
   lawOfBehavioral_outcomeKernel_eq_toKernelGame
   lawOfPure_outcomeKernel_eq_toStrategicKernelGame
   outcomeDistPure_eq_machine_outcomeKernel
   toMachineStrategicKernelGame_outcomeKernel_eq_toStrategicKernelGame
   toMachineStrategicKernelGame_eu_eq_toStrategicKernelGame
   toMachineStrategicKernelGame_udist_eq_toStrategicKernelGame
   bind_toMachineStrategicKernelGame_outcomeKernel_eq_toStrategicKernelGame
   toMachineKernelGamePMF_outcomeKernel_eq_toKernelGamePMF
   toMachineKernelGamePMF_eu_eq_toKernelGamePMF
   toMachineKernelGamePMF_udist_eq_toKernelGamePMF
   bind_toMachineKernelGamePMF_outcomeKernel_eq_toKernelGamePMF
   toMachineKernelGame_outcomeKernel_eq_toKernelGame
   toMachineKernelGame_eu_eq_toKernelGame
   toMachineKernelGame_udist_eq_toKernelGame
   bind_toMachineKernelGame_outcomeKernel_eq_toKernelGame)

end Vegas
