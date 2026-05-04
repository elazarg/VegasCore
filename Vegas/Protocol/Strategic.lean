import Vegas.Protocol.EventLaw

/-!
# Machine-native strategic kernel games

This module gives the syntax-facing Vegas strategy spaces a machine-native
`KernelGame` presentation. The strategy carriers are the existing legal
strategy types, while outcome kernels run through the checked graph machine and
the event-law adapters from `Vegas.Protocol.EventLaw`.
-/

namespace Vegas

open GameTheory
open FOSGBridge

namespace GraphEventLaw

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Pure strategic form whose outcome kernel is the checked graph machine. -/
noncomputable def toMachineStrategicKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ) : GameTheory.KernelGame P where
  Strategy := LegalProgramPureStrategy g
  Outcome := Outcome P
  utility := fun o i => (o i : ℝ)
  outcomeKernel := fun σ =>
    (graphMachine g hctx).outcomeKernel
      (lawOfPure σ hctx).val (syntaxSteps g.prog)

@[simp] theorem toMachineStrategicKernelGame_outcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g) :
    (toMachineStrategicKernelGame g hctx).outcomeKernel σ =
      (graphMachine g hctx).outcomeKernel
        (lawOfPure σ hctx).val (syntaxSteps g.prog) := rfl

@[simp] theorem toMachineStrategicKernelGame_Strategy
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    (toMachineStrategicKernelGame g hctx).Strategy =
      LegalProgramPureStrategy g := rfl

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

/-- PMF behavioral strategic form whose outcome kernel is the checked graph
machine. -/
noncomputable def toMachineKernelGamePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ) : GameTheory.KernelGame P where
  Strategy := SyntaxLegalProgramBehavioralStrategyPMF g
  Outcome := Outcome P
  utility := fun o i => (o i : ℝ)
  outcomeKernel := fun σ =>
    (graphMachine g hctx).outcomeKernel
      (lawOfBehavioralPMF σ hctx).val (syntaxSteps g.prog)

@[simp] theorem toMachineKernelGamePMF_outcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : SyntaxLegalProgramBehavioralProfilePMF g) :
    (toMachineKernelGamePMF g hctx).outcomeKernel σ =
      (graphMachine g hctx).outcomeKernel
        (lawOfBehavioralPMF σ hctx).val (syntaxSteps g.prog) := rfl

@[simp] theorem toMachineKernelGamePMF_Strategy
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    (toMachineKernelGamePMF g hctx).Strategy =
      SyntaxLegalProgramBehavioralStrategyPMF g := rfl

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

/-- FDist behavioral strategic form whose outcome kernel is the checked graph
machine. -/
noncomputable def toMachineKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ) : GameTheory.KernelGame P where
  Strategy := LegalProgramBehavioralStrategy g
  Outcome := Outcome P
  utility := fun o i => (o i : ℝ)
  outcomeKernel := fun σ =>
    (graphMachine g hctx).outcomeKernel
      (lawOfBehavioral σ hctx).val (syntaxSteps g.prog)

@[simp] theorem toMachineKernelGame_outcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) :
    (toMachineKernelGame g hctx).outcomeKernel σ =
      (graphMachine g hctx).outcomeKernel
        (lawOfBehavioral σ hctx).val (syntaxSteps g.prog) := rfl

@[simp] theorem toMachineKernelGame_Strategy
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    (toMachineKernelGame g hctx).Strategy =
      LegalProgramBehavioralStrategy g := rfl

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
  (toMachineStrategicKernelGame toMachineKernelGamePMF toMachineKernelGame
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
