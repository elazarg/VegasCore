import Vegas.FOSG.Observed.Kernel
import Vegas.FOSG.Observed.Current

namespace Vegas
namespace FOSGBridge

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-!
# FOSG denotation for checked Vegas programs

This file is the public entrypoint for the FOSG integration. The internal
`Observed` modules contain the cursor machinery and proof infrastructure; the
definitions below expose the intended denotational surface.
-/

/-- Canonical sequential denotation of a checked Vegas program as a FOSG. -/
noncomputable abbrev toFOSG
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :=
  observedProgramFOSG g hctx

theorem toFOSG_legalObservable
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    (toFOSG g hctx).LegalObservable :=
  Observed.observedProgramFOSG_legalObservable g hctx

theorem toFOSG_boundedHorizon
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    (toFOSG g hctx).BoundedHorizon (syntaxSteps g.prog) :=
  observedProgramFOSG_boundedHorizon g hctx

/-- Strategic KernelGame view of the canonical FOSG denotation. -/
noncomputable abbrev toFOSGKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P] : KernelGame P :=
  Observed.observedProgramReachableKernelGame g hctx LF

@[simp] theorem toFOSGKernelGame_outcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (β : (toFOSG g hctx).ReachableLegalBehavioralProfile) :
    letI : Fintype (CursorCheckedWorld g) :=
      observedProgramFOSG.instFintypeWorld g hctx LF
    letI : ∀ who : P, Fintype (Option (ProgramAction g.prog who)) :=
      fun who => observedProgramFOSG.instFintypeOptionAction g hctx LF who
    letI : DecidablePred (toFOSG g hctx).terminal :=
      observedProgramFOSG.instDecidablePredTerminal g hctx
    (toFOSGKernelGame g hctx LF).outcomeKernel β =
      PMF.map (observedProgramHistoryOutcome g hctx)
        ((toFOSG g hctx).runDist (syntaxSteps g.prog) β.extend) := by
  exact Observed.observedProgramReachableKernelGame_outcomeKernel
    g hctx LF β

/-- FOSG Kuhn M→B, specialized to product-mixed Vegas pure strategies and
stated as preservation of the Vegas outcome distribution. -/
theorem toFOSG_mixedPure_realizedByBehavioral_outcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    ∃ β : KernelGame.Profile (toFOSGKernelGame g hctx LF),
      (toFOSGKernelGame g hctx LF).outcomeKernel β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toStrategicKernelGame g).outcomeKernel σ) :=
  Observed.observedProgramReachableKernelGame_mixedPure_realization
    g hctx LF μ

/-- FOSG Kuhn M→B with a total legal FOSG behavioral witness.

The theorem preserves the Vegas outcome distribution. The behavioral witness is
total for the compiled FOSG information-state space; this is stronger than the
reachable-profile wrapper below, but it is still a FOSG strategy, not a Vegas
`LegalProgramBehavioralProfilePMF`. -/
theorem toFOSG_mixedPure_realizedByFullBehavioral_runDist
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    letI : Fintype (CursorCheckedWorld g) :=
      observedProgramFOSG.instFintypeWorld g hctx LF
    letI : ∀ who : P, Fintype (Option (ProgramAction g.prog who)) :=
      fun who => observedProgramFOSG.instFintypeOptionAction g hctx LF who
    letI : Fintype (toFOSG g hctx).History :=
      observedProgramFOSG.instFintypeHistory g hctx LF
    letI : DecidablePred (toFOSG g hctx).terminal :=
      observedProgramFOSG.instDecidablePredTerminal g hctx
    ∃ β : (toFOSG g hctx).LegalBehavioralProfile,
      PMF.map (observedProgramHistoryOutcome g hctx)
          ((toFOSG g hctx).runDist (syntaxSteps g.prog) β) =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toStrategicKernelGame g).outcomeKernel σ) :=
  Observed.observedProgramFullFOSG_vegasMixedPure_runDist_toStrategicKernelGame_finite
    g hctx LF μ

end FOSGBridge

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A Vegas behavioral profile defined only on reachable program observations.

This is the partial strategy space: unlike `LegalProgramBehavioralProfilePMF`,
it does not assign behavior to syntactically well-typed views that cannot occur
as player observations in the sequential execution. -/
structure ReachableProgramBehavioralProfilePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ) where
  profile : (FOSGBridge.toFOSG g hctx).ReachableLegalBehavioralProfile

/-- Outcome kernel for a reachable Vegas behavioral profile. -/
noncomputable def reachableProgramOutcomeKernelPMF
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (β : ReachableProgramBehavioralProfilePMF g hctx) : PMF (Outcome P) :=
  (FOSGBridge.toFOSGKernelGame g hctx LF).outcomeKernel β.profile

/-- Finite-game Kuhn theorem in the reachable Vegas strategy space. -/
theorem reachableProgram_mixedPure_realizedByBehavioralPMF_finite
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    ∃ β : ReachableProgramBehavioralProfilePMF g hctx,
      reachableProgramOutcomeKernelPMF g hctx LF β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toStrategicKernelGame g).outcomeKernel σ) := by
  letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
    fun who => LegalProgramPureStrategy.instFintype g LF who
  obtain ⟨βF, hβF⟩ :=
    FOSGBridge.toFOSG_mixedPure_realizedByBehavioral_outcomeKernel
      g hctx LF μ
  exact ⟨⟨βF⟩, hβF⟩

/-- Finite-game Kuhn theorem in the total Vegas behavioral strategy space. -/
theorem program_mixedPure_realizedByBehavioralPMF_finite
    [Fintype P] [∀ τ : L.Ty, Nonempty (L.Val τ)]
    (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    ∃ β : LegalProgramBehavioralProfilePMF g,
      (toKernelGamePMF g).outcomeKernel β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toStrategicKernelGame g).outcomeKernel σ) := by
  exact FOSGBridge.Observed.currentObsModel_mixedPure_realizedByBehavioralPMF_finite
    g hctx LF μ

end Vegas
