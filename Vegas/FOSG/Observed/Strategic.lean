import Vegas.FOSG.Observed.Kernel
import Vegas.Protocol.StrategicCompatibility
import Vegas.StrategicPMF

namespace Vegas
namespace FOSGBridge

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace Observed

theorem observedProgramOutcomeKernelPMF_eq_toKernelGamePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : SyntaxLegalProgramBehavioralProfilePMF g) :
    observedProgramOutcomeKernelPMF g hctx LF σ =
      (toKernelGamePMF g).outcomeKernel σ := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        g hctx LF who
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  let R := observedProgramOutcomeValuePMF g hctx σ
  have hclosure :=
    R.map_observe_runDist_eq_value
      (syntaxSteps g.prog)
      (observedProgramFOSG_initial_remainingSyntaxSteps_le g hctx)
  have hrun :
      observedProgramOutcomeKernelPMF g hctx LF σ =
        (graphMachine g hctx).outcomeKernel
          (lawOfBehavioralPMF σ hctx).val (syntaxSteps g.prog) := by
    rw [GraphEventLaw.lawOfBehavioralPMF_outcomeKernel_eq_cursorVegasOutcomeKernelPMF]
    simpa [R, observedProgramOutcomeValuePMF, observedProgramOutcomeKernelPMF]
      using hclosure
  exact hrun.trans
    (lawOfBehavioralPMF_outcomeKernel_eq_toKernelGamePMF σ hctx)

/-- Pure-strategy outcome preservation for the observed-program FOSG.

Transporting a Vegas legal pure profile to the FOSG, running its deterministic
behavioral lift, and projecting terminal histories to Vegas outcomes gives the
same outcome distribution as `toStrategicKernelGame`. -/
theorem observedProgramPureOutcomeKernel_eq_toStrategicKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramPureProfile g) :
    PMF.map (observedProgramHistoryOutcome g hctx)
        (observedProgramRunDist g hctx LF
          ((observedProgramFOSG g hctx).legalPureToBehavioral
            (toObservedProgramLegalPureProfile g hctx σ))) =
      (toStrategicKernelGame g).outcomeKernel σ := by
  rw [show
      PMF.map (observedProgramHistoryOutcome g hctx)
          (observedProgramRunDist g hctx LF
            ((observedProgramFOSG g hctx).legalPureToBehavioral
              (toObservedProgramLegalPureProfile g hctx σ))) =
        observedProgramOutcomeKernelPMF g hctx LF
          (LegalProgramPureProfile.toBehavioralPMF σ) by
        simp [observedProgramOutcomeKernelPMF,
          toObservedProgramLegalBehavioralProfilePMF_toBehavioralPMF]]
  rw [observedProgramOutcomeKernelPMF_eq_toKernelGamePMF]
  exact toKernelGamePMF_outcomeKernel_eq_toStrategicKernelGame_toBehavioralPMF
    g σ

/-- Reachable pure-profile outcome preservation for the observed-program FOSG.

The reachable-coordinate FOSG Kuhn theorem states its pure side using
`reachableHistoryOutcomeDistPureProfile`. For Vegas, that distribution is the
same terminal-history law as the native observed-program FOSG run of the
extended pure profile, hence it projects to `toStrategicKernelGame`. -/
theorem observedProgramReachablePureOutcomeKernel_eq_toStrategicKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramPureProfile g) :
    letI : ∀ who : P,
        Fintype (Option (ProgramAction g.prog who)) :=
      fun who =>
        observedProgramFOSG.instFintypeOptionAction
          g hctx LF who
    PMF.map (observedProgramHistoryOutcome g hctx)
        (GameTheory.FOSG.Kuhn.reachableHistoryOutcomeDistPureProfile
          (G := observedProgramFOSG g hctx)
          (observedProgramFOSG_legalObservable g hctx)
          (syntaxSteps g.prog)
          (toObservedProgramReachableLegalPureProfile g hctx σ)) =
      (toStrategicKernelGame g).outcomeKernel σ := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        g hctx LF who
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  rw [GameTheory.FOSG.Kuhn.reachableHistoryOutcomeDistPureProfile_eq_runDist
    (G := observedProgramFOSG g hctx)
    (observedProgramFOSG_legalObservable g hctx)]
  rw [show
      (observedProgramFOSG g hctx).runDist (syntaxSteps g.prog)
          ((observedProgramFOSG g hctx).legalPureToBehavioral
            (toObservedProgramReachableLegalPureProfile g hctx σ).extend) =
        observedProgramRunDist g hctx LF
          ((observedProgramFOSG g hctx).legalPureToBehavioral
            (toObservedProgramLegalPureProfile g hctx σ)) by
        simpa [observedProgramRunDist,
          GameTheory.FOSG.Kuhn.legalPureProfileRestrictReachable,
          toObservedProgramReachableLegalPureProfile] using
          GameTheory.FOSG.Kuhn.legalPureProfileRestrictReachable_extend_runDist
          (G := observedProgramFOSG g hctx)
          (toObservedProgramLegalPureProfile g hctx σ)
          (syntaxSteps g.prog)]
  exact observedProgramPureOutcomeKernel_eq_toStrategicKernelGame g hctx LF σ

/-- Native-FOSG run-distribution form of reachable-coordinate FOSG M→B.

This is the Vegas-facing distribution theorem: the witness is a legal
reachable FOSG behavioral profile, and the left side is the ordinary FOSG
`runDist` of its global extension. -/
theorem observedProgramReachable_mixed_to_legal_behavioral_runDist_outcomeDist
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [Fintype (CursorCheckedWorld g)]
    [∀ who : P, Fintype (Option (ProgramAction g.prog who))]
    [Fintype (observedProgramFOSG g hctx).History]
    [DecidablePred (observedProgramFOSG g hctx).terminal]
    (μ : GameTheory.FOSG.Kuhn.ReachableMixedProfile
      (G := observedProgramFOSG g hctx)) :
    ∃ β : (observedProgramFOSG g hctx).ReachableLegalBehavioralProfile,
      PMF.map (observedProgramHistoryOutcome g hctx)
          ((observedProgramFOSG g hctx).runDist
            (syntaxSteps g.prog) β.extend) =
        (GameTheory.FOSG.Kuhn.reachableMixedProfileJoint
          (G := observedProgramFOSG g hctx) μ).bind
      (fun π =>
        PMF.map (observedProgramHistoryOutcome g hctx)
          (GameTheory.FOSG.Kuhn.reachableHistoryOutcomeDistPureProfile
            (G := observedProgramFOSG g hctx)
            (observedProgramFOSG_legalObservable g hctx)
            (syntaxSteps g.prog) π)) := by
  exact
    GameTheory.FOSG.Kuhn.reachable_mixed_to_legal_behavioral_mapped_runDist
    (G := observedProgramFOSG g hctx)
    (observedProgramFOSG_legalObservable g hctx)
    μ (syntaxSteps g.prog) (observedProgramHistoryOutcome g hctx)

/-- Strategic KernelGame collapse of the observed-program FOSG, using legal
reachable behavioral strategies as the strategic choices.

This is the KernelGame view of the sequential FOSG denotation. Its outcome
kernel is the finite-horizon FOSG run distribution, pushed forward to Vegas
payoff outcomes. -/
noncomputable def observedProgramReachableKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P] : GameTheory.KernelGame P where
  Strategy := fun who =>
    (observedProgramFOSG g hctx).ReachableLegalBehavioralStrategy who
  Outcome := Outcome P
  utility := fun o who => (o who : ℝ)
  outcomeKernel := fun β => by
    letI : Fintype (CursorCheckedWorld g) :=
      observedProgramFOSG.instFintypeWorld g hctx LF
    letI : ∀ who : P, Fintype (Option (ProgramAction g.prog who)) :=
      fun who => observedProgramFOSG.instFintypeOptionAction g hctx LF who
    letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
      observedProgramFOSG.instDecidablePredTerminal g hctx
    exact PMF.map (observedProgramHistoryOutcome g hctx)
      ((observedProgramFOSG g hctx).runDist
        (syntaxSteps g.prog)
        (GameTheory.FOSG.ReachableLegalBehavioralProfile.extend
          (G := observedProgramFOSG g hctx) β))

@[simp] theorem observedProgramReachableKernelGame_outcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (β : (observedProgramFOSG g hctx).ReachableLegalBehavioralProfile) :
    letI : Fintype (CursorCheckedWorld g) :=
      observedProgramFOSG.instFintypeWorld g hctx LF
    letI : ∀ who : P, Fintype (Option (ProgramAction g.prog who)) :=
      fun who => observedProgramFOSG.instFintypeOptionAction g hctx LF who
    letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
      observedProgramFOSG.instDecidablePredTerminal g hctx
    (observedProgramReachableKernelGame g hctx LF).outcomeKernel β =
      PMF.map (observedProgramHistoryOutcome g hctx)
        ((observedProgramFOSG g hctx).runDist
          (syntaxSteps g.prog) β.extend) := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P, Fintype (Option (ProgramAction g.prog who)) :=
    fun who => observedProgramFOSG.instFintypeOptionAction g hctx LF who
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  rfl

/-- Product-mixed Vegas-pure specialization of reachable-coordinate FOSG M→B,
stated over native FOSG execution.

The witness is a legal reachable behavioral profile for the observed-program
FOSG. The preserved object is the pushforward distribution on Vegas outcomes;
expected-utility preservation is a corollary of this distribution statement. -/
theorem observedProgramReachable_vegasMixedPure_runDist_toStrategicKernelGame_finite
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    letI : Fintype (CursorCheckedWorld g) :=
      observedProgramFOSG.instFintypeWorld g hctx LF
    letI : ∀ who : P, Fintype (Option (ProgramAction g.prog who)) :=
      fun who => observedProgramFOSG.instFintypeOptionAction g hctx LF who
    letI : Fintype (observedProgramFOSG g hctx).History :=
      observedProgramFOSG.instFintypeHistory g hctx LF
    letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
      observedProgramFOSG.instDecidablePredTerminal g hctx
    ∃ β : (observedProgramFOSG g hctx).ReachableLegalBehavioralProfile,
      PMF.map (observedProgramHistoryOutcome g hctx)
          ((observedProgramFOSG g hctx).runDist
            (syntaxSteps g.prog) β.extend) =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toStrategicKernelGame g).outcomeKernel σ) := by
  letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
    fun who => LegalProgramPureStrategy.instFintype g LF who
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P, Fintype (Option (ProgramAction g.prog who)) :=
    fun who => observedProgramFOSG.instFintypeOptionAction g hctx LF who
  letI : Fintype (observedProgramFOSG g hctx).History :=
    observedProgramFOSG.instFintypeHistory g hctx LF
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  obtain ⟨β, hdist⟩ :=
    observedProgramReachable_mixed_to_legal_behavioral_runDist_outcomeDist
      g hctx (toObservedProgramReachableMixedPureProfile g hctx μ)
  refine ⟨β, ?_⟩
  rw [toObservedProgramReachableMixedPureProfile_joint] at hdist
  rw [PMF.bind_map] at hdist
  rw [hdist]
  apply congrArg
  funext σ
  exact observedProgramReachablePureOutcomeKernel_eq_toStrategicKernelGame
    g hctx LF σ

/-- Product-mixed Vegas-pure specialization of FOSG M→B with a total FOSG
behavioral witness.

The proof still uses the bounded-history reachable theorem internally, then
extends the reachable behavioral profile to a total legal FOSG behavioral
profile. This avoids any finiteness assumption on the full FOSG information
state space. -/
theorem observedProgramFullFOSG_vegasMixedPure_runDist_toStrategicKernelGame_finite
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    letI : Fintype (CursorCheckedWorld g) :=
      observedProgramFOSG.instFintypeWorld g hctx LF
    letI : ∀ who : P, Fintype (Option (ProgramAction g.prog who)) :=
      fun who => observedProgramFOSG.instFintypeOptionAction g hctx LF who
    letI : Fintype (observedProgramFOSG g hctx).History :=
      observedProgramFOSG.instFintypeHistory g hctx LF
    letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
      observedProgramFOSG.instDecidablePredTerminal g hctx
    ∃ β : (observedProgramFOSG g hctx).LegalBehavioralProfile,
      PMF.map (observedProgramHistoryOutcome g hctx)
          ((observedProgramFOSG g hctx).runDist
            (syntaxSteps g.prog) β) =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toStrategicKernelGame g).outcomeKernel σ) := by
  letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
    fun who => LegalProgramPureStrategy.instFintype g LF who
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P, Fintype (Option (ProgramAction g.prog who)) :=
    fun who => observedProgramFOSG.instFintypeOptionAction g hctx LF who
  letI : Fintype (observedProgramFOSG g hctx).History :=
    observedProgramFOSG.instFintypeHistory g hctx LF
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  obtain ⟨β, hβ⟩ :=
    observedProgramReachable_vegasMixedPure_runDist_toStrategicKernelGame_finite
      g hctx LF μ
  exact ⟨β.extend, hβ⟩

/-- KernelGame-shaped FOSG Kuhn corollary for Vegas.

A product mixed profile over legal Vegas pure strategies is realized by a legal
reachable behavioral profile in the KernelGame collapse of the observed-program
FOSG, with the same distribution over Vegas payoff outcomes. -/
theorem observedProgramReachableKernelGame_mixedPure_realization
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    ∃ β : GameTheory.KernelGame.Profile
        (observedProgramReachableKernelGame g hctx LF),
      (observedProgramReachableKernelGame g hctx LF).outcomeKernel β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toStrategicKernelGame g).outcomeKernel σ) := by
  letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
    fun who => LegalProgramPureStrategy.instFintype g LF who
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P, Fintype (Option (ProgramAction g.prog who)) :=
    fun who => observedProgramFOSG.instFintypeOptionAction g hctx LF who
  letI : Fintype (observedProgramFOSG g hctx).History :=
    observedProgramFOSG.instFintypeHistory g hctx LF
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  obtain ⟨β, hβ⟩ :=
    observedProgramReachable_vegasMixedPure_runDist_toStrategicKernelGame_finite
      g hctx LF μ
  refine ⟨β, ?_⟩
  simpa using hβ

end Observed

end FOSGBridge
end Vegas
