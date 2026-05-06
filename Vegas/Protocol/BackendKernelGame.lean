import Vegas.Protocol.Backend
import Vegas.Protocol.Strategic

/-!
# Backend kernel-game transport

This module packages a backend machine refinement as a kernel-game morphism.
The strategic carriers are the same carriers as the canonical Vegas games; the
backend outcome keeps the full implementation blocked trace.

The only extra datum beyond `StochasticStepRefinement` is a per-profile
history-dependent block-law lift, supplied per profile. This keeps machine
refinement independent of strategic scheduling while giving backend users a
precise place to supply the runtime scheduler/transaction-lift witness.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Per-pure-profile block-law lift from the canonical syntax machine to a
backend implementation.

`specLaw_sound` is the bridge to the Stage 1 blocked-trace game: running the
spec block law for the syntax horizon must reproduce the existing
`pureBlockedTraceKernelGameAt` outcome kernel. -/
structure BackendPureBlockLawLift
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (syntaxGraphMachine g)) where
  specLaw : pureProfileAt g → (syntaxGraphMachine g).BlockLaw
  backendLaw : pureProfileAt g → Impl.BlockLaw
  compatible :
    ∀ π, R.BlockLawCompatible (backendLaw π) (specLaw π)
  specLaw_sound :
    ∀ π,
      (syntaxGraphMachine g).blockTraceDist
          (specLaw π) (syntaxSteps g.prog) =
        (pureBlockedTraceKernelGameAt g).outcomeKernel π

/-- Per-PMF-behavioral-profile block-law lift from the canonical syntax
machine to a backend implementation. -/
structure BackendBehavioralBlockLawLift
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (syntaxGraphMachine g)) where
  specLaw : behavioralProfilePMFAt g → (syntaxGraphMachine g).BlockLaw
  backendLaw : behavioralProfilePMFAt g → Impl.BlockLaw
  compatible :
    ∀ β, R.BlockLawCompatible (backendLaw β) (specLaw β)
  specLaw_sound :
    ∀ β,
      (syntaxGraphMachine g).blockTraceDist
          (specLaw β) (syntaxSteps g.prog) =
        (pmfBehavioralBlockedTraceKernelGameAt g).outcomeKernel β

/-- Backend blocked trace utility, read by projecting the backend terminal
state back to the canonical syntax machine state. -/
noncomputable def backendBlockedTraceUtility
    (g : WFProgram P L) {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (syntaxGraphMachine g)) :
    Impl.BlockTrace → GameTheory.Payoff P :=
  fun trace => syntaxBlockedTraceUtility g (R.projectBlockTrace trace)

/-- Backend block-trace kernel game for a backend/refinement/law-lift triple.

Strategies are the canonical pure Vegas strategies. Outcomes are full backend
blocked traces, so downstream backend-specific statements can still inspect
implementation events. -/
noncomputable def backendBlockedTraceKernelGameAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (syntaxGraphMachine g))
    (lift : BackendPureBlockLawLift g R) :
    GameTheory.KernelGame P where
  Strategy := pureStrategyAt g
  Outcome := Impl.BlockTrace
  utility := backendBlockedTraceUtility g R
  outcomeKernel := fun π =>
    Impl.blockTraceDist (lift.backendLaw π) (syntaxSteps g.prog)

/-- Backend blocked-trace kernel game for PMF behavioral profiles. -/
noncomputable def backendPMFBehavioralBlockedTraceKernelGameAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (syntaxGraphMachine g))
    (lift : BackendBehavioralBlockLawLift g R) :
    GameTheory.KernelGame P where
  Strategy := behavioralStrategyPMFAt g
  Outcome := Impl.BlockTrace
  utility := backendBlockedTraceUtility g R
  outcomeKernel := fun β =>
    Impl.blockTraceDist (lift.backendLaw β) (syntaxSteps g.prog)

@[simp] theorem backendBlockedTraceKernelGameAt_Strategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (syntaxGraphMachine g))
    (lift : BackendPureBlockLawLift g R) :
    (backendBlockedTraceKernelGameAt g R lift).Strategy = pureStrategyAt g :=
  rfl

@[simp] theorem backendPMFBehavioralBlockedTraceKernelGameAt_Strategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (syntaxGraphMachine g))
    (lift : BackendBehavioralBlockLawLift g R) :
    (backendPMFBehavioralBlockedTraceKernelGameAt g R lift).Strategy =
      behavioralStrategyPMFAt g :=
  rfl

/-- Projecting the backend blocked-trace outcome kernel gives the canonical
spec blocked-trace outcome kernel. -/
theorem backendBlockedTraceKernelGameAt_outcomeKernel_map_project
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (syntaxGraphMachine g))
    (lift : BackendPureBlockLawLift g R)
    (π : pureProfileAt g) :
    PMF.map R.projectBlockTrace
        ((backendBlockedTraceKernelGameAt g R lift).outcomeKernel π) =
      (pureBlockedTraceKernelGameAt g).outcomeKernel π := by
  have h :=
    R.blockTraceDist_project_eq
      (lift.specLaw π) (lift.backendLaw π) (lift.compatible π)
      (syntaxSteps g.prog) ([], Impl.init)
  have h' :
      PMF.map R.projectBlockTrace
          (Impl.blockTraceDistFrom (lift.backendLaw π)
            (syntaxSteps g.prog) ([], Impl.init)) =
        (syntaxGraphMachine g).blockTraceDist
          (lift.specLaw π) (syntaxSteps g.prog) := by
    simpa [Machine.blockTraceDist,
      Machine.StochasticStepRefinement.projectBlockTrace, R.init_project]
      using h
  change
    PMF.map R.projectBlockTrace
        (Impl.blockTraceDistFrom (lift.backendLaw π)
          (syntaxSteps g.prog) ([], Impl.init)) =
      (pureBlockedTraceKernelGameAt g).outcomeKernel π
  exact h'.trans (lift.specLaw_sound π)

/-- Projecting the backend PMF-behavioral blocked-trace outcome kernel gives
the canonical spec PMF-behavioral blocked-trace outcome kernel. -/
theorem backendPMFBehavioralBlockedTraceKernelGameAt_outcomeKernel_map_project
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (syntaxGraphMachine g))
    (lift : BackendBehavioralBlockLawLift g R)
    (β : behavioralProfilePMFAt g) :
    PMF.map R.projectBlockTrace
        ((backendPMFBehavioralBlockedTraceKernelGameAt g R lift).outcomeKernel β) =
      (pmfBehavioralBlockedTraceKernelGameAt g).outcomeKernel β := by
  have h :=
    R.blockTraceDist_project_eq
      (lift.specLaw β) (lift.backendLaw β) (lift.compatible β)
      (syntaxSteps g.prog) ([], Impl.init)
  have h' :
      PMF.map R.projectBlockTrace
          (Impl.blockTraceDistFrom (lift.backendLaw β)
            (syntaxSteps g.prog) ([], Impl.init)) =
        (syntaxGraphMachine g).blockTraceDist
          (lift.specLaw β) (syntaxSteps g.prog) := by
    simpa [Machine.blockTraceDist,
      Machine.StochasticStepRefinement.projectBlockTrace, R.init_project]
      using h
  change
    PMF.map R.projectBlockTrace
        (Impl.blockTraceDistFrom (lift.backendLaw β)
          (syntaxSteps g.prog) ([], Impl.init)) =
      (pmfBehavioralBlockedTraceKernelGameAt g).outcomeKernel β
  exact h'.trans (lift.specLaw_sound β)

/-- Backend blocked-trace play and canonical spec blocked-trace play have the
same expected utility for every pure profile. -/
theorem backendBlockedTraceKernelGameAt_eu_eq
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (syntaxGraphMachine g))
    (lift : BackendPureBlockLawLift g R)
    (π : pureProfileAt g) (who : P) :
    (backendBlockedTraceKernelGameAt g R lift).eu π who =
      (pureBlockedTraceKernelGameAt g).eu π who := by
  classical
  let backendDist :=
    (backendBlockedTraceKernelGameAt g R lift).outcomeKernel π
  let specDist :=
    (pureBlockedTraceKernelGameAt g).outcomeKernel π
  let backendState : Impl.BlockTrace → (syntaxGraphMachine g).State :=
    fun trace => R.projectState trace.2
  let specState : (syntaxGraphMachine g).BlockTrace →
      (syntaxGraphMachine g).State :=
    fun trace => trace.2
  let stateUtility : (syntaxGraphMachine g).State → ℝ :=
    fun state => syntaxBlockedTraceUtility g ([], state) who
  have hproject :
      PMF.map R.projectBlockTrace backendDist = specDist := by
    simpa [backendDist, specDist] using
      backendBlockedTraceKernelGameAt_outcomeKernel_map_project
        g R lift π
  have hstate :
      PMF.map backendState backendDist = PMF.map specState specDist := by
    have h :=
      congrArg (fun μ =>
        PMF.map
          (fun trace : (syntaxGraphMachine g).BlockTrace => trace.2) μ)
        hproject
    change
      PMF.map (fun trace : (syntaxGraphMachine g).BlockTrace => trace.2)
          (PMF.map R.projectBlockTrace backendDist) =
        PMF.map (fun trace : (syntaxGraphMachine g).BlockTrace => trace.2)
          specDist at h
    rw [PMF.map_comp] at h
    simpa [backendState, specState, backendDist, specDist,
      Machine.StochasticStepRefinement.projectBlockTrace, Function.comp_def]
      using h
  calc
    (backendBlockedTraceKernelGameAt g R lift).eu π who =
        Math.Probability.expect backendDist
          (fun trace => stateUtility (backendState trace)) := by
          rfl
    _ =
        Math.Probability.expect (PMF.map backendState backendDist)
          stateUtility := by
          exact (Math.Probability.expect_map_fintype_target
            backendDist backendState stateUtility).symm
    _ =
        Math.Probability.expect (PMF.map specState specDist)
          stateUtility := by
          rw [hstate]
    _ =
        Math.Probability.expect specDist
          (fun trace => stateUtility (specState trace)) := by
          exact Math.Probability.expect_map_fintype_target
            specDist specState stateUtility
    _ = (pureBlockedTraceKernelGameAt g).eu π who := by
          simp [GameTheory.KernelGame.eu, pureBlockedTraceKernelGameAt,
            syntaxBlockedTraceUtility, syntaxBlockedTraceOutcome,
            stateUtility, specState, specDist]

/-- Backend PMF-behavioral blocked-trace play and canonical spec
PMF-behavioral blocked-trace play have the same expected utility. -/
theorem backendPMFBehavioralBlockedTraceKernelGameAt_eu_eq
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (syntaxGraphMachine g))
    (lift : BackendBehavioralBlockLawLift g R)
    (β : behavioralProfilePMFAt g) (who : P) :
    (backendPMFBehavioralBlockedTraceKernelGameAt g R lift).eu β who =
      (pmfBehavioralBlockedTraceKernelGameAt g).eu β who := by
  classical
  let backendDist :=
    (backendPMFBehavioralBlockedTraceKernelGameAt g R lift).outcomeKernel β
  let specDist :=
    (pmfBehavioralBlockedTraceKernelGameAt g).outcomeKernel β
  let backendState : Impl.BlockTrace → (syntaxGraphMachine g).State :=
    fun trace => R.projectState trace.2
  let specState : (syntaxGraphMachine g).BlockTrace →
      (syntaxGraphMachine g).State :=
    fun trace => trace.2
  let stateUtility : (syntaxGraphMachine g).State → ℝ :=
    fun state => syntaxBlockedTraceUtility g ([], state) who
  have hproject :
      PMF.map R.projectBlockTrace backendDist = specDist := by
    simpa [backendDist, specDist] using
      backendPMFBehavioralBlockedTraceKernelGameAt_outcomeKernel_map_project
        g R lift β
  have hstate :
      PMF.map backendState backendDist = PMF.map specState specDist := by
    have h :=
      congrArg (fun μ =>
        PMF.map
          (fun trace : (syntaxGraphMachine g).BlockTrace => trace.2) μ)
        hproject
    change
      PMF.map (fun trace : (syntaxGraphMachine g).BlockTrace => trace.2)
          (PMF.map R.projectBlockTrace backendDist) =
        PMF.map (fun trace : (syntaxGraphMachine g).BlockTrace => trace.2)
          specDist at h
    rw [PMF.map_comp] at h
    simpa [backendState, specState, backendDist, specDist,
      Machine.StochasticStepRefinement.projectBlockTrace, Function.comp_def]
      using h
  calc
    (backendPMFBehavioralBlockedTraceKernelGameAt g R lift).eu β who =
        Math.Probability.expect backendDist
          (fun trace => stateUtility (backendState trace)) := by
          rfl
    _ =
        Math.Probability.expect (PMF.map backendState backendDist)
          stateUtility := by
          exact (Math.Probability.expect_map_fintype_target
            backendDist backendState stateUtility).symm
    _ =
        Math.Probability.expect (PMF.map specState specDist)
          stateUtility := by
          rw [hstate]
    _ =
        Math.Probability.expect specDist
          (fun trace => stateUtility (specState trace)) := by
          exact Math.Probability.expect_map_fintype_target
            specDist specState stateUtility
    _ = (pmfBehavioralBlockedTraceKernelGameAt g).eu β who := by
          simp [GameTheory.KernelGame.eu,
            pmfBehavioralBlockedTraceKernelGameAt,
            syntaxBlockedTraceUtility, syntaxBlockedTraceOutcome,
            stateUtility, specState, specDist]

/-- The backend blocked-trace game maps to the canonical spec blocked-trace
game by projecting backend traces to spec traces. This is the direction needed
to pull Nash equilibria back from the spec to the backend. -/
noncomputable def Machine.StochasticStepRefinement.toBackendBlockedTraceMorphism
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (syntaxGraphMachine g))
    (lift : BackendPureBlockLawLift g R) :
    GameTheory.KernelGame.EUMorphism
      (backendBlockedTraceKernelGameAt g R lift)
      (pureBlockedTraceKernelGameAt g) where
  toMorphism :=
    GameTheory.KernelGame.Morphism.ofOutcomeEmbedding
      (fun _ strategy => strategy)
      R.projectBlockTrace
      (fun π =>
        (backendBlockedTraceKernelGameAt_outcomeKernel_map_project
          g R lift π).symm)
      (fun _ => by
        funext who
        rfl)
  eu_preserved := by
    intro π who
    exact (backendBlockedTraceKernelGameAt_eu_eq g R lift π who).symm

/-- PMF-behavioral backend blocked-trace game maps to the canonical
PMF-behavioral spec blocked-trace game by projecting backend traces. -/
noncomputable def Machine.StochasticStepRefinement.toBackendPMFBehavioralBlockedTraceMorphism
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (syntaxGraphMachine g))
    (lift : BackendBehavioralBlockLawLift g R) :
    GameTheory.KernelGame.EUMorphism
      (backendPMFBehavioralBlockedTraceKernelGameAt g R lift)
      (pmfBehavioralBlockedTraceKernelGameAt g) where
  toMorphism :=
    GameTheory.KernelGame.Morphism.ofOutcomeEmbedding
      (fun _ strategy => strategy)
      R.projectBlockTrace
      (fun β =>
        (backendPMFBehavioralBlockedTraceKernelGameAt_outcomeKernel_map_project
          g R lift β).symm)
      (fun _ => by
        funext who
        rfl)
  eu_preserved := by
    intro β who
    exact
      (backendPMFBehavioralBlockedTraceKernelGameAt_eu_eq
        g R lift β who).symm

/-- Nash equilibria of the canonical spec blocked-trace game pull back to any
backend equipped with a compatible block-law lift. -/
theorem backendBlockedTraceKernelGameAt_isNash_pullback
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (syntaxGraphMachine g))
    (lift : BackendPureBlockLawLift g R)
    {σ : pureProfileAt g}
    (h : (pureBlockedTraceKernelGameAt g).IsNash σ) :
    (backendBlockedTraceKernelGameAt g R lift).IsNash σ := by
  exact
    GameTheory.KernelGame.EUMorphism.nash_of_nash
      (G := backendBlockedTraceKernelGameAt g R lift)
      (H := pureBlockedTraceKernelGameAt g)
      (R.toBackendBlockedTraceMorphism g lift)
      (σ := σ) h

/-- Composed Stage 1 + backend transport: Nash equilibria of the public pure
kernel game pull back to the backend blocked-trace game. -/
theorem backendBlockedTraceKernelGameAt_isNash_pullback_pure
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (syntaxGraphMachine g))
    (lift : BackendPureBlockLawLift g R)
    {σ : pureProfileAt g}
    (h : (pureKernelGameAt g).IsNash σ) :
    (backendBlockedTraceKernelGameAt g R lift).IsNash σ := by
  have hblocked : (pureBlockedTraceKernelGameAt g).IsNash σ := by
    simpa using
      ((pureKernelGameAt.blockedTraceEUBisimulation g).nash_iff σ).mp h
  exact backendBlockedTraceKernelGameAt_isNash_pullback g R lift
    hblocked

/-- Nash equilibria of the canonical PMF-behavioral spec blocked-trace game
pull back to any backend equipped with a compatible behavioral block-law lift. -/
theorem backendPMFBehavioralBlockedTraceKernelGameAt_isNash_pullback
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (syntaxGraphMachine g))
    (lift : BackendBehavioralBlockLawLift g R)
    {σ : behavioralProfilePMFAt g}
    (h : (pmfBehavioralBlockedTraceKernelGameAt g).IsNash σ) :
    (backendPMFBehavioralBlockedTraceKernelGameAt g R lift).IsNash σ := by
  exact
    GameTheory.KernelGame.EUMorphism.nash_of_nash
      (G := backendPMFBehavioralBlockedTraceKernelGameAt g R lift)
      (H := pmfBehavioralBlockedTraceKernelGameAt g)
      (R.toBackendPMFBehavioralBlockedTraceMorphism g lift)
      (σ := σ) h

/-- Composed Stage 1 + backend transport: Nash equilibria of the public
PMF-behavioral kernel game pull back to the backend PMF-behavioral
blocked-trace game. -/
theorem backendPMFBehavioralBlockedTraceKernelGameAt_isNash_pullback_behavioral
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (syntaxGraphMachine g))
    (lift : BackendBehavioralBlockLawLift g R)
    {σ : behavioralProfilePMFAt g}
    (h : (pmfBehavioralKernelGameAt g).IsNash σ) :
    (backendPMFBehavioralBlockedTraceKernelGameAt g R lift).IsNash σ := by
  have hblocked : (pmfBehavioralBlockedTraceKernelGameAt g).IsNash σ := by
    simpa using
      ((pmfBehavioralKernelGameAt.blockedTraceEUBisimulation g).nash_iff σ).mp h
  exact backendPMFBehavioralBlockedTraceKernelGameAt_isNash_pullback g R lift
    hblocked

end Vegas
