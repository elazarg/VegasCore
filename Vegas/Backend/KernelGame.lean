import Vegas.Backend.Refinement
import Vegas.Strategic.KernelGame

/-!
# Backend kernel-game transport

This module packages a backend machine refinement as a kernel-game morphism.
The strategic carriers are the same carriers as the canonical Vegas games; the
backend outcome keeps the full implementation event-batch trace.

The only extra datum beyond `StochasticStepRefinement` is a per-profile
history-dependent event-batch-law lift, supplied per profile. The FOSG bridge
constructs theorem-facing event-batch trace distributions, but this module does
not infer a canonical `Machine.EventBatchLaw` from an arbitrary strategic
profile. Keeping the law explicit keeps machine refinement independent of
strategic scheduling while giving backend users a precise place to supply the
runtime scheduler/transaction-lift witness.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Per-pure-profile event-batch-law lift from the canonical event-graph machine to a
backend implementation.

`specLaw_sound` is the bridge to the Stage 1 event-batch trace game: running the
spec event-batch law for the syntax horizon must reproduce the existing
`pureEventBatchTraceKernelGameAt` outcome kernel. -/
structure BackendPureEventBatchLawLift
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g)) where
  specLaw : pureProfileAt g → (eventGraphMachine g).EventBatchLaw
  backendLaw : pureProfileAt g → Impl.EventBatchLaw
  compatible :
    ∀ π, R.EventBatchLawCompatible (backendLaw π) (specLaw π)
  specLaw_sound :
    ∀ π,
      (eventGraphMachine g).eventBatchTraceDist
          (specLaw π) (syntaxSteps g.prog) =
        (pureEventBatchTraceKernelGameAt g).outcomeKernel π

/-- Per-PMF-behavioral-profile event-batch-law lift from the canonical event-graph
machine to a backend implementation. -/
structure BackendBehavioralEventBatchLawLift
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g)) where
  specLaw : behavioralProfilePMFAt g → (eventGraphMachine g).EventBatchLaw
  backendLaw : behavioralProfilePMFAt g → Impl.EventBatchLaw
  compatible :
    ∀ β, R.EventBatchLawCompatible (backendLaw β) (specLaw β)
  specLaw_sound :
    ∀ β,
      (eventGraphMachine g).eventBatchTraceDist
          (specLaw β) (syntaxSteps g.prog) =
        (pmfBehavioralEventBatchTraceKernelGameAt g).outcomeKernel β

/-- A specification-side pure event-batch law, packaged independently of any
backend.  This is the missing bridge between a strategic profile and the
machine-level `EventBatchLaw` interface. -/
structure PureSpecEventBatchLaw
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] where
  specLaw : pureProfileAt g → (eventGraphMachine g).EventBatchLaw
  specLaw_sound :
    ∀ π,
      (eventGraphMachine g).eventBatchTraceDist
          (specLaw π) (syntaxSteps g.prog) =
        (pureEventBatchTraceKernelGameAt g).outcomeKernel π

/-- A specification-side PMF-behavioral event-batch law, packaged independently of
any backend. -/
structure BehavioralSpecEventBatchLaw
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] where
  specLaw : behavioralProfilePMFAt g → (eventGraphMachine g).EventBatchLaw
  specLaw_sound :
    ∀ β,
      (eventGraphMachine g).eventBatchTraceDist
          (specLaw β) (syntaxSteps g.prog) =
        (pmfBehavioralEventBatchTraceKernelGameAt g).outcomeKernel β

namespace PureSpecEventBatchLaw

/-- The identity backend lift induced by a proved pure spec event-batch law. -/
noncomputable def identityBackendLift
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (law : PureSpecEventBatchLaw g) :
    BackendPureEventBatchLawLift g
      (Machine.StochasticStepRefinement.refl (eventGraphMachine g)) where
  specLaw := law.specLaw
  backendLaw := law.specLaw
  compatible := by
    intro π
    exact Machine.StochasticStepRefinement.refl_eventBatchLawCompatible
      (eventGraphMachine g) (law.specLaw π)
  specLaw_sound := law.specLaw_sound

end PureSpecEventBatchLaw

namespace BehavioralSpecEventBatchLaw

/-- The identity backend lift induced by a proved PMF-behavioral spec event batch
law. -/
noncomputable def identityBackendLift
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (law : BehavioralSpecEventBatchLaw g) :
    BackendBehavioralEventBatchLawLift g
      (Machine.StochasticStepRefinement.refl (eventGraphMachine g)) where
  specLaw := law.specLaw
  backendLaw := law.specLaw
  compatible := by
    intro β
    exact Machine.StochasticStepRefinement.refl_eventBatchLawCompatible
      (eventGraphMachine g) (law.specLaw β)
  specLaw_sound := law.specLaw_sound

end BehavioralSpecEventBatchLaw

/-- Backend event-batch trace utility, read by projecting the backend terminal
state back to the canonical event-graph machine state. -/
noncomputable def backendEventBatchTraceUtility
    (g : WFProgram P L) {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g)) :
    Impl.EventBatchTrace → GameTheory.Payoff P :=
  fun trace => syntaxEventBatchTraceUtility g (R.projectEventBatchTrace trace)

/-- Backend event-batch trace kernel game for a backend/refinement/law-lift triple.

Strategies are the canonical pure Vegas strategies. Outcomes are full backend
event-batch traces, so downstream backend-specific statements can still inspect
implementation events. -/
noncomputable def backendEventBatchTraceKernelGameAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g))
    (lift : BackendPureEventBatchLawLift g R) :
    GameTheory.KernelGame P where
  Strategy := pureStrategyAt g
  Outcome := Impl.EventBatchTrace
  utility := backendEventBatchTraceUtility g R
  outcomeKernel := fun π =>
    Impl.eventBatchTraceDist (lift.backendLaw π) (syntaxSteps g.prog)

/-- Backend event-batch trace kernel game for PMF behavioral profiles. -/
noncomputable def backendPMFBehavioralEventBatchTraceKernelGameAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g))
    (lift : BackendBehavioralEventBatchLawLift g R) :
    GameTheory.KernelGame P where
  Strategy := behavioralStrategyPMFAt g
  Outcome := Impl.EventBatchTrace
  utility := backendEventBatchTraceUtility g R
  outcomeKernel := fun β =>
    Impl.eventBatchTraceDist (lift.backendLaw β) (syntaxSteps g.prog)

@[simp] theorem backendEventBatchTraceKernelGameAt_Strategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g))
    (lift : BackendPureEventBatchLawLift g R) :
    (backendEventBatchTraceKernelGameAt g R lift).Strategy = pureStrategyAt g :=
  rfl

@[simp] theorem backendPMFBehavioralEventBatchTraceKernelGameAt_Strategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g))
    (lift : BackendBehavioralEventBatchLawLift g R) :
    (backendPMFBehavioralEventBatchTraceKernelGameAt g R lift).Strategy =
      behavioralStrategyPMFAt g :=
  rfl

/-- Projecting the backend event-batch trace outcome kernel gives the canonical
spec event-batch trace outcome kernel. -/
theorem backendEventBatchTraceKernelGameAt_outcomeKernel_map_project
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g))
    (lift : BackendPureEventBatchLawLift g R)
    (π : pureProfileAt g) :
    PMF.map R.projectEventBatchTrace
        ((backendEventBatchTraceKernelGameAt g R lift).outcomeKernel π) =
      (pureEventBatchTraceKernelGameAt g).outcomeKernel π := by
  have h :=
    R.eventBatchTraceDist_project_eq
      (lift.specLaw π) (lift.backendLaw π) (lift.compatible π)
      (syntaxSteps g.prog) ([], Impl.init)
  have h' :
      PMF.map R.projectEventBatchTrace
          (Impl.eventBatchTraceDistFrom (lift.backendLaw π)
            (syntaxSteps g.prog) ([], Impl.init)) =
        (eventGraphMachine g).eventBatchTraceDist
          (lift.specLaw π) (syntaxSteps g.prog) := by
    simpa [Machine.eventBatchTraceDist,
      Machine.StochasticStepRefinement.projectEventBatchTrace, R.init_project]
      using h
  change
    PMF.map R.projectEventBatchTrace
        (Impl.eventBatchTraceDistFrom (lift.backendLaw π)
          (syntaxSteps g.prog) ([], Impl.init)) =
      (pureEventBatchTraceKernelGameAt g).outcomeKernel π
  exact h'.trans (lift.specLaw_sound π)

/-- Projecting the backend PMF-behavioral event-batch trace outcome kernel gives
the canonical spec PMF-behavioral event-batch trace outcome kernel. -/
theorem backendPMFBehavioralEventBatchTraceKernelGameAt_outcomeKernel_map_project
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g))
    (lift : BackendBehavioralEventBatchLawLift g R)
    (β : behavioralProfilePMFAt g) :
    PMF.map R.projectEventBatchTrace
        ((backendPMFBehavioralEventBatchTraceKernelGameAt g R lift).outcomeKernel β) =
      (pmfBehavioralEventBatchTraceKernelGameAt g).outcomeKernel β := by
  have h :=
    R.eventBatchTraceDist_project_eq
      (lift.specLaw β) (lift.backendLaw β) (lift.compatible β)
      (syntaxSteps g.prog) ([], Impl.init)
  have h' :
      PMF.map R.projectEventBatchTrace
          (Impl.eventBatchTraceDistFrom (lift.backendLaw β)
            (syntaxSteps g.prog) ([], Impl.init)) =
        (eventGraphMachine g).eventBatchTraceDist
          (lift.specLaw β) (syntaxSteps g.prog) := by
    simpa [Machine.eventBatchTraceDist,
      Machine.StochasticStepRefinement.projectEventBatchTrace, R.init_project]
      using h
  change
    PMF.map R.projectEventBatchTrace
        (Impl.eventBatchTraceDistFrom (lift.backendLaw β)
          (syntaxSteps g.prog) ([], Impl.init)) =
      (pmfBehavioralEventBatchTraceKernelGameAt g).outcomeKernel β
  exact h'.trans (lift.specLaw_sound β)

/-- Projecting backend event-batch traces to syntax states agrees with projecting
canonical syntax event-batch traces to their checkpoint state. -/
theorem backendProjectedStateDist_eq
    (g : WFProgram P L)
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g))
    {backendDist : PMF Impl.EventBatchTrace}
    {specDist : PMF (eventGraphMachine g).EventBatchTrace}
    (hproject : PMF.map R.projectEventBatchTrace backendDist = specDist) :
    PMF.map (fun trace : Impl.EventBatchTrace => R.projectState trace.2)
        backendDist =
      PMF.map (fun trace : (eventGraphMachine g).EventBatchTrace => trace.2)
        specDist := by
  have h :=
    congrArg (fun μ =>
      PMF.map
        (fun trace : (eventGraphMachine g).EventBatchTrace => trace.2) μ)
      hproject
  change
    PMF.map (fun trace : (eventGraphMachine g).EventBatchTrace => trace.2)
        (PMF.map R.projectEventBatchTrace backendDist) =
      PMF.map (fun trace : (eventGraphMachine g).EventBatchTrace => trace.2)
        specDist at h
  rw [PMF.map_comp] at h
  simpa [Machine.StochasticStepRefinement.projectEventBatchTrace, Function.comp_def]
    using h

/-- Backend event-batch trace play and canonical spec event-batch trace play have the
same expected utility for every pure profile. -/
theorem backendEventBatchTraceKernelGameAt_eu_eq
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g))
    (lift : BackendPureEventBatchLawLift g R)
    (π : pureProfileAt g) (who : P) :
    (backendEventBatchTraceKernelGameAt g R lift).eu π who =
      (pureEventBatchTraceKernelGameAt g).eu π who := by
  classical
  let backendDist :=
    (backendEventBatchTraceKernelGameAt g R lift).outcomeKernel π
  let specDist :=
    (pureEventBatchTraceKernelGameAt g).outcomeKernel π
  let backendState : Impl.EventBatchTrace → (eventGraphMachine g).State :=
    fun trace => R.projectState trace.2
  let specState : (eventGraphMachine g).EventBatchTrace →
      (eventGraphMachine g).State :=
    fun trace => trace.2
  let stateUtility : (eventGraphMachine g).State → ℝ :=
    fun state => syntaxEventBatchTraceUtility g ([], state) who
  have hproject :
      PMF.map R.projectEventBatchTrace backendDist = specDist := by
    simpa [backendDist, specDist] using
      backendEventBatchTraceKernelGameAt_outcomeKernel_map_project
        g R lift π
  have hstate :
      PMF.map backendState backendDist = PMF.map specState specDist := by
    simpa [backendState, specState, backendDist, specDist,
      Machine.StochasticStepRefinement.projectEventBatchTrace]
      using backendProjectedStateDist_eq g R hproject
  calc
    (backendEventBatchTraceKernelGameAt g R lift).eu π who =
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
    _ = (pureEventBatchTraceKernelGameAt g).eu π who := by
          simp [GameTheory.KernelGame.eu, pureEventBatchTraceKernelGameAt,
            syntaxEventBatchTraceUtility, syntaxEventBatchTraceOutcome,
            stateUtility, specState, specDist]

/-- Backend PMF-behavioral event-batch trace play and canonical spec
PMF-behavioral event-batch trace play have the same expected utility. -/
theorem backendPMFBehavioralEventBatchTraceKernelGameAt_eu_eq
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g))
    (lift : BackendBehavioralEventBatchLawLift g R)
    (β : behavioralProfilePMFAt g) (who : P) :
    (backendPMFBehavioralEventBatchTraceKernelGameAt g R lift).eu β who =
      (pmfBehavioralEventBatchTraceKernelGameAt g).eu β who := by
  classical
  let backendDist :=
    (backendPMFBehavioralEventBatchTraceKernelGameAt g R lift).outcomeKernel β
  let specDist :=
    (pmfBehavioralEventBatchTraceKernelGameAt g).outcomeKernel β
  let backendState : Impl.EventBatchTrace → (eventGraphMachine g).State :=
    fun trace => R.projectState trace.2
  let specState : (eventGraphMachine g).EventBatchTrace →
      (eventGraphMachine g).State :=
    fun trace => trace.2
  let stateUtility : (eventGraphMachine g).State → ℝ :=
    fun state => syntaxEventBatchTraceUtility g ([], state) who
  have hproject :
      PMF.map R.projectEventBatchTrace backendDist = specDist := by
    simpa [backendDist, specDist] using
      backendPMFBehavioralEventBatchTraceKernelGameAt_outcomeKernel_map_project
        g R lift β
  have hstate :
      PMF.map backendState backendDist = PMF.map specState specDist := by
    simpa [backendState, specState, backendDist, specDist,
      Machine.StochasticStepRefinement.projectEventBatchTrace]
      using backendProjectedStateDist_eq g R hproject
  calc
    (backendPMFBehavioralEventBatchTraceKernelGameAt g R lift).eu β who =
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
    _ = (pmfBehavioralEventBatchTraceKernelGameAt g).eu β who := by
          simp [GameTheory.KernelGame.eu,
            pmfBehavioralEventBatchTraceKernelGameAt,
            syntaxEventBatchTraceUtility, syntaxEventBatchTraceOutcome,
            stateUtility, specState, specDist]

/-- The backend event-batch trace game maps to the canonical spec event-batch trace
game by projecting backend traces to spec traces. This is the direction needed
to pull Nash equilibria back from the spec to the backend. -/
noncomputable def Machine.StochasticStepRefinement.toBackendEventBatchTraceMorphism
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g))
    (lift : BackendPureEventBatchLawLift g R) :
    GameTheory.KernelGame.EUMorphism
      (backendEventBatchTraceKernelGameAt g R lift)
      (pureEventBatchTraceKernelGameAt g) where
  toMorphism :=
    GameTheory.KernelGame.Morphism.ofOutcomeEmbedding
      (fun _ strategy => strategy)
      R.projectEventBatchTrace
      (fun π =>
        (backendEventBatchTraceKernelGameAt_outcomeKernel_map_project
          g R lift π).symm)
      (fun _ => by
        funext who
        rfl)
  eu_preserved := by
    intro π who
    exact (backendEventBatchTraceKernelGameAt_eu_eq g R lift π who).symm

/-- PMF-behavioral backend event-batch trace game maps to the canonical
PMF-behavioral spec event-batch trace game by projecting backend traces. -/
noncomputable def Machine.StochasticStepRefinement.toBackendPMFBehavioralEventBatchTraceMorphism
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g))
    (lift : BackendBehavioralEventBatchLawLift g R) :
    GameTheory.KernelGame.EUMorphism
      (backendPMFBehavioralEventBatchTraceKernelGameAt g R lift)
      (pmfBehavioralEventBatchTraceKernelGameAt g) where
  toMorphism :=
    GameTheory.KernelGame.Morphism.ofOutcomeEmbedding
      (fun _ strategy => strategy)
      R.projectEventBatchTrace
      (fun β =>
        (backendPMFBehavioralEventBatchTraceKernelGameAt_outcomeKernel_map_project
          g R lift β).symm)
      (fun _ => by
        funext who
        rfl)
  eu_preserved := by
    intro β who
    exact
      (backendPMFBehavioralEventBatchTraceKernelGameAt_eu_eq
        g R lift β who).symm

/-- Nash equilibria of the canonical spec event-batch trace game pull back to any
backend equipped with a compatible event-batch-law lift. -/
theorem backendEventBatchTraceKernelGameAt_isNash_pullback
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g))
    (lift : BackendPureEventBatchLawLift g R)
    {σ : pureProfileAt g}
    (h : (pureEventBatchTraceKernelGameAt g).IsNash σ) :
    (backendEventBatchTraceKernelGameAt g R lift).IsNash σ := by
  exact
    GameTheory.KernelGame.EUMorphism.nash_of_nash
      (G := backendEventBatchTraceKernelGameAt g R lift)
      (H := pureEventBatchTraceKernelGameAt g)
      (R.toBackendEventBatchTraceMorphism g lift)
      (σ := σ) h

/-- Composed Stage 1 + backend transport: Nash equilibria of the public pure
kernel game pull back to the backend event-batch trace game. -/
theorem backendEventBatchTraceKernelGameAt_isNash_pullback_pure
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g))
    (lift : BackendPureEventBatchLawLift g R)
    {σ : pureProfileAt g}
    (h : (pureKernelGameAt g).IsNash σ) :
    (backendEventBatchTraceKernelGameAt g R lift).IsNash σ := by
  have hEventBatch : (pureEventBatchTraceKernelGameAt g).IsNash σ := by
    simpa using
      ((pureKernelGameAt.eventBatchTraceEUBisimulation g).nash_iff σ).mp h
  exact backendEventBatchTraceKernelGameAt_isNash_pullback g R lift
    hEventBatch

/-- Nash equilibria of the canonical PMF-behavioral spec event-batch trace game
pull back to any backend equipped with a compatible behavioral event-batch-law lift. -/
theorem backendPMFBehavioralEventBatchTraceKernelGameAt_isNash_pullback
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g))
    (lift : BackendBehavioralEventBatchLawLift g R)
    {σ : behavioralProfilePMFAt g}
    (h : (pmfBehavioralEventBatchTraceKernelGameAt g).IsNash σ) :
    (backendPMFBehavioralEventBatchTraceKernelGameAt g R lift).IsNash σ := by
  exact
    GameTheory.KernelGame.EUMorphism.nash_of_nash
      (G := backendPMFBehavioralEventBatchTraceKernelGameAt g R lift)
      (H := pmfBehavioralEventBatchTraceKernelGameAt g)
      (R.toBackendPMFBehavioralEventBatchTraceMorphism g lift)
      (σ := σ) h

/-- Composed Stage 1 + backend transport: Nash equilibria of the public
PMF-behavioral kernel game pull back to the backend PMF-behavioral
event-batch trace game. -/
theorem backendPMFBehavioralEventBatchTraceKernelGameAt_isNash_pullback_behavioral
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g))
    (lift : BackendBehavioralEventBatchLawLift g R)
    {σ : behavioralProfilePMFAt g}
    (h : (pmfBehavioralKernelGameAt g).IsNash σ) :
    (backendPMFBehavioralEventBatchTraceKernelGameAt g R lift).IsNash σ := by
  have hEventBatch : (pmfBehavioralEventBatchTraceKernelGameAt g).IsNash σ := by
    simpa using
      ((pmfBehavioralKernelGameAt.eventBatchTraceEUBisimulation g).nash_iff σ).mp h
  exact backendPMFBehavioralEventBatchTraceKernelGameAt_isNash_pullback g R lift
    hEventBatch

end Vegas
