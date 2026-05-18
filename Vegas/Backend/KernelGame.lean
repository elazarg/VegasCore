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

`specLaw_sound` says that running the specification event-batch law for the
syntax horizon induces the public pure outcome kernel after forgetting runtime
events. -/
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
      PMF.map
          (fun trace : (eventGraphMachine g).EventBatchTrace =>
            (eventGraphMachine g).outcome trace.2)
          ((eventGraphMachine g).eventBatchTraceDist
            (specLaw π) (syntaxSteps g.prog)) =
        pureOutcomeKernelAt g π

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
      PMF.map
          (fun trace : (eventGraphMachine g).EventBatchTrace =>
            (eventGraphMachine g).outcome trace.2)
          ((eventGraphMachine g).eventBatchTraceDist
            (specLaw β) (syntaxSteps g.prog)) =
        behavioralOutcomeKernelPMFAt g β

/-- A specification-side pure event-batch law, packaged independently of any
backend.  This is the missing bridge between a strategic profile and the
machine-level `EventBatchLaw` interface. -/
structure PureSpecEventBatchLaw
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] where
  specLaw : pureProfileAt g → (eventGraphMachine g).EventBatchLaw
  specLaw_sound :
    ∀ π,
      PMF.map
          (fun trace : (eventGraphMachine g).EventBatchTrace =>
            (eventGraphMachine g).outcome trace.2)
          ((eventGraphMachine g).eventBatchTraceDist
            (specLaw π) (syntaxSteps g.prog)) =
        pureOutcomeKernelAt g π

/-- A specification-side PMF-behavioral event-batch law, packaged independently of
any backend. -/
structure BehavioralSpecEventBatchLaw
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] where
  specLaw : behavioralProfilePMFAt g → (eventGraphMachine g).EventBatchLaw
  specLaw_sound :
    ∀ β,
      PMF.map
          (fun trace : (eventGraphMachine g).EventBatchTrace =>
            (eventGraphMachine g).outcome trace.2)
          ((eventGraphMachine g).eventBatchTraceDist
            (specLaw β) (syntaxSteps g.prog)) =
        behavioralOutcomeKernelPMFAt g β

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
  fun trace =>
    publicOutcomeUtility
      ((eventGraphMachine g).outcome (R.projectState trace.2))

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

/-- Projecting backend event-batch traces to public outcomes gives the pure
specification outcome kernel. -/
theorem backendEventBatchTraceKernelGameAt_outcomeKernel_map_outcome
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g))
    (lift : BackendPureEventBatchLawLift g R)
    (π : pureProfileAt g) :
    PMF.map
        (fun trace : Impl.EventBatchTrace =>
          (eventGraphMachine g).outcome (R.projectState trace.2))
        ((backendEventBatchTraceKernelGameAt g R lift).outcomeKernel π) =
      (pureKernelGameAt g).outcomeKernel π := by
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
  have hout :
      PMF.map
          (fun trace : Impl.EventBatchTrace =>
            (eventGraphMachine g).outcome (R.projectState trace.2))
          (Impl.eventBatchTraceDistFrom (lift.backendLaw π)
            (syntaxSteps g.prog) ([], Impl.init)) =
        PMF.map
          (fun trace : (eventGraphMachine g).EventBatchTrace =>
            (eventGraphMachine g).outcome trace.2)
          ((eventGraphMachine g).eventBatchTraceDist
            (lift.specLaw π) (syntaxSteps g.prog)) := by
    simpa [PMF.map_comp, Function.comp_def,
      Machine.StochasticStepRefinement.projectEventBatchTrace] using
      congrArg
        (fun μ =>
          PMF.map
            (fun trace : (eventGraphMachine g).EventBatchTrace =>
              (eventGraphMachine g).outcome trace.2) μ)
        h'
  change
    PMF.map
        (fun trace : Impl.EventBatchTrace =>
          (eventGraphMachine g).outcome (R.projectState trace.2))
        (Impl.eventBatchTraceDistFrom (lift.backendLaw π)
          (syntaxSteps g.prog) ([], Impl.init)) =
      (pureKernelGameAt g).outcomeKernel π
  rw [pureKernelGameAt_outcomeKernel]
  exact hout.trans (lift.specLaw_sound π)

/-- Projecting backend PMF-behavioral event-batch traces to public outcomes gives
the behavioral specification outcome kernel. -/
theorem backendPMFBehavioralEventBatchTraceKernelGameAt_outcomeKernel_map_outcome
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g))
    (lift : BackendBehavioralEventBatchLawLift g R)
    (β : behavioralProfilePMFAt g) :
    PMF.map
        (fun trace : Impl.EventBatchTrace =>
          (eventGraphMachine g).outcome (R.projectState trace.2))
        ((backendPMFBehavioralEventBatchTraceKernelGameAt g R lift).outcomeKernel β) =
      (pmfBehavioralKernelGameAt g).outcomeKernel β := by
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
  have hout :
      PMF.map
          (fun trace : Impl.EventBatchTrace =>
            (eventGraphMachine g).outcome (R.projectState trace.2))
          (Impl.eventBatchTraceDistFrom (lift.backendLaw β)
            (syntaxSteps g.prog) ([], Impl.init)) =
        PMF.map
          (fun trace : (eventGraphMachine g).EventBatchTrace =>
            (eventGraphMachine g).outcome trace.2)
          ((eventGraphMachine g).eventBatchTraceDist
            (lift.specLaw β) (syntaxSteps g.prog)) := by
    simpa [PMF.map_comp, Function.comp_def,
      Machine.StochasticStepRefinement.projectEventBatchTrace] using
      congrArg
        (fun μ =>
          PMF.map
            (fun trace : (eventGraphMachine g).EventBatchTrace =>
              (eventGraphMachine g).outcome trace.2) μ)
        h'
  change
    PMF.map
        (fun trace : Impl.EventBatchTrace =>
          (eventGraphMachine g).outcome (R.projectState trace.2))
        (Impl.eventBatchTraceDistFrom (lift.backendLaw β)
          (syntaxSteps g.prog) ([], Impl.init)) =
      (pmfBehavioralKernelGameAt g).outcomeKernel β
  rw [pmfBehavioralKernelGameAt_outcomeKernel]
  exact hout.trans (lift.specLaw_sound β)

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

/-- Backend event-batch trace play and public specification play have the same
expected utility for every pure profile. -/
theorem backendEventBatchTraceKernelGameAt_eu_eq
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g))
    (lift : BackendPureEventBatchLawLift g R)
    (π : pureProfileAt g) (who : P) :
    (backendEventBatchTraceKernelGameAt g R lift).eu π who =
      (pureKernelGameAt g).eu π who := by
  classical
  let backendDist : PMF Impl.EventBatchTrace :=
    (backendEventBatchTraceKernelGameAt g R lift).outcomeKernel π
  let specDist : PMF (eventGraphMachine g).EventBatchTrace :=
    (eventGraphMachine g).eventBatchTraceDist
      (lift.specLaw π) (syntaxSteps g.prog)
  let projectState : Impl.EventBatchTrace → (eventGraphMachine g).State :=
    fun trace => R.projectState trace.2
  let specStateDist : PMF (eventGraphMachine g).State :=
    PMF.map (fun trace : (eventGraphMachine g).EventBatchTrace => trace.2)
      specDist
  let stateUtility : (eventGraphMachine g).State → ℝ :=
    fun state =>
      publicOutcomeUtility ((eventGraphMachine g).outcome state) who
  have hprojectTrace :
      PMF.map R.projectEventBatchTrace backendDist = specDist := by
    have h :=
      R.eventBatchTraceDist_project_eq
        (lift.specLaw π) (lift.backendLaw π) (lift.compatible π)
        (syntaxSteps g.prog) ([], Impl.init)
    simpa [backendDist, specDist, Machine.eventBatchTraceDist,
      Machine.StochasticStepRefinement.projectEventBatchTrace,
      R.init_project] using h
  have hstate :
      PMF.map projectState backendDist = specStateDist := by
    simpa [projectState, specStateDist] using
      backendProjectedStateDist_eq g R hprojectTrace
  have hfull :
      PMF.map
          (fun state : (eventGraphMachine g).State =>
            (eventGraphMachine g).outcome state)
          specStateDist =
        (pureKernelGameAt g).outcomeKernel π := by
    have hsound := lift.specLaw_sound π
    rw [pureKernelGameAt_outcomeKernel]
    simpa [specStateDist, specDist, PMF.map_comp, Function.comp_def]
      using hsound
  calc
    (backendEventBatchTraceKernelGameAt g R lift).eu π who =
        Math.Probability.expect backendDist
          (fun trace => stateUtility (projectState trace)) := by
          rfl
    _ =
        Math.Probability.expect (PMF.map projectState backendDist)
          stateUtility := by
          exact (Math.Probability.expect_map_fintype_target
            backendDist projectState stateUtility).symm
    _ =
        Math.Probability.expect specStateDist stateUtility := by
          rw [hstate]
    _ =
        ∑ state : (eventGraphMachine g).State,
          (specStateDist state).toReal * stateUtility state := by
          rw [Math.Probability.expect_eq_sum]
    _ =
        Math.Probability.expect
          (PMF.map
            (fun state : (eventGraphMachine g).State =>
              (eventGraphMachine g).outcome state)
            specStateDist)
          (fun outcome => publicOutcomeUtility outcome who) := by
          rw [Math.Probability.expect_map_fintype_source]
    _ =
        Math.Probability.expect ((pureKernelGameAt g).outcomeKernel π)
          (fun outcome => publicOutcomeUtility outcome who) := by
          rw [hfull]
          rfl
    _ = (pureKernelGameAt g).eu π who := rfl

/-- Backend PMF-behavioral event-batch trace play and public specification play
have the same expected utility. -/
theorem backendPMFBehavioralEventBatchTraceKernelGameAt_eu_eq
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g))
    (lift : BackendBehavioralEventBatchLawLift g R)
    (β : behavioralProfilePMFAt g) (who : P) :
    (backendPMFBehavioralEventBatchTraceKernelGameAt g R lift).eu β who =
      (pmfBehavioralKernelGameAt g).eu β who := by
  classical
  let backendDist : PMF Impl.EventBatchTrace :=
    (backendPMFBehavioralEventBatchTraceKernelGameAt g R lift).outcomeKernel β
  let specDist : PMF (eventGraphMachine g).EventBatchTrace :=
    (eventGraphMachine g).eventBatchTraceDist
      (lift.specLaw β) (syntaxSteps g.prog)
  let projectState : Impl.EventBatchTrace → (eventGraphMachine g).State :=
    fun trace => R.projectState trace.2
  let specStateDist : PMF (eventGraphMachine g).State :=
    PMF.map (fun trace : (eventGraphMachine g).EventBatchTrace => trace.2)
      specDist
  let stateUtility : (eventGraphMachine g).State → ℝ :=
    fun state =>
      publicOutcomeUtility ((eventGraphMachine g).outcome state) who
  have hprojectTrace :
      PMF.map R.projectEventBatchTrace backendDist = specDist := by
    have h :=
      R.eventBatchTraceDist_project_eq
        (lift.specLaw β) (lift.backendLaw β) (lift.compatible β)
        (syntaxSteps g.prog) ([], Impl.init)
    simpa [backendDist, specDist, Machine.eventBatchTraceDist,
      Machine.StochasticStepRefinement.projectEventBatchTrace,
      R.init_project] using h
  have hstate :
      PMF.map projectState backendDist = specStateDist := by
    simpa [projectState, specStateDist] using
      backendProjectedStateDist_eq g R hprojectTrace
  have hfull :
      PMF.map
          (fun state : (eventGraphMachine g).State =>
            (eventGraphMachine g).outcome state)
          specStateDist =
        (pmfBehavioralKernelGameAt g).outcomeKernel β := by
    have hsound := lift.specLaw_sound β
    rw [pmfBehavioralKernelGameAt_outcomeKernel]
    simpa [specStateDist, specDist, PMF.map_comp, Function.comp_def]
      using hsound
  calc
    (backendPMFBehavioralEventBatchTraceKernelGameAt g R lift).eu β who =
        Math.Probability.expect backendDist
          (fun trace => stateUtility (projectState trace)) := by
          rfl
    _ =
        Math.Probability.expect (PMF.map projectState backendDist)
          stateUtility := by
          exact (Math.Probability.expect_map_fintype_target
            backendDist projectState stateUtility).symm
    _ =
        Math.Probability.expect specStateDist stateUtility := by
          rw [hstate]
    _ =
        ∑ state : (eventGraphMachine g).State,
          (specStateDist state).toReal * stateUtility state := by
          rw [Math.Probability.expect_eq_sum]
    _ =
        Math.Probability.expect
          (PMF.map
            (fun state : (eventGraphMachine g).State =>
              (eventGraphMachine g).outcome state)
            specStateDist)
          (fun outcome => publicOutcomeUtility outcome who) := by
          rw [Math.Probability.expect_map_fintype_source]
    _ =
        Math.Probability.expect ((pmfBehavioralKernelGameAt g).outcomeKernel β)
          (fun outcome => publicOutcomeUtility outcome who) := by
          rw [hfull]
          rfl
    _ = (pmfBehavioralKernelGameAt g).eu β who := rfl

/-- The backend event-batch trace game maps to the public pure specification
game by projecting backend traces to public payoff outcomes. This is the
direction needed to pull Nash equilibria back from the spec to the backend. -/
noncomputable def Machine.StochasticStepRefinement.toBackendEventBatchTraceMorphism
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g))
    (lift : BackendPureEventBatchLawLift g R) :
    GameTheory.KernelGame.EUMorphism
      (backendEventBatchTraceKernelGameAt g R lift)
      (pureKernelGameAt g) where
  toMorphism :=
    GameTheory.KernelGame.Morphism.ofOutcomeEmbedding
      (fun _ strategy => strategy)
      (fun trace : Impl.EventBatchTrace =>
        (eventGraphMachine g).outcome (R.projectState trace.2))
      (fun π =>
        (backendEventBatchTraceKernelGameAt_outcomeKernel_map_outcome
          g R lift π).symm)
      (fun trace => by
        funext who
        rfl)
  eu_preserved := by
    intro π who
    exact (backendEventBatchTraceKernelGameAt_eu_eq g R lift π who).symm

/-- PMF-behavioral backend event-batch trace game maps to the public
PMF-behavioral specification game by projecting backend traces to public payoff
outcomes. -/
noncomputable def Machine.StochasticStepRefinement.toBackendPMFBehavioralEventBatchTraceMorphism
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g))
    (lift : BackendBehavioralEventBatchLawLift g R) :
    GameTheory.KernelGame.EUMorphism
      (backendPMFBehavioralEventBatchTraceKernelGameAt g R lift)
      (pmfBehavioralKernelGameAt g) where
  toMorphism :=
    GameTheory.KernelGame.Morphism.ofOutcomeEmbedding
      (fun _ strategy => strategy)
      (fun trace : Impl.EventBatchTrace =>
        (eventGraphMachine g).outcome (R.projectState trace.2))
      (fun β =>
        (backendPMFBehavioralEventBatchTraceKernelGameAt_outcomeKernel_map_outcome
          g R lift β).symm)
      (fun trace => by
        funext who
        rfl)
  eu_preserved := by
    intro β who
    exact
      (backendPMFBehavioralEventBatchTraceKernelGameAt_eu_eq
        g R lift β who).symm

/-- Nash equilibria of the public pure specification game pull back to any
backend equipped with a compatible event-batch-law lift. -/
theorem backendEventBatchTraceKernelGameAt_isNash_pullback
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g))
    (lift : BackendPureEventBatchLawLift g R)
    {σ : pureProfileAt g}
    (h : (pureKernelGameAt g).IsNash σ) :
    (backendEventBatchTraceKernelGameAt g R lift).IsNash σ := by
  exact
    GameTheory.KernelGame.EUMorphism.nash_of_nash
      (G := backendEventBatchTraceKernelGameAt g R lift)
      (H := pureKernelGameAt g)
      (R.toBackendEventBatchTraceMorphism g lift)
      (σ := σ) h

/-- Nash equilibria of the public PMF-behavioral specification game pull back to
any backend equipped with a compatible behavioral event-batch-law lift. -/
theorem backendPMFBehavioralEventBatchTraceKernelGameAt_isNash_pullback
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g))
    (lift : BackendBehavioralEventBatchLawLift g R)
    {σ : behavioralProfilePMFAt g}
    (h : (pmfBehavioralKernelGameAt g).IsNash σ) :
    (backendPMFBehavioralEventBatchTraceKernelGameAt g R lift).IsNash σ := by
  exact
    GameTheory.KernelGame.EUMorphism.nash_of_nash
      (G := backendPMFBehavioralEventBatchTraceKernelGameAt g R lift)
      (H := pmfBehavioralKernelGameAt g)
      (R.toBackendPMFBehavioralEventBatchTraceMorphism g lift)
      (σ := σ) h

end Vegas
