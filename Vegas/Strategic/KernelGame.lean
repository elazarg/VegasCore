import GameTheory.Core.GameSimulation
import Vegas.Core.Config
import Vegas.Strategic.Native

/-!
# Strategic kernel games

This module exposes the canonical finite strategic forms of checked Vegas
programs.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Outcome kernel of the finite pure strategic form of a checked Vegas
program. -/
noncomputable def pureOutcomeKernelAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) : PMF (Outcome P) := by
  classical
  exact
    (eventGraphRoundView g).boundedOutcomeFromPure
      (syntaxSteps g.prog) π (syntaxSteps g.prog)

/-- Outcome kernel of the finite PMF behavioral strategic form of a checked
Vegas program. -/
noncomputable def behavioralOutcomeKernelPMFAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) : PMF (Outcome P) := by
  classical
  exact
    (eventGraphRoundView g).boundedOutcomeFromBehavioral
      (syntaxSteps g.prog) β (syntaxSteps g.prog)

/-- Pure strategic-form outcomes are projections of the native realization
trace distribution induced by the finite event-graph round view. -/
theorem pureOutcomeKernelAt_eq_realizationTraceDist
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) :
    pureOutcomeKernelAt g π =
      PMF.map (fun trace : (eventGraphRoundView g).BoundedHistory
          (syntaxSteps g.prog) =>
          (eventGraphMachine g).outcome trace.lastState.state)
        ((eventGraphRoundView g).runDist
          (syntaxSteps g.prog) (syntaxSteps g.prog)
          ((eventGraphRoundView g).legalPureToBehavioral
            (syntaxSteps g.prog) π)) := by
  dsimp [pureOutcomeKernelAt, Machine.RoundView.boundedOutcomeFromPure,
    Machine.RoundView.boundedEventBatchTraceFromPure,
    Machine.RoundView.boundedEventBatchTraceFromBehavioral,
    Machine.RoundView.boundedHistoryTrace]
  rw [PMF.map_comp]
  rfl

/-- PMF behavioral strategic-form outcomes are projections of the native
realization trace distribution induced by the finite event-graph round view. -/
theorem behavioralOutcomeKernelPMFAt_eq_realizationTraceDist
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) :
    behavioralOutcomeKernelPMFAt g β =
      PMF.map (fun trace : (eventGraphRoundView g).BoundedHistory
          (syntaxSteps g.prog) =>
          (eventGraphMachine g).outcome trace.lastState.state)
        ((eventGraphRoundView g).runDist
          (syntaxSteps g.prog) (syntaxSteps g.prog) β) := by
  dsimp [behavioralOutcomeKernelPMFAt,
    Machine.RoundView.boundedOutcomeFromBehavioral,
    Machine.RoundView.boundedEventBatchTraceFromBehavioral,
    Machine.RoundView.boundedHistoryTrace]
  rw [PMF.map_comp]
  rfl

/-- Order-free realization trace induced by the bounded native event-graph
round view. A bounded history records source state, legal joint action, and
realized destination for each frontier round, without recording a primitive
event schedule. -/
abbrev syntaxRealizationTraceAt
    (g : WFProgram P L) : Type :=
  (eventGraphRoundView g).BoundedHistory (syntaxSteps g.prog)

/-- Public outcome read from a realization trace. -/
noncomputable def syntaxRealizationTraceOutcome
    (g : WFProgram P L) :
    syntaxRealizationTraceAt g → Outcome P :=
  fun trace => (eventGraphMachine g).outcome trace.lastState.state

/-- Terminal public state read from a realization trace.

This is the public observation carried by the event-graph machine: completed
nodes plus public field values. It is intentionally separate from
`Outcome P`, which is only the payoff-vector projection. -/
noncomputable def syntaxRealizationTracePublicState
    (g : WFProgram P L) :
    syntaxRealizationTraceAt g → ProgramPublicObs g :=
  fun trace => eventGraphPublicView g trace.lastState.state

/-- Utility read from a realization trace through its public outcome. -/
noncomputable def syntaxRealizationTraceUtility
    (g : WFProgram P L) :
    syntaxRealizationTraceAt g → GameTheory.Payoff P :=
  fun trace who => ((syntaxRealizationTraceOutcome g trace) who : ℝ)

/-- Canonical utility for payoff-vector outcomes. -/
noncomputable def publicOutcomeUtility :
    Outcome P → GameTheory.Payoff P :=
  fun outcome who => (outcome who : ℝ)

/-- Realization trace kernel induced by a pure profile. -/
noncomputable def pureRealizationTraceOutcomeKernelAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) : PMF (syntaxRealizationTraceAt g) :=
  (eventGraphRoundView g).runDist
    (syntaxSteps g.prog) (syntaxSteps g.prog)
    ((eventGraphRoundView g).legalPureToBehavioral
      (syntaxSteps g.prog) π)

/-- Realization trace kernel induced by a PMF behavioral profile. -/
noncomputable def behavioralRealizationTraceOutcomeKernelPMFAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) : PMF (syntaxRealizationTraceAt g) :=
  (eventGraphRoundView g).runDist
    (syntaxSteps g.prog) (syntaxSteps g.prog) β

/-- Pure terminal-public-state outcome kernel induced by a pure profile. -/
noncomputable def purePublicStateOutcomeKernelAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) : PMF (ProgramPublicObs g) :=
  PMF.map (syntaxRealizationTracePublicState g)
    (pureRealizationTraceOutcomeKernelAt g π)

/-- PMF-behavioral terminal-public-state outcome kernel induced by a
behavioral profile. -/
noncomputable def behavioralPublicStateOutcomeKernelPMFAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) : PMF (ProgramPublicObs g) :=
  PMF.map (syntaxRealizationTracePublicState g)
    (behavioralRealizationTraceOutcomeKernelPMFAt g β)

/-! ## Game forms -/

/-- Finite pure game form whose outcomes are terminal public machine states,
not payoff vectors. -/
noncomputable def purePublicStateGameFormAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.GameForm P where
  Strategy := pureStrategyAt g
  Outcome := ProgramPublicObs g
  outcomeKernel := purePublicStateOutcomeKernelAt g

/-- Finite PMF-behavioral game form whose outcomes are terminal public machine
states, not payoff vectors. -/
noncomputable def pmfBehavioralPublicStateGameFormAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.GameForm P where
  Strategy := behavioralStrategyPMFAt g
  Outcome := ProgramPublicObs g
  outcomeKernel := behavioralPublicStateOutcomeKernelPMFAt g

/-- Finite pure game form of a checked Vegas program, before utility is
attached. -/
noncomputable def pureGameFormAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.GameForm P where
  Strategy := pureStrategyAt g
  Outcome := Outcome P
  outcomeKernel := pureOutcomeKernelAt g

/-- Finite PMF-behavioral game form of a checked Vegas program, before utility
is attached. -/
noncomputable def pmfBehavioralGameFormAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.GameForm P where
  Strategy := behavioralStrategyPMFAt g
  Outcome := Outcome P
  outcomeKernel := behavioralOutcomeKernelPMFAt g

/-- Finite pure game form whose outcomes are bounded order-free realization
traces. -/
noncomputable def pureRealizationTraceGameFormAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.GameForm P where
  Strategy := pureStrategyAt g
  Outcome := syntaxRealizationTraceAt g
  outcomeKernel := pureRealizationTraceOutcomeKernelAt g

/-- Finite PMF-behavioral game form whose outcomes are bounded order-free
realization traces. -/
noncomputable def pmfBehavioralRealizationTraceGameFormAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.GameForm P where
  Strategy := behavioralStrategyPMFAt g
  Outcome := syntaxRealizationTraceAt g
  outcomeKernel := behavioralRealizationTraceOutcomeKernelPMFAt g

/-- Finite pure strategic form whose outcomes are bounded order-free realization
traces rather than just terminal public outcomes. -/
noncomputable def pureRealizationTraceKernelGameAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame P :=
  (pureRealizationTraceGameFormAt g).withUtility (syntaxRealizationTraceUtility g)

@[simp] theorem pureRealizationTraceKernelGameAt_Strategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pureRealizationTraceKernelGameAt g).Strategy = pureStrategyAt g := rfl

@[simp] theorem pureRealizationTraceKernelGameAt_toGameForm
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pureRealizationTraceKernelGameAt g).toGameForm =
      pureRealizationTraceGameFormAt g := by
  rfl

@[simp] theorem purePublicStateGameFormAt_outcomeKernel
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : (purePublicStateGameFormAt g).Profile) :
    (purePublicStateGameFormAt g).outcomeKernel π =
      purePublicStateOutcomeKernelAt g π := rfl

/-- Finite PMF behavioral strategic form whose outcomes are bounded order-free
realization traces rather than just terminal public outcomes. -/
noncomputable def pmfBehavioralRealizationTraceKernelGameAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame P :=
  (pmfBehavioralRealizationTraceGameFormAt g).withUtility
    (syntaxRealizationTraceUtility g)

@[simp] theorem pmfBehavioralRealizationTraceKernelGameAt_Strategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pmfBehavioralRealizationTraceKernelGameAt g).Strategy =
      behavioralStrategyPMFAt g := rfl

@[simp] theorem pmfBehavioralRealizationTraceKernelGameAt_toGameForm
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pmfBehavioralRealizationTraceKernelGameAt g).toGameForm =
      pmfBehavioralRealizationTraceGameFormAt g := by
  rfl

@[simp] theorem pmfBehavioralPublicStateGameFormAt_outcomeKernel
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : (pmfBehavioralPublicStateGameFormAt g).Profile) :
    (pmfBehavioralPublicStateGameFormAt g).outcomeKernel β =
      behavioralPublicStateOutcomeKernelPMFAt g β := rfl

/-- Finite pure strategic form of a checked Vegas program. -/
noncomputable def pureKernelGameAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame P :=
  (pureGameFormAt g).withUtility publicOutcomeUtility

@[simp] theorem pureKernelGameAt_Strategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pureKernelGameAt g).Strategy = pureStrategyAt g := rfl

@[simp] theorem pureKernelGameAt_outcomeKernel
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) :
    (pureKernelGameAt g).outcomeKernel π = pureOutcomeKernelAt g π := rfl

@[simp] theorem pureKernelGameAt_toGameForm
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pureKernelGameAt g).toGameForm = pureGameFormAt g := by
  rfl

/-- Finite pure strategies for the public pure kernel game. -/
noncomputable instance pureKernelGameAt.instFintypeStrategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] (who : P) :
    Fintype ((pureKernelGameAt g).Strategy who) := by
  classical
  change Fintype (pureStrategyAt g who)
  infer_instance

/-- Finite PMF behavioral strategic form of a checked Vegas program. -/
noncomputable def pmfBehavioralKernelGameAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame P :=
  (pmfBehavioralGameFormAt g).withUtility publicOutcomeUtility

@[simp] theorem pmfBehavioralKernelGameAt_Strategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pmfBehavioralKernelGameAt g).Strategy =
      behavioralStrategyPMFAt g := rfl

@[simp] theorem pmfBehavioralKernelGameAt_outcomeKernel
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) :
    (pmfBehavioralKernelGameAt g).outcomeKernel β =
      behavioralOutcomeKernelPMFAt g β := rfl

@[simp] theorem pmfBehavioralKernelGameAt_toGameForm
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pmfBehavioralKernelGameAt g).toGameForm =
      pmfBehavioralGameFormAt g := by
  rfl

/-- Projecting pure realization trace outcomes to public outcomes gives the public
pure strategic-form outcome kernel. -/
theorem pureRealizationTraceKernelGameAt_outcomeKernel_map_outcome
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) :
    PMF.map (syntaxRealizationTraceOutcome g)
        ((pureRealizationTraceKernelGameAt g).outcomeKernel π) =
      (pureKernelGameAt g).outcomeKernel π := by
  simpa [pureRealizationTraceKernelGameAt, pureKernelGameAt,
    pureRealizationTraceOutcomeKernelAt, syntaxRealizationTraceOutcome] using
    (pureOutcomeKernelAt_eq_realizationTraceDist g π).symm

/-- Projecting PMF behavioral realization trace outcomes to public outcomes gives
the public PMF behavioral strategic-form outcome kernel. -/
theorem pmfBehavioralRealizationTraceKernelGameAt_outcomeKernel_map_outcome
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) :
    PMF.map (syntaxRealizationTraceOutcome g)
        ((pmfBehavioralRealizationTraceKernelGameAt g).outcomeKernel β) =
      (pmfBehavioralKernelGameAt g).outcomeKernel β := by
  simpa [pmfBehavioralRealizationTraceKernelGameAt, pmfBehavioralKernelGameAt,
    behavioralRealizationTraceOutcomeKernelPMFAt, syntaxRealizationTraceOutcome] using
    (behavioralOutcomeKernelPMFAt_eq_realizationTraceDist g β).symm

/-- The realization trace pure game refines the public pure game by the public
outcome projection. The load-bearing field is PMF preservation of outcome
kernels under `syntaxRealizationTraceOutcome`. -/
noncomputable def pureKernelGameAt.realizationTraceProjection
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame.Simulation
      (pureKernelGameAt g) (pureRealizationTraceKernelGameAt g) :=
  GameTheory.KernelGame.Morphism.ofOutcomeProjection
    (fun _ strategy => strategy)
    (syntaxRealizationTraceOutcome g)
    (fun π => pureRealizationTraceKernelGameAt_outcomeKernel_map_outcome g π)
    (fun _ trace _ => by
      funext who
      rfl)

/-- The realization trace PMF behavioral game refines the public PMF behavioral
game by the public outcome projection. The load-bearing field is PMF
preservation of outcome kernels under `syntaxRealizationTraceOutcome`. -/
noncomputable def pmfBehavioralKernelGameAt.realizationTraceProjection
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame.Simulation
      (pmfBehavioralKernelGameAt g)
      (pmfBehavioralRealizationTraceKernelGameAt g) :=
  GameTheory.KernelGame.Morphism.ofOutcomeProjection
    (fun _ strategy => strategy)
    (syntaxRealizationTraceOutcome g)
    (fun β =>
      pmfBehavioralRealizationTraceKernelGameAt_outcomeKernel_map_outcome g β)
    (fun _ trace _ => by
      funext who
      rfl)

/-- Pure strategic-form play and realization trace play give the same expected
utility. -/
theorem pureRealizationTraceKernelGameAt_eu_eq
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) (who : P) :
    (pureRealizationTraceKernelGameAt g).eu π who =
      (pureKernelGameAt g).eu π who := by
  classical
  let traceDist : PMF (syntaxRealizationTraceAt g) :=
    (pureRealizationTraceKernelGameAt g).outcomeKernel π
  let projectOutcome := syntaxRealizationTraceOutcome g
  let utility := fun outcome : Outcome P => publicOutcomeUtility outcome who
  letI : Fintype (syntaxRealizationTraceAt g) :=
    (eventGraphRoundView g).instFintypeBoundedHistory (syntaxSteps g.prog)
  have houtcome :
      PMF.map projectOutcome traceDist =
        (pureKernelGameAt g).outcomeKernel π := by
    simpa [traceDist, projectOutcome] using
      pureRealizationTraceKernelGameAt_outcomeKernel_map_outcome g π
  calc
    (pureRealizationTraceKernelGameAt g).eu π who =
        Math.Probability.expect traceDist
          (fun trace => utility (projectOutcome trace)) := rfl
    _ =
        ∑ trace : syntaxRealizationTraceAt g,
          (traceDist trace).toReal * utility (projectOutcome trace) := by
          rw [Math.Probability.expect_eq_sum]
    _ =
        Math.Probability.expect (PMF.map projectOutcome traceDist)
          utility := by
          rw [Math.Probability.expect_map_fintype_source]
    _ = (pureKernelGameAt g).eu π who := by
          rw [houtcome]
          rfl

/-- PMF behavioral strategic-form play and realization trace play give the same
expected utility. -/
theorem pmfBehavioralRealizationTraceKernelGameAt_eu_eq
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) (who : P) :
    (pmfBehavioralRealizationTraceKernelGameAt g).eu β who =
      (pmfBehavioralKernelGameAt g).eu β who := by
  classical
  let traceDist : PMF (syntaxRealizationTraceAt g) :=
    (pmfBehavioralRealizationTraceKernelGameAt g).outcomeKernel β
  let projectOutcome := syntaxRealizationTraceOutcome g
  let utility := fun outcome : Outcome P => publicOutcomeUtility outcome who
  letI : Fintype (syntaxRealizationTraceAt g) :=
    (eventGraphRoundView g).instFintypeBoundedHistory (syntaxSteps g.prog)
  have houtcome :
      PMF.map projectOutcome traceDist =
        (pmfBehavioralKernelGameAt g).outcomeKernel β := by
    simpa [traceDist, projectOutcome] using
      pmfBehavioralRealizationTraceKernelGameAt_outcomeKernel_map_outcome g β
  calc
    (pmfBehavioralRealizationTraceKernelGameAt g).eu β who =
        Math.Probability.expect traceDist
          (fun trace => utility (projectOutcome trace)) := rfl
    _ =
        ∑ trace : syntaxRealizationTraceAt g,
          (traceDist trace).toReal * utility (projectOutcome trace) := by
          rw [Math.Probability.expect_eq_sum]
    _ =
        Math.Probability.expect (PMF.map projectOutcome traceDist)
          utility := by
          rw [Math.Probability.expect_map_fintype_source]
    _ = (pmfBehavioralKernelGameAt g).eu β who := by
          rw [houtcome]
          rfl

/-- Pure strategic-form play and realization trace play induce the same joint
utility distribution. -/
noncomputable def pureKernelGameAt.realizationTraceBisimulation
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame.Bisimulation
      (pureKernelGameAt g) (pureRealizationTraceKernelGameAt g) where
  stratEquiv := fun _ => Equiv.refl _
  udist_preserved := by
    intro π
    change
      ((pureRealizationTraceKernelGameAt g).outcomeKernel π).bind
          (fun trace =>
            PMF.pure ((pureRealizationTraceKernelGameAt g).utility trace)) =
        ((pureKernelGameAt g).outcomeKernel π).bind
          (fun outcome =>
            PMF.pure ((pureKernelGameAt g).utility outcome))
    rw [← pureRealizationTraceKernelGameAt_outcomeKernel_map_outcome g π]
    exact (PMF.bind_map
      ((pureRealizationTraceKernelGameAt g).outcomeKernel π)
      (syntaxRealizationTraceOutcome g)
      (fun outcome =>
        PMF.pure ((pureKernelGameAt g).utility outcome))).symm

/-- Pure strategic-form play and realization trace play are EU-preserving
bisimilar kernel games. -/
noncomputable def pureKernelGameAt.realizationTraceEUBisimulation
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame.EUGameIsomorphism
      (pureKernelGameAt g) (pureRealizationTraceKernelGameAt g) where
  toGameIsomorphism := pureKernelGameAt.realizationTraceBisimulation g
  eu_preserved := by
    intro π who
    exact pureRealizationTraceKernelGameAt_eu_eq g π who

/-- PMF behavioral strategic-form play and realization trace play induce the same
joint utility distribution. -/
noncomputable def pmfBehavioralKernelGameAt.realizationTraceBisimulation
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame.Bisimulation
      (pmfBehavioralKernelGameAt g)
      (pmfBehavioralRealizationTraceKernelGameAt g) where
  stratEquiv := fun _ => Equiv.refl _
  udist_preserved := by
    intro β
    change
      ((pmfBehavioralRealizationTraceKernelGameAt g).outcomeKernel β).bind
          (fun trace =>
            PMF.pure ((pmfBehavioralRealizationTraceKernelGameAt g).utility trace)) =
        ((pmfBehavioralKernelGameAt g).outcomeKernel β).bind
          (fun outcome =>
            PMF.pure ((pmfBehavioralKernelGameAt g).utility outcome))
    rw [← pmfBehavioralRealizationTraceKernelGameAt_outcomeKernel_map_outcome g β]
    exact (PMF.bind_map
      ((pmfBehavioralRealizationTraceKernelGameAt g).outcomeKernel β)
      (syntaxRealizationTraceOutcome g)
      (fun outcome =>
        PMF.pure ((pmfBehavioralKernelGameAt g).utility outcome))).symm

/-- PMF behavioral strategic-form play and realization trace play are
EU-preserving bisimilar kernel games. -/
noncomputable def pmfBehavioralKernelGameAt.realizationTraceEUBisimulation
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame.EUGameIsomorphism
      (pmfBehavioralKernelGameAt g)
      (pmfBehavioralRealizationTraceKernelGameAt g) where
  toGameIsomorphism :=
    pmfBehavioralKernelGameAt.realizationTraceBisimulation g
  eu_preserved := by
    intro β who
    exact pmfBehavioralRealizationTraceKernelGameAt_eu_eq g β who

end Vegas
