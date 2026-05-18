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
theorem pureOutcomeKernelAt_eq_roundHistoryDist
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
round history distribution induced by the finite event-graph round view. -/
theorem behavioralOutcomeKernelPMFAt_eq_roundHistoryDist
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

/-- Order-free round history induced by the bounded native event-graph
round view. A bounded history records source state, legal joint action, and
realized destination for each frontier step, without recording a primitive
event schedule. -/
abbrev syntaxRoundHistoryAt
    (g : WFProgram P L) : Type :=
  (eventGraphRoundView g).BoundedHistory (syntaxSteps g.prog)

/-- Public outcome read from a round history. -/
noncomputable def syntaxRoundHistoryOutcome
    (g : WFProgram P L) :
    syntaxRoundHistoryAt g → Outcome P :=
  fun trace => (eventGraphMachine g).outcome trace.lastState.state

/-- Terminal public state read from a round history.

This is the public observation carried by the event-graph machine: completed
nodes plus public field values. It is intentionally separate from
`Outcome P`, which is only the payoff-vector projection. -/
noncomputable def syntaxRoundHistoryPublicState
    (g : WFProgram P L) :
    syntaxRoundHistoryAt g → ProgramPublicObs g :=
  fun trace => eventGraphPublicView g trace.lastState.state

/-- Utility read from a round history through its public outcome. -/
noncomputable def syntaxRoundHistoryUtility
    (g : WFProgram P L) :
    syntaxRoundHistoryAt g → GameTheory.Payoff P :=
  fun trace who => ((syntaxRoundHistoryOutcome g trace) who : ℝ)

/-- Canonical utility for payoff-vector outcomes. -/
noncomputable def publicOutcomeUtility :
    Outcome P → GameTheory.Payoff P :=
  fun outcome who => (outcome who : ℝ)

/-- Realization trace kernel induced by a pure profile. -/
noncomputable def pureRoundHistoryOutcomeKernelAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) : PMF (syntaxRoundHistoryAt g) :=
  (eventGraphRoundView g).runDist
    (syntaxSteps g.prog) (syntaxSteps g.prog)
    ((eventGraphRoundView g).legalPureToBehavioral
      (syntaxSteps g.prog) π)

/-- Realization trace kernel induced by a PMF behavioral profile. -/
noncomputable def behavioralRoundHistoryOutcomeKernelPMFAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) : PMF (syntaxRoundHistoryAt g) :=
  (eventGraphRoundView g).runDist
    (syntaxSteps g.prog) (syntaxSteps g.prog) β

/-- Pure terminal-public-state outcome kernel induced by a pure profile. -/
noncomputable def purePublicStateOutcomeKernelAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) : PMF (ProgramPublicObs g) :=
  PMF.map (syntaxRoundHistoryPublicState g)
    (pureRoundHistoryOutcomeKernelAt g π)

/-- PMF-behavioral terminal-public-state outcome kernel induced by a
behavioral profile. -/
noncomputable def behavioralPublicStateOutcomeKernelPMFAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) : PMF (ProgramPublicObs g) :=
  PMF.map (syntaxRoundHistoryPublicState g)
    (behavioralRoundHistoryOutcomeKernelPMFAt g β)

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
noncomputable def pureRoundHistoryGameFormAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.GameForm P where
  Strategy := pureStrategyAt g
  Outcome := syntaxRoundHistoryAt g
  outcomeKernel := pureRoundHistoryOutcomeKernelAt g

/-- Finite PMF-behavioral game form whose outcomes are bounded order-free
round histories. -/
noncomputable def pmfBehavioralRoundHistoryGameFormAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.GameForm P where
  Strategy := behavioralStrategyPMFAt g
  Outcome := syntaxRoundHistoryAt g
  outcomeKernel := behavioralRoundHistoryOutcomeKernelPMFAt g

/-- Finite pure strategic form whose outcomes are bounded order-free realization
traces rather than just terminal public outcomes. -/
noncomputable def pureRoundHistoryKernelGameAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame P :=
  (pureRoundHistoryGameFormAt g).withUtility (syntaxRoundHistoryUtility g)

@[simp] theorem pureRoundHistoryKernelGameAt_Strategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pureRoundHistoryKernelGameAt g).Strategy = pureStrategyAt g := rfl

@[simp] theorem pureRoundHistoryKernelGameAt_toGameForm
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pureRoundHistoryKernelGameAt g).toGameForm =
      pureRoundHistoryGameFormAt g := by
  rfl

@[simp] theorem purePublicStateGameFormAt_outcomeKernel
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : (purePublicStateGameFormAt g).Profile) :
    (purePublicStateGameFormAt g).outcomeKernel π =
      purePublicStateOutcomeKernelAt g π := rfl

/-- Finite PMF behavioral strategic form whose outcomes are bounded order-free
round histories rather than just terminal public outcomes. -/
noncomputable def pmfBehavioralRoundHistoryKernelGameAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame P :=
  (pmfBehavioralRoundHistoryGameFormAt g).withUtility
    (syntaxRoundHistoryUtility g)

@[simp] theorem pmfBehavioralRoundHistoryKernelGameAt_Strategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pmfBehavioralRoundHistoryKernelGameAt g).Strategy =
      behavioralStrategyPMFAt g := rfl

@[simp] theorem pmfBehavioralRoundHistoryKernelGameAt_toGameForm
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pmfBehavioralRoundHistoryKernelGameAt g).toGameForm =
      pmfBehavioralRoundHistoryGameFormAt g := by
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

/-- Projecting pure round history outcomes to public outcomes gives the public
pure strategic-form outcome kernel. -/
theorem pureRoundHistoryKernelGameAt_outcomeKernel_map_outcome
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) :
    PMF.map (syntaxRoundHistoryOutcome g)
        ((pureRoundHistoryKernelGameAt g).outcomeKernel π) =
      (pureKernelGameAt g).outcomeKernel π := by
  simpa [pureRoundHistoryKernelGameAt, pureKernelGameAt,
    pureRoundHistoryOutcomeKernelAt, syntaxRoundHistoryOutcome] using
    (pureOutcomeKernelAt_eq_roundHistoryDist g π).symm

/-- Projecting PMF behavioral round history outcomes to public outcomes gives
the public PMF behavioral strategic-form outcome kernel. -/
theorem pmfBehavioralRoundHistoryKernelGameAt_outcomeKernel_map_outcome
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) :
    PMF.map (syntaxRoundHistoryOutcome g)
        ((pmfBehavioralRoundHistoryKernelGameAt g).outcomeKernel β) =
      (pmfBehavioralKernelGameAt g).outcomeKernel β := by
  simpa [pmfBehavioralRoundHistoryKernelGameAt, pmfBehavioralKernelGameAt,
    behavioralRoundHistoryOutcomeKernelPMFAt, syntaxRoundHistoryOutcome] using
    (behavioralOutcomeKernelPMFAt_eq_roundHistoryDist g β).symm

/-- The round history pure game refines the public pure game by the public
outcome projection. The load-bearing field is PMF preservation of outcome
kernels under `syntaxRoundHistoryOutcome`. -/
noncomputable def pureKernelGameAt.roundHistoryProjection
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame.Simulation
      (pureKernelGameAt g) (pureRoundHistoryKernelGameAt g) :=
  GameTheory.KernelGame.Morphism.ofOutcomeProjection
    (fun _ strategy => strategy)
    (syntaxRoundHistoryOutcome g)
    (fun π => pureRoundHistoryKernelGameAt_outcomeKernel_map_outcome g π)
    (fun _ trace _ => by
      funext who
      rfl)

/-- The round history PMF behavioral game refines the public PMF behavioral
game by the public outcome projection. The load-bearing field is PMF
preservation of outcome kernels under `syntaxRoundHistoryOutcome`. -/
noncomputable def pmfBehavioralKernelGameAt.roundHistoryProjection
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame.Simulation
      (pmfBehavioralKernelGameAt g)
      (pmfBehavioralRoundHistoryKernelGameAt g) :=
  GameTheory.KernelGame.Morphism.ofOutcomeProjection
    (fun _ strategy => strategy)
    (syntaxRoundHistoryOutcome g)
    (fun β =>
      pmfBehavioralRoundHistoryKernelGameAt_outcomeKernel_map_outcome g β)
    (fun _ trace _ => by
      funext who
      rfl)

/-- Pure strategic-form play and round history play give the same expected
utility. -/
theorem pureRoundHistoryKernelGameAt_eu_eq
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) (who : P) :
    (pureRoundHistoryKernelGameAt g).eu π who =
      (pureKernelGameAt g).eu π who := by
  classical
  let traceDist : PMF (syntaxRoundHistoryAt g) :=
    (pureRoundHistoryKernelGameAt g).outcomeKernel π
  let projectOutcome := syntaxRoundHistoryOutcome g
  let utility := fun outcome : Outcome P => publicOutcomeUtility outcome who
  letI : Fintype (syntaxRoundHistoryAt g) :=
    (eventGraphRoundView g).instFintypeBoundedHistory (syntaxSteps g.prog)
  have houtcome :
      PMF.map projectOutcome traceDist =
        (pureKernelGameAt g).outcomeKernel π := by
    simpa [traceDist, projectOutcome] using
      pureRoundHistoryKernelGameAt_outcomeKernel_map_outcome g π
  calc
    (pureRoundHistoryKernelGameAt g).eu π who =
        Math.Probability.expect traceDist
          (fun trace => utility (projectOutcome trace)) := rfl
    _ =
        ∑ trace : syntaxRoundHistoryAt g,
          (traceDist trace).toReal * utility (projectOutcome trace) := by
          rw [Math.Probability.expect_eq_sum]
    _ =
        Math.Probability.expect (PMF.map projectOutcome traceDist)
          utility := by
          rw [Math.Probability.expect_map_fintype_source]
    _ = (pureKernelGameAt g).eu π who := by
          rw [houtcome]
          rfl

/-- PMF behavioral strategic-form play and round history play give the same
expected utility. -/
theorem pmfBehavioralRoundHistoryKernelGameAt_eu_eq
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) (who : P) :
    (pmfBehavioralRoundHistoryKernelGameAt g).eu β who =
      (pmfBehavioralKernelGameAt g).eu β who := by
  classical
  let traceDist : PMF (syntaxRoundHistoryAt g) :=
    (pmfBehavioralRoundHistoryKernelGameAt g).outcomeKernel β
  let projectOutcome := syntaxRoundHistoryOutcome g
  let utility := fun outcome : Outcome P => publicOutcomeUtility outcome who
  letI : Fintype (syntaxRoundHistoryAt g) :=
    (eventGraphRoundView g).instFintypeBoundedHistory (syntaxSteps g.prog)
  have houtcome :
      PMF.map projectOutcome traceDist =
        (pmfBehavioralKernelGameAt g).outcomeKernel β := by
    simpa [traceDist, projectOutcome] using
      pmfBehavioralRoundHistoryKernelGameAt_outcomeKernel_map_outcome g β
  calc
    (pmfBehavioralRoundHistoryKernelGameAt g).eu β who =
        Math.Probability.expect traceDist
          (fun trace => utility (projectOutcome trace)) := rfl
    _ =
        ∑ trace : syntaxRoundHistoryAt g,
          (traceDist trace).toReal * utility (projectOutcome trace) := by
          rw [Math.Probability.expect_eq_sum]
    _ =
        Math.Probability.expect (PMF.map projectOutcome traceDist)
          utility := by
          rw [Math.Probability.expect_map_fintype_source]
    _ = (pmfBehavioralKernelGameAt g).eu β who := by
          rw [houtcome]
          rfl

/-- Pure strategic-form play and round history play induce the same joint
utility distribution. -/
noncomputable def pureKernelGameAt.roundHistoryBisimulation
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame.Bisimulation
      (pureKernelGameAt g) (pureRoundHistoryKernelGameAt g) where
  stratEquiv := fun _ => Equiv.refl _
  udist_preserved := by
    intro π
    change
      ((pureRoundHistoryKernelGameAt g).outcomeKernel π).bind
          (fun trace =>
            PMF.pure ((pureRoundHistoryKernelGameAt g).utility trace)) =
        ((pureKernelGameAt g).outcomeKernel π).bind
          (fun outcome =>
            PMF.pure ((pureKernelGameAt g).utility outcome))
    rw [← pureRoundHistoryKernelGameAt_outcomeKernel_map_outcome g π]
    exact (PMF.bind_map
      ((pureRoundHistoryKernelGameAt g).outcomeKernel π)
      (syntaxRoundHistoryOutcome g)
      (fun outcome =>
        PMF.pure ((pureKernelGameAt g).utility outcome))).symm

/-- Pure strategic-form play and round history play are EU-preserving
bisimilar kernel games. -/
noncomputable def pureKernelGameAt.roundHistoryEUBisimulation
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame.EUGameIsomorphism
      (pureKernelGameAt g) (pureRoundHistoryKernelGameAt g) where
  toGameIsomorphism := pureKernelGameAt.roundHistoryBisimulation g
  eu_preserved := by
    intro π who
    exact pureRoundHistoryKernelGameAt_eu_eq g π who

/-- PMF behavioral strategic-form play and round history play induce the same
joint utility distribution. -/
noncomputable def pmfBehavioralKernelGameAt.roundHistoryBisimulation
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame.Bisimulation
      (pmfBehavioralKernelGameAt g)
      (pmfBehavioralRoundHistoryKernelGameAt g) where
  stratEquiv := fun _ => Equiv.refl _
  udist_preserved := by
    intro β
    change
      ((pmfBehavioralRoundHistoryKernelGameAt g).outcomeKernel β).bind
          (fun trace =>
            PMF.pure ((pmfBehavioralRoundHistoryKernelGameAt g).utility trace)) =
        ((pmfBehavioralKernelGameAt g).outcomeKernel β).bind
          (fun outcome =>
            PMF.pure ((pmfBehavioralKernelGameAt g).utility outcome))
    rw [← pmfBehavioralRoundHistoryKernelGameAt_outcomeKernel_map_outcome g β]
    exact (PMF.bind_map
      ((pmfBehavioralRoundHistoryKernelGameAt g).outcomeKernel β)
      (syntaxRoundHistoryOutcome g)
      (fun outcome =>
        PMF.pure ((pmfBehavioralKernelGameAt g).utility outcome))).symm

/-- PMF behavioral strategic-form play and round history play are
EU-preserving bisimilar kernel games. -/
noncomputable def pmfBehavioralKernelGameAt.roundHistoryEUBisimulation
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame.EUGameIsomorphism
      (pmfBehavioralKernelGameAt g)
      (pmfBehavioralRoundHistoryKernelGameAt g) where
  toGameIsomorphism :=
    pmfBehavioralKernelGameAt.roundHistoryBisimulation g
  eu_preserved := by
    intro β who
    exact pmfBehavioralRoundHistoryKernelGameAt_eu_eq g β who

end Vegas
