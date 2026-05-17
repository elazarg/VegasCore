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

/-- Pure strategic-form outcomes are machine-outcome projections of the
native event-batched primitive trace distribution induced by the finite event-graph
round view. -/
theorem pureOutcomeKernelAt_eq_eventBatchTraceDist
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) :
    pureOutcomeKernelAt g π =
      PMF.map
        (fun trace : (eventGraphMachine g).EventBatchTrace =>
          (eventGraphMachine g).outcome trace.2)
        ((eventGraphRoundView g).boundedEventBatchTraceFromPure
          (syntaxSteps g.prog) π (syntaxSteps g.prog)) := by
  rfl

/-- PMF behavioral strategic-form outcomes are machine-outcome projections of
the native event-batched primitive trace distribution induced by the finite
event-graph round view. -/
theorem behavioralOutcomeKernelPMFAt_eq_eventBatchTraceDist
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) :
    behavioralOutcomeKernelPMFAt g β =
      PMF.map
        (fun trace : (eventGraphMachine g).EventBatchTrace =>
          (eventGraphMachine g).outcome trace.2)
        ((eventGraphRoundView g).boundedEventBatchTraceFromBehavioral
          (syntaxSteps g.prog) β (syntaxSteps g.prog)) := by
  rfl

/-- Machine event-batch trace outcomes induced by the bounded native event-graph
round view: the primitive event batches executed so far, paired with the
resulting checkpoint state. -/
abbrev syntaxEventBatchTraceAt
    (g : WFProgram P L) : Type :=
  (eventGraphMachine g).EventBatchTrace

/-- Public outcome read from an event-batch machine trace. -/
noncomputable def syntaxEventBatchTraceOutcome
    (g : WFProgram P L) :
    syntaxEventBatchTraceAt g → Outcome P :=
  fun trace => (eventGraphMachine g).outcome trace.2

/-- Terminal public state read from an event-batch machine trace.

This is the public observation carried by the event-graph machine: completed
nodes plus public field values. It is intentionally separate from
`Outcome P`, which is only the payoff-vector projection. -/
noncomputable def syntaxEventBatchTracePublicState
    (g : WFProgram P L) :
    syntaxEventBatchTraceAt g → ProgramPublicObs g :=
  fun trace => eventGraphPublicView g trace.2

/-- Utility read from an event-batch machine trace through its public outcome. -/
noncomputable def syntaxEventBatchTraceUtility
    (g : WFProgram P L) :
    syntaxEventBatchTraceAt g → GameTheory.Payoff P :=
  fun trace who => ((syntaxEventBatchTraceOutcome g trace) who : ℝ)

/-- Canonical utility for payoff-vector outcomes. -/
noncomputable def publicOutcomeUtility :
    Outcome P → GameTheory.Payoff P :=
  fun outcome who => (outcome who : ℝ)

/-- Event-batched primitive trace kernel induced by a pure profile. -/
noncomputable def pureEventBatchTraceOutcomeKernelAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) : PMF (syntaxEventBatchTraceAt g) :=
  (eventGraphRoundView g).boundedEventBatchTraceFromPure
    (syntaxSteps g.prog) π (syntaxSteps g.prog)

/-- Event-batched primitive trace kernel induced by a PMF behavioral profile. -/
noncomputable def behavioralEventBatchTraceOutcomeKernelPMFAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) : PMF (syntaxEventBatchTraceAt g) :=
  (eventGraphRoundView g).boundedEventBatchTraceFromBehavioral
    (syntaxSteps g.prog) β (syntaxSteps g.prog)

/-- Pure terminal-public-state outcome kernel induced by a pure profile. -/
noncomputable def purePublicStateOutcomeKernelAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) : PMF (ProgramPublicObs g) :=
  PMF.map (syntaxEventBatchTracePublicState g)
    (pureEventBatchTraceOutcomeKernelAt g π)

/-- PMF-behavioral terminal-public-state outcome kernel induced by a
behavioral profile. -/
noncomputable def behavioralPublicStateOutcomeKernelPMFAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) : PMF (ProgramPublicObs g) :=
  PMF.map (syntaxEventBatchTracePublicState g)
    (behavioralEventBatchTraceOutcomeKernelPMFAt g β)

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

/-- Finite pure game form whose outcomes are event-batched primitive machine traces. -/
noncomputable def pureEventBatchTraceGameFormAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.GameForm P where
  Strategy := pureStrategyAt g
  Outcome := syntaxEventBatchTraceAt g
  outcomeKernel := pureEventBatchTraceOutcomeKernelAt g

/-- Finite PMF-behavioral game form whose outcomes are event-batched primitive
machine traces. -/
noncomputable def pmfBehavioralEventBatchTraceGameFormAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.GameForm P where
  Strategy := behavioralStrategyPMFAt g
  Outcome := syntaxEventBatchTraceAt g
  outcomeKernel := behavioralEventBatchTraceOutcomeKernelPMFAt g

/-- Finite pure strategic form whose outcomes are event-batched primitive machine
traces rather than just terminal public outcomes. -/
noncomputable def pureEventBatchTraceKernelGameAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame P :=
  (pureEventBatchTraceGameFormAt g).withUtility (syntaxEventBatchTraceUtility g)

@[simp] theorem pureEventBatchTraceKernelGameAt_Strategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pureEventBatchTraceKernelGameAt g).Strategy = pureStrategyAt g := rfl

@[simp] theorem pureEventBatchTraceKernelGameAt_toGameForm
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pureEventBatchTraceKernelGameAt g).toGameForm =
      pureEventBatchTraceGameFormAt g := by
  rfl

@[simp] theorem purePublicStateGameFormAt_outcomeKernel
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : (purePublicStateGameFormAt g).Profile) :
    (purePublicStateGameFormAt g).outcomeKernel π =
      purePublicStateOutcomeKernelAt g π := rfl

/-- Finite PMF behavioral strategic form whose outcomes are event-batched primitive
machine traces rather than just terminal public outcomes. -/
noncomputable def pmfBehavioralEventBatchTraceKernelGameAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame P :=
  (pmfBehavioralEventBatchTraceGameFormAt g).withUtility
    (syntaxEventBatchTraceUtility g)

@[simp] theorem pmfBehavioralEventBatchTraceKernelGameAt_Strategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pmfBehavioralEventBatchTraceKernelGameAt g).Strategy =
      behavioralStrategyPMFAt g := rfl

@[simp] theorem pmfBehavioralEventBatchTraceKernelGameAt_toGameForm
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pmfBehavioralEventBatchTraceKernelGameAt g).toGameForm =
      pmfBehavioralEventBatchTraceGameFormAt g := by
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

/-- Projecting pure event-batch trace outcomes to public outcomes gives the public
pure strategic-form outcome kernel. -/
theorem pureEventBatchTraceKernelGameAt_outcomeKernel_map_outcome
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) :
    PMF.map (syntaxEventBatchTraceOutcome g)
        ((pureEventBatchTraceKernelGameAt g).outcomeKernel π) =
      (pureKernelGameAt g).outcomeKernel π := by
  simpa [pureEventBatchTraceKernelGameAt, pureKernelGameAt,
    pureEventBatchTraceOutcomeKernelAt, syntaxEventBatchTraceOutcome] using
    (pureOutcomeKernelAt_eq_eventBatchTraceDist g π).symm

/-- Projecting PMF behavioral event-batch trace outcomes to public outcomes gives
the public PMF behavioral strategic-form outcome kernel. -/
theorem pmfBehavioralEventBatchTraceKernelGameAt_outcomeKernel_map_outcome
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) :
    PMF.map (syntaxEventBatchTraceOutcome g)
        ((pmfBehavioralEventBatchTraceKernelGameAt g).outcomeKernel β) =
      (pmfBehavioralKernelGameAt g).outcomeKernel β := by
  simpa [pmfBehavioralEventBatchTraceKernelGameAt, pmfBehavioralKernelGameAt,
    behavioralEventBatchTraceOutcomeKernelPMFAt, syntaxEventBatchTraceOutcome] using
    (behavioralOutcomeKernelPMFAt_eq_eventBatchTraceDist g β).symm

/-- The event-batch trace pure game refines the public pure game by the public
outcome projection. The load-bearing field is PMF preservation of outcome
kernels under `syntaxEventBatchTraceOutcome`. -/
noncomputable def pureKernelGameAt.eventBatchTraceProjection
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame.Simulation
      (pureKernelGameAt g) (pureEventBatchTraceKernelGameAt g) :=
  GameTheory.KernelGame.Morphism.ofOutcomeProjection
    (fun _ strategy => strategy)
    (syntaxEventBatchTraceOutcome g)
    (fun π => pureEventBatchTraceKernelGameAt_outcomeKernel_map_outcome g π)
    (fun _ trace _ => by
      funext who
      rfl)

/-- The event-batch trace PMF behavioral game refines the public PMF behavioral
game by the public outcome projection. The load-bearing field is PMF
preservation of outcome kernels under `syntaxEventBatchTraceOutcome`. -/
noncomputable def pmfBehavioralKernelGameAt.eventBatchTraceProjection
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame.Simulation
      (pmfBehavioralKernelGameAt g)
      (pmfBehavioralEventBatchTraceKernelGameAt g) :=
  GameTheory.KernelGame.Morphism.ofOutcomeProjection
    (fun _ strategy => strategy)
    (syntaxEventBatchTraceOutcome g)
    (fun β =>
      pmfBehavioralEventBatchTraceKernelGameAt_outcomeKernel_map_outcome g β)
    (fun _ trace _ => by
      funext who
      rfl)

omit [DecidableEq P] in
/-- If two outcome kernels are projections of the same finite source run and
the projected utilities agree pointwise, their expected utility agrees. -/
theorem expect_eq_of_projected_kernel
    {α β γ : Type} [Finite α]
    (run : PMF α)
    (projectTrace : α → β) (projectOutcome : α → γ)
    (traceUtility : β → P → ℝ) (outcomeUtility : γ → P → ℝ)
    (who : P)
    (hutility :
      ∀ h, traceUtility (projectTrace h) who =
        outcomeUtility (projectOutcome h) who) :
    Math.Probability.expect (PMF.map projectTrace run)
        (fun trace => traceUtility trace who) =
      Math.Probability.expect (PMF.map projectOutcome run)
        (fun outcome => outcomeUtility outcome who) := by
  classical
  letI := Fintype.ofFinite α
  calc
    Math.Probability.expect (PMF.map projectTrace run)
        (fun trace => traceUtility trace who) =
        ∑ h : α, (run h).toReal * traceUtility (projectTrace h) who := by
          rw [Math.Probability.expect_map_fintype_source]
    _ =
        ∑ h : α, (run h).toReal * outcomeUtility (projectOutcome h) who := by
          refine Finset.sum_congr rfl ?_
          intro h _
          rw [hutility h]
    _ =
      Math.Probability.expect (PMF.map projectOutcome run)
        (fun outcome => outcomeUtility outcome who) := by
          rw [Math.Probability.expect_map_fintype_source]

/-- Pure strategic-form play and event-batch trace play give the same expected
utility. -/
theorem pureEventBatchTraceKernelGameAt_eu_eq
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) (who : P) :
    (pureEventBatchTraceKernelGameAt g).eu π who =
      (pureKernelGameAt g).eu π who := by
  classical
  let horizon := syntaxSteps g.prog
  let G := eventGraphRoundView g
  let σ := G.legalPureToBehavioral horizon π
  let run := G.runDist horizon horizon σ
  let projectTrace : G.BoundedHistory horizon → syntaxEventBatchTraceAt g :=
    fun h' => G.boundedHistoryTrace horizon h'
  let projectOutcome : G.BoundedHistory horizon → Outcome P :=
    fun h' => (eventGraphMachine g).outcome h'.lastState.state
  letI : Fintype (G.BoundedHistory horizon) :=
    G.instFintypeBoundedHistory horizon
  have htrace :
      (pureEventBatchTraceKernelGameAt g).outcomeKernel π =
        PMF.map projectTrace run := by
    simp [pureEventBatchTraceKernelGameAt, pureEventBatchTraceOutcomeKernelAt,
      pureEventBatchTraceGameFormAt,
      Machine.RoundView.boundedEventBatchTraceFromPure,
      Machine.RoundView.boundedEventBatchTraceFromBehavioral,
      Machine.RoundView.runDist, projectTrace, run, σ, G, horizon]
  have hpublic :
      (pureKernelGameAt g).outcomeKernel π =
        PMF.map projectOutcome run := by
    rw [pureKernelGameAt_outcomeKernel]
    dsimp [pureOutcomeKernelAt, Machine.RoundView.boundedOutcomeFromPure,
      Machine.RoundView.boundedEventBatchTraceFromPure,
      Machine.RoundView.boundedEventBatchTraceFromBehavioral,
      Machine.RoundView.runDist, projectOutcome, run, σ, G, horizon]
    rw [PMF.map_comp]
    rfl
  calc
    (pureEventBatchTraceKernelGameAt g).eu π who =
        Math.Probability.expect
          ((pureEventBatchTraceKernelGameAt g).outcomeKernel π)
          (fun trace => (pureEventBatchTraceKernelGameAt g).utility trace who) := rfl
    _ =
        Math.Probability.expect (PMF.map projectTrace run)
          (fun trace => (pureEventBatchTraceKernelGameAt g).utility trace who) := by
          rw [htrace]
          rfl
    _ =
        Math.Probability.expect (PMF.map projectOutcome run)
          (fun outcome => (pureKernelGameAt g).utility outcome who) := by
          exact expect_eq_of_projected_kernel run projectTrace projectOutcome
            (pureEventBatchTraceKernelGameAt g).utility
            (pureKernelGameAt g).utility who (fun _ => rfl)
    _ = (pureKernelGameAt g).eu π who := by
          rw [← hpublic]
          rfl

/-- PMF behavioral strategic-form play and event-batch trace play give the same
expected utility. -/
theorem pmfBehavioralEventBatchTraceKernelGameAt_eu_eq
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) (who : P) :
    (pmfBehavioralEventBatchTraceKernelGameAt g).eu β who =
      (pmfBehavioralKernelGameAt g).eu β who := by
  classical
  let horizon := syntaxSteps g.prog
  let G := eventGraphRoundView g
  let σ := β
  let run := G.runDist horizon horizon σ
  let projectTrace : G.BoundedHistory horizon → syntaxEventBatchTraceAt g :=
    fun h' => G.boundedHistoryTrace horizon h'
  let projectOutcome : G.BoundedHistory horizon → Outcome P :=
    fun h' => (eventGraphMachine g).outcome h'.lastState.state
  letI : Fintype (G.BoundedHistory horizon) :=
    G.instFintypeBoundedHistory horizon
  have htrace :
      (pmfBehavioralEventBatchTraceKernelGameAt g).outcomeKernel β =
        PMF.map projectTrace run := by
    simp [pmfBehavioralEventBatchTraceKernelGameAt,
      behavioralEventBatchTraceOutcomeKernelPMFAt,
      pmfBehavioralEventBatchTraceGameFormAt,
      Machine.RoundView.boundedEventBatchTraceFromBehavioral,
      Machine.RoundView.runDist, projectTrace, run, σ, G, horizon]
  have hpublic :
      (pmfBehavioralKernelGameAt g).outcomeKernel β =
        PMF.map projectOutcome run := by
    rw [pmfBehavioralKernelGameAt_outcomeKernel]
    dsimp [behavioralOutcomeKernelPMFAt,
      Machine.RoundView.boundedOutcomeFromBehavioral,
      Machine.RoundView.boundedEventBatchTraceFromBehavioral,
      Machine.RoundView.runDist, projectOutcome, run, σ, G, horizon]
    rw [PMF.map_comp]
    rfl
  calc
    (pmfBehavioralEventBatchTraceKernelGameAt g).eu β who =
        Math.Probability.expect
          ((pmfBehavioralEventBatchTraceKernelGameAt g).outcomeKernel β)
          (fun trace =>
            (pmfBehavioralEventBatchTraceKernelGameAt g).utility trace who) := rfl
    _ =
        Math.Probability.expect (PMF.map projectTrace run)
          (fun trace =>
            (pmfBehavioralEventBatchTraceKernelGameAt g).utility trace who) := by
          rw [htrace]
          rfl
    _ =
        Math.Probability.expect (PMF.map projectOutcome run)
          (fun outcome => (pmfBehavioralKernelGameAt g).utility outcome who) := by
          exact expect_eq_of_projected_kernel run projectTrace projectOutcome
            (pmfBehavioralEventBatchTraceKernelGameAt g).utility
            (pmfBehavioralKernelGameAt g).utility who (fun _ => rfl)
    _ = (pmfBehavioralKernelGameAt g).eu β who := by
          rw [← hpublic]
          rfl

/-- Pure strategic-form play and event-batch trace play induce the same joint
utility distribution. -/
noncomputable def pureKernelGameAt.eventBatchTraceBisimulation
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame.Bisimulation
      (pureKernelGameAt g) (pureEventBatchTraceKernelGameAt g) where
  stratEquiv := fun _ => Equiv.refl _
  udist_preserved := by
    intro π
    change
      ((pureEventBatchTraceKernelGameAt g).outcomeKernel π).bind
          (fun trace =>
            PMF.pure ((pureEventBatchTraceKernelGameAt g).utility trace)) =
        ((pureKernelGameAt g).outcomeKernel π).bind
          (fun outcome =>
            PMF.pure ((pureKernelGameAt g).utility outcome))
    rw [← pureEventBatchTraceKernelGameAt_outcomeKernel_map_outcome g π]
    exact (PMF.bind_map
      ((pureEventBatchTraceKernelGameAt g).outcomeKernel π)
      (syntaxEventBatchTraceOutcome g)
      (fun outcome =>
        PMF.pure ((pureKernelGameAt g).utility outcome))).symm

/-- Pure strategic-form play and event-batch trace play are EU-preserving
bisimilar kernel games. -/
noncomputable def pureKernelGameAt.eventBatchTraceEUBisimulation
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame.EUGameIsomorphism
      (pureKernelGameAt g) (pureEventBatchTraceKernelGameAt g) where
  toGameIsomorphism := pureKernelGameAt.eventBatchTraceBisimulation g
  eu_preserved := by
    intro π who
    exact pureEventBatchTraceKernelGameAt_eu_eq g π who

/-- PMF behavioral strategic-form play and event-batch trace play induce the same
joint utility distribution. -/
noncomputable def pmfBehavioralKernelGameAt.eventBatchTraceBisimulation
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame.Bisimulation
      (pmfBehavioralKernelGameAt g)
      (pmfBehavioralEventBatchTraceKernelGameAt g) where
  stratEquiv := fun _ => Equiv.refl _
  udist_preserved := by
    intro β
    change
      ((pmfBehavioralEventBatchTraceKernelGameAt g).outcomeKernel β).bind
          (fun trace =>
            PMF.pure ((pmfBehavioralEventBatchTraceKernelGameAt g).utility trace)) =
        ((pmfBehavioralKernelGameAt g).outcomeKernel β).bind
          (fun outcome =>
            PMF.pure ((pmfBehavioralKernelGameAt g).utility outcome))
    rw [← pmfBehavioralEventBatchTraceKernelGameAt_outcomeKernel_map_outcome g β]
    exact (PMF.bind_map
      ((pmfBehavioralEventBatchTraceKernelGameAt g).outcomeKernel β)
      (syntaxEventBatchTraceOutcome g)
      (fun outcome =>
        PMF.pure ((pmfBehavioralKernelGameAt g).utility outcome))).symm

/-- PMF behavioral strategic-form play and event-batch trace play are
EU-preserving bisimilar kernel games. -/
noncomputable def pmfBehavioralKernelGameAt.eventBatchTraceEUBisimulation
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame.EUGameIsomorphism
      (pmfBehavioralKernelGameAt g)
      (pmfBehavioralEventBatchTraceKernelGameAt g) where
  toGameIsomorphism :=
    pmfBehavioralKernelGameAt.eventBatchTraceBisimulation g
  eu_preserved := by
    intro β who
    exact pmfBehavioralEventBatchTraceKernelGameAt_eu_eq g β who

end Vegas
