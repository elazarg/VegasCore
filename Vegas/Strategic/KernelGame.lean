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
native blocked primitive trace distribution induced by the finite event-graph
round view. -/
theorem pureOutcomeKernelAt_eq_blockTraceDist
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) :
    pureOutcomeKernelAt g π =
      PMF.map
        (fun trace : (eventGraphMachine g).BlockTrace =>
          (eventGraphMachine g).outcome trace.2)
        ((eventGraphRoundView g).boundedBlockTraceFromPure
          (syntaxSteps g.prog) π (syntaxSteps g.prog)) := by
  rfl

/-- PMF behavioral strategic-form outcomes are machine-outcome projections of
the native blocked primitive trace distribution induced by the finite
event-graph round view. -/
theorem behavioralOutcomeKernelPMFAt_eq_blockTraceDist
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) :
    behavioralOutcomeKernelPMFAt g β =
      PMF.map
        (fun trace : (eventGraphMachine g).BlockTrace =>
          (eventGraphMachine g).outcome trace.2)
        ((eventGraphRoundView g).boundedBlockTraceFromBehavioral
          (syntaxSteps g.prog) β (syntaxSteps g.prog)) := by
  rfl

/-- Machine blocked trace outcomes induced by the bounded native event-graph
round view: the primitive event blocks executed so far, paired with the
resulting checkpoint state. -/
abbrev syntaxBlockedTraceAt
    (g : WFProgram P L) : Type :=
  (eventGraphMachine g).BlockTrace

/-- Public outcome read from a blocked machine trace. -/
noncomputable def syntaxBlockedTraceOutcome
    (g : WFProgram P L) :
    syntaxBlockedTraceAt g → Outcome P :=
  fun trace => (eventGraphMachine g).outcome trace.2

/-- Terminal public state read from a blocked machine trace.

This is the public observation carried by the event-graph machine: completed
nodes plus public field values. It is intentionally separate from
`Outcome P`, which is only the payoff-vector projection. -/
noncomputable def syntaxBlockedTracePublicState
    (g : WFProgram P L) :
    syntaxBlockedTraceAt g → ProgramPublicObs g :=
  fun trace => eventGraphPublicView g trace.2

/-- Utility read from a blocked machine trace through its public outcome. -/
noncomputable def syntaxBlockedTraceUtility
    (g : WFProgram P L) :
    syntaxBlockedTraceAt g → GameTheory.Payoff P :=
  fun trace who => ((syntaxBlockedTraceOutcome g trace) who : ℝ)

/-- Canonical utility for payoff-vector outcomes. -/
noncomputable def publicOutcomeUtility :
    Outcome P → GameTheory.Payoff P :=
  fun outcome who => (outcome who : ℝ)

/-- Blocked primitive trace kernel induced by a pure profile. -/
noncomputable def pureBlockedTraceOutcomeKernelAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) : PMF (syntaxBlockedTraceAt g) :=
  (eventGraphRoundView g).boundedBlockTraceFromPure
    (syntaxSteps g.prog) π (syntaxSteps g.prog)

/-- Blocked primitive trace kernel induced by a PMF behavioral profile. -/
noncomputable def behavioralBlockedTraceOutcomeKernelPMFAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) : PMF (syntaxBlockedTraceAt g) :=
  (eventGraphRoundView g).boundedBlockTraceFromBehavioral
    (syntaxSteps g.prog) β (syntaxSteps g.prog)

/-- Pure terminal-public-state outcome kernel induced by a pure profile. -/
noncomputable def purePublicStateOutcomeKernelAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) : PMF (ProgramPublicObs g) :=
  PMF.map (syntaxBlockedTracePublicState g)
    (pureBlockedTraceOutcomeKernelAt g π)

/-- PMF-behavioral terminal-public-state outcome kernel induced by a
behavioral profile. -/
noncomputable def behavioralPublicStateOutcomeKernelPMFAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) : PMF (ProgramPublicObs g) :=
  PMF.map (syntaxBlockedTracePublicState g)
    (behavioralBlockedTraceOutcomeKernelPMFAt g β)

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

/-- Finite pure game form whose outcomes are blocked primitive machine traces. -/
noncomputable def pureBlockedTraceGameFormAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.GameForm P where
  Strategy := pureStrategyAt g
  Outcome := syntaxBlockedTraceAt g
  outcomeKernel := pureBlockedTraceOutcomeKernelAt g

/-- Finite PMF-behavioral game form whose outcomes are blocked primitive
machine traces. -/
noncomputable def pmfBehavioralBlockedTraceGameFormAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.GameForm P where
  Strategy := behavioralStrategyPMFAt g
  Outcome := syntaxBlockedTraceAt g
  outcomeKernel := behavioralBlockedTraceOutcomeKernelPMFAt g

/-- Finite pure strategic form whose outcomes are blocked primitive machine
traces rather than just terminal public outcomes. -/
noncomputable def pureBlockedTraceKernelGameAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame P :=
  (pureBlockedTraceGameFormAt g).withUtility (syntaxBlockedTraceUtility g)

@[simp] theorem pureBlockedTraceKernelGameAt_Strategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pureBlockedTraceKernelGameAt g).Strategy = pureStrategyAt g := rfl

@[simp] theorem pureBlockedTraceKernelGameAt_toGameForm
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pureBlockedTraceKernelGameAt g).toGameForm =
      pureBlockedTraceGameFormAt g := by
  rfl

@[simp] theorem purePublicStateGameFormAt_outcomeKernel
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : (purePublicStateGameFormAt g).Profile) :
    (purePublicStateGameFormAt g).outcomeKernel π =
      purePublicStateOutcomeKernelAt g π := rfl

/-- Finite PMF behavioral strategic form whose outcomes are blocked primitive
machine traces rather than just terminal public outcomes. -/
noncomputable def pmfBehavioralBlockedTraceKernelGameAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame P :=
  (pmfBehavioralBlockedTraceGameFormAt g).withUtility
    (syntaxBlockedTraceUtility g)

@[simp] theorem pmfBehavioralBlockedTraceKernelGameAt_Strategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pmfBehavioralBlockedTraceKernelGameAt g).Strategy =
      behavioralStrategyPMFAt g := rfl

@[simp] theorem pmfBehavioralBlockedTraceKernelGameAt_toGameForm
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pmfBehavioralBlockedTraceKernelGameAt g).toGameForm =
      pmfBehavioralBlockedTraceGameFormAt g := by
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

/-- Projecting pure blocked-trace outcomes to public outcomes gives the public
pure strategic-form outcome kernel. -/
theorem pureBlockedTraceKernelGameAt_outcomeKernel_map_outcome
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) :
    PMF.map (syntaxBlockedTraceOutcome g)
        ((pureBlockedTraceKernelGameAt g).outcomeKernel π) =
      (pureKernelGameAt g).outcomeKernel π := by
  simpa [pureBlockedTraceKernelGameAt, pureKernelGameAt,
    pureBlockedTraceOutcomeKernelAt, syntaxBlockedTraceOutcome] using
    (pureOutcomeKernelAt_eq_blockTraceDist g π).symm

/-- Projecting PMF behavioral blocked-trace outcomes to public outcomes gives
the public PMF behavioral strategic-form outcome kernel. -/
theorem pmfBehavioralBlockedTraceKernelGameAt_outcomeKernel_map_outcome
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) :
    PMF.map (syntaxBlockedTraceOutcome g)
        ((pmfBehavioralBlockedTraceKernelGameAt g).outcomeKernel β) =
      (pmfBehavioralKernelGameAt g).outcomeKernel β := by
  simpa [pmfBehavioralBlockedTraceKernelGameAt, pmfBehavioralKernelGameAt,
    behavioralBlockedTraceOutcomeKernelPMFAt, syntaxBlockedTraceOutcome] using
    (behavioralOutcomeKernelPMFAt_eq_blockTraceDist g β).symm

/-- The blocked-trace pure game refines the public pure game by the public
outcome projection. The load-bearing field is PMF preservation of outcome
kernels under `syntaxBlockedTraceOutcome`. -/
noncomputable def pureKernelGameAt.blockedTraceProjection
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame.Simulation
      (pureKernelGameAt g) (pureBlockedTraceKernelGameAt g) :=
  GameTheory.KernelGame.Morphism.ofOutcomeProjection
    (fun _ strategy => strategy)
    (syntaxBlockedTraceOutcome g)
    (fun π => pureBlockedTraceKernelGameAt_outcomeKernel_map_outcome g π)
    (fun _ trace _ => by
      funext who
      rfl)

/-- The blocked-trace PMF behavioral game refines the public PMF behavioral
game by the public outcome projection. The load-bearing field is PMF
preservation of outcome kernels under `syntaxBlockedTraceOutcome`. -/
noncomputable def pmfBehavioralKernelGameAt.blockedTraceProjection
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame.Simulation
      (pmfBehavioralKernelGameAt g)
      (pmfBehavioralBlockedTraceKernelGameAt g) :=
  GameTheory.KernelGame.Morphism.ofOutcomeProjection
    (fun _ strategy => strategy)
    (syntaxBlockedTraceOutcome g)
    (fun β =>
      pmfBehavioralBlockedTraceKernelGameAt_outcomeKernel_map_outcome g β)
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

/-- Pure strategic-form play and blocked-trace play give the same expected
utility. -/
theorem pureBlockedTraceKernelGameAt_eu_eq
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) (who : P) :
    (pureBlockedTraceKernelGameAt g).eu π who =
      (pureKernelGameAt g).eu π who := by
  classical
  let horizon := syntaxSteps g.prog
  let G := eventGraphRoundView g
  let σ := G.legalPureToBehavioral horizon π
  let run := G.runDist horizon horizon σ
  let projectTrace : G.BoundedHistory horizon → syntaxBlockedTraceAt g :=
    fun h' => G.boundedHistoryTrace horizon h'
  let projectOutcome : G.BoundedHistory horizon → Outcome P :=
    fun h' => (eventGraphMachine g).outcome h'.lastState.state
  letI : Fintype (G.BoundedHistory horizon) :=
    G.instFintypeBoundedHistory horizon
  have htrace :
      (pureBlockedTraceKernelGameAt g).outcomeKernel π =
        PMF.map projectTrace run := by
    simp [pureBlockedTraceKernelGameAt, pureBlockedTraceOutcomeKernelAt,
      pureBlockedTraceGameFormAt,
      Machine.RoundView.boundedBlockTraceFromPure,
      Machine.RoundView.boundedBlockTraceFromBehavioral,
      Machine.RoundView.runDist, projectTrace, run, σ, G, horizon]
  have hpublic :
      (pureKernelGameAt g).outcomeKernel π =
        PMF.map projectOutcome run := by
    rw [pureKernelGameAt_outcomeKernel]
    dsimp [pureOutcomeKernelAt, Machine.RoundView.boundedOutcomeFromPure,
      Machine.RoundView.boundedBlockTraceFromPure,
      Machine.RoundView.boundedBlockTraceFromBehavioral,
      Machine.RoundView.runDist, projectOutcome, run, σ, G, horizon]
    rw [PMF.map_comp]
    rfl
  calc
    (pureBlockedTraceKernelGameAt g).eu π who =
        Math.Probability.expect
          ((pureBlockedTraceKernelGameAt g).outcomeKernel π)
          (fun trace => (pureBlockedTraceKernelGameAt g).utility trace who) := rfl
    _ =
        Math.Probability.expect (PMF.map projectTrace run)
          (fun trace => (pureBlockedTraceKernelGameAt g).utility trace who) := by
          rw [htrace]
          rfl
    _ =
        Math.Probability.expect (PMF.map projectOutcome run)
          (fun outcome => (pureKernelGameAt g).utility outcome who) := by
          exact expect_eq_of_projected_kernel run projectTrace projectOutcome
            (pureBlockedTraceKernelGameAt g).utility
            (pureKernelGameAt g).utility who (fun _ => rfl)
    _ = (pureKernelGameAt g).eu π who := by
          rw [← hpublic]
          rfl

/-- PMF behavioral strategic-form play and blocked-trace play give the same
expected utility. -/
theorem pmfBehavioralBlockedTraceKernelGameAt_eu_eq
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) (who : P) :
    (pmfBehavioralBlockedTraceKernelGameAt g).eu β who =
      (pmfBehavioralKernelGameAt g).eu β who := by
  classical
  let horizon := syntaxSteps g.prog
  let G := eventGraphRoundView g
  let σ := β
  let run := G.runDist horizon horizon σ
  let projectTrace : G.BoundedHistory horizon → syntaxBlockedTraceAt g :=
    fun h' => G.boundedHistoryTrace horizon h'
  let projectOutcome : G.BoundedHistory horizon → Outcome P :=
    fun h' => (eventGraphMachine g).outcome h'.lastState.state
  letI : Fintype (G.BoundedHistory horizon) :=
    G.instFintypeBoundedHistory horizon
  have htrace :
      (pmfBehavioralBlockedTraceKernelGameAt g).outcomeKernel β =
        PMF.map projectTrace run := by
    simp [pmfBehavioralBlockedTraceKernelGameAt,
      behavioralBlockedTraceOutcomeKernelPMFAt,
      pmfBehavioralBlockedTraceGameFormAt,
      Machine.RoundView.boundedBlockTraceFromBehavioral,
      Machine.RoundView.runDist, projectTrace, run, σ, G, horizon]
  have hpublic :
      (pmfBehavioralKernelGameAt g).outcomeKernel β =
        PMF.map projectOutcome run := by
    rw [pmfBehavioralKernelGameAt_outcomeKernel]
    dsimp [behavioralOutcomeKernelPMFAt,
      Machine.RoundView.boundedOutcomeFromBehavioral,
      Machine.RoundView.boundedBlockTraceFromBehavioral,
      Machine.RoundView.runDist, projectOutcome, run, σ, G, horizon]
    rw [PMF.map_comp]
    rfl
  calc
    (pmfBehavioralBlockedTraceKernelGameAt g).eu β who =
        Math.Probability.expect
          ((pmfBehavioralBlockedTraceKernelGameAt g).outcomeKernel β)
          (fun trace =>
            (pmfBehavioralBlockedTraceKernelGameAt g).utility trace who) := rfl
    _ =
        Math.Probability.expect (PMF.map projectTrace run)
          (fun trace =>
            (pmfBehavioralBlockedTraceKernelGameAt g).utility trace who) := by
          rw [htrace]
          rfl
    _ =
        Math.Probability.expect (PMF.map projectOutcome run)
          (fun outcome => (pmfBehavioralKernelGameAt g).utility outcome who) := by
          exact expect_eq_of_projected_kernel run projectTrace projectOutcome
            (pmfBehavioralBlockedTraceKernelGameAt g).utility
            (pmfBehavioralKernelGameAt g).utility who (fun _ => rfl)
    _ = (pmfBehavioralKernelGameAt g).eu β who := by
          rw [← hpublic]
          rfl

/-- Pure strategic-form play and blocked-trace play induce the same joint
utility distribution. -/
noncomputable def pureKernelGameAt.blockedTraceBisimulation
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame.Bisimulation
      (pureKernelGameAt g) (pureBlockedTraceKernelGameAt g) where
  stratEquiv := fun _ => Equiv.refl _
  udist_preserved := by
    intro π
    change
      ((pureBlockedTraceKernelGameAt g).outcomeKernel π).bind
          (fun trace =>
            PMF.pure ((pureBlockedTraceKernelGameAt g).utility trace)) =
        ((pureKernelGameAt g).outcomeKernel π).bind
          (fun outcome =>
            PMF.pure ((pureKernelGameAt g).utility outcome))
    rw [← pureBlockedTraceKernelGameAt_outcomeKernel_map_outcome g π]
    exact (PMF.bind_map
      ((pureBlockedTraceKernelGameAt g).outcomeKernel π)
      (syntaxBlockedTraceOutcome g)
      (fun outcome =>
        PMF.pure ((pureKernelGameAt g).utility outcome))).symm

/-- Pure strategic-form play and blocked-trace play are EU-preserving
bisimilar kernel games. -/
noncomputable def pureKernelGameAt.blockedTraceEUBisimulation
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame.EUGameIsomorphism
      (pureKernelGameAt g) (pureBlockedTraceKernelGameAt g) where
  toGameIsomorphism := pureKernelGameAt.blockedTraceBisimulation g
  eu_preserved := by
    intro π who
    exact pureBlockedTraceKernelGameAt_eu_eq g π who

/-- PMF behavioral strategic-form play and blocked-trace play induce the same
joint utility distribution. -/
noncomputable def pmfBehavioralKernelGameAt.blockedTraceBisimulation
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame.Bisimulation
      (pmfBehavioralKernelGameAt g)
      (pmfBehavioralBlockedTraceKernelGameAt g) where
  stratEquiv := fun _ => Equiv.refl _
  udist_preserved := by
    intro β
    change
      ((pmfBehavioralBlockedTraceKernelGameAt g).outcomeKernel β).bind
          (fun trace =>
            PMF.pure ((pmfBehavioralBlockedTraceKernelGameAt g).utility trace)) =
        ((pmfBehavioralKernelGameAt g).outcomeKernel β).bind
          (fun outcome =>
            PMF.pure ((pmfBehavioralKernelGameAt g).utility outcome))
    rw [← pmfBehavioralBlockedTraceKernelGameAt_outcomeKernel_map_outcome g β]
    exact (PMF.bind_map
      ((pmfBehavioralBlockedTraceKernelGameAt g).outcomeKernel β)
      (syntaxBlockedTraceOutcome g)
      (fun outcome =>
        PMF.pure ((pmfBehavioralKernelGameAt g).utility outcome))).symm

/-- PMF behavioral strategic-form play and blocked-trace play are
EU-preserving bisimilar kernel games. -/
noncomputable def pmfBehavioralKernelGameAt.blockedTraceEUBisimulation
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame.EUGameIsomorphism
      (pmfBehavioralKernelGameAt g)
      (pmfBehavioralBlockedTraceKernelGameAt g) where
  toGameIsomorphism :=
    pmfBehavioralKernelGameAt.blockedTraceBisimulation g
  eu_preserved := by
    intro β who
    exact pmfBehavioralBlockedTraceKernelGameAt_eu_eq g β who

end Vegas
