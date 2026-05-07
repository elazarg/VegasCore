import GameTheory.Core.GameSimulation
import Vegas.Config
import Vegas.Protocol.ProgramEventGraph

/-!
# Strategic kernel games

This module exposes the canonical finite strategic forms of checked Vegas
programs.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Pure strategy carrier at the program's finite syntax horizon. -/
abbrev pureStrategyAt
    (g : WFProgram P L) (who : P) : Type :=
  (eventGraphFOSGView g).BoundedPureStrategy (syntaxSteps g.prog) who

/-- Pure profile carrier at the program's finite syntax horizon. -/
abbrev pureProfileAt
    (g : WFProgram P L) : Type :=
  (eventGraphFOSGView g).BoundedPureProfile (syntaxSteps g.prog)

/-- PMF behavioral strategy carrier at the program's finite syntax horizon. -/
abbrev behavioralStrategyPMFAt
    (g : WFProgram P L) (who : P) : Type :=
  (eventGraphFOSGView g).BoundedBehavioralStrategy (syntaxSteps g.prog) who

/-- PMF behavioral profile carrier at the program's finite syntax horizon. -/
abbrev behavioralProfilePMFAt
    (g : WFProgram P L) : Type :=
  (eventGraphFOSGView g).BoundedBehavioralProfile (syntaxSteps g.prog)

/-- Outcome kernel of the finite pure strategic form of a checked Vegas
program. -/
noncomputable def pureOutcomeKernelAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) : PMF (Outcome P) := by
  classical
  exact
    (eventGraphFOSGView g).boundedOutcomeFromPure
      (syntaxSteps g.prog) π (syntaxSteps g.prog)

/-- Outcome kernel of the finite PMF behavioral strategic form of a checked
Vegas program. -/
noncomputable def behavioralOutcomeKernelPMFAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) : PMF (Outcome P) := by
  classical
  exact
    (eventGraphFOSGView g).boundedOutcomeFromBehavioral
      (syntaxSteps g.prog) β (syntaxSteps g.prog)

/-- Pure strategic-form outcomes are machine-outcome projections of the
blocked primitive trace distribution induced by the finite event-graph FOSG
view. -/
theorem pureOutcomeKernelAt_eq_blockTraceDist
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) :
    pureOutcomeKernelAt g π =
      PMF.map
        (eventGraphTraceOutcome g)
        (eventGraphFOSGBlockTraceDistFrom g (syntaxSteps g.prog)
          (GameTheory.FOSG.legalPureToBehavioral
            ((eventGraphFOSGView g).toBoundedFOSG (syntaxSteps g.prog))
            π.extend)
          (syntaxSteps g.prog)
          (eventGraphInitialHistory g (syntaxSteps g.prog))) := by
  simp [pureOutcomeKernelAt,
    eventGraphFOSG_boundedOutcomeFromPure_eq_blockTraceDist]

/-- PMF behavioral strategic-form outcomes are machine-outcome projections of
the blocked primitive trace distribution induced by the finite event-graph
FOSG view. -/
theorem behavioralOutcomeKernelPMFAt_eq_blockTraceDist
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) :
    behavioralOutcomeKernelPMFAt g β =
      PMF.map
        (eventGraphTraceOutcome g)
        (eventGraphFOSGBlockTraceDistFrom g (syntaxSteps g.prog)
          β.extend
          (syntaxSteps g.prog)
          (eventGraphInitialHistory g (syntaxSteps g.prog))) := by
  simp [behavioralOutcomeKernelPMFAt,
    eventGraphFOSG_boundedOutcomeFromBehavioral_eq_blockTraceDist]

/-- Machine blocked trace outcomes induced by the bounded event-graph FOSG
view: the primitive event blocks executed so far, paired with the resulting
checkpoint state. -/
abbrev syntaxBlockedTraceAt
    (g : WFProgram P L) : Type :=
  List (List (eventGraphMachine g).Event) × (eventGraphMachine g).State

/-- Public outcome read from a blocked machine trace. -/
noncomputable def syntaxBlockedTraceOutcome
    (g : WFProgram P L) :
    syntaxBlockedTraceAt g → Outcome P :=
  fun trace => (eventGraphMachine g).outcome trace.2

/-- Utility read from a blocked machine trace through its public outcome. -/
noncomputable def syntaxBlockedTraceUtility
    (g : WFProgram P L) :
    syntaxBlockedTraceAt g → GameTheory.Payoff P :=
  fun trace who => ((syntaxBlockedTraceOutcome g trace) who : ℝ)

/-- Blocked primitive trace kernel induced by a pure profile. -/
noncomputable def pureBlockedTraceOutcomeKernelAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) : PMF (syntaxBlockedTraceAt g) :=
  eventGraphFOSGBlockTraceDistFrom g (syntaxSteps g.prog)
    (GameTheory.FOSG.legalPureToBehavioral
      ((eventGraphFOSGView g).toBoundedFOSG (syntaxSteps g.prog))
      π.extend)
    (syntaxSteps g.prog)
    (eventGraphInitialHistory g (syntaxSteps g.prog))

/-- Blocked primitive trace kernel induced by a PMF behavioral profile. -/
noncomputable def behavioralBlockedTraceOutcomeKernelPMFAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) : PMF (syntaxBlockedTraceAt g) :=
  eventGraphFOSGBlockTraceDistFrom g (syntaxSteps g.prog)
    β.extend
    (syntaxSteps g.prog)
    (eventGraphInitialHistory g (syntaxSteps g.prog))

/-- Finite pure strategic form whose outcomes are blocked primitive machine
traces rather than just terminal public outcomes. -/
noncomputable def pureBlockedTraceKernelGameAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame P where
  Strategy := pureStrategyAt g
  Outcome := syntaxBlockedTraceAt g
  utility := syntaxBlockedTraceUtility g
  outcomeKernel := pureBlockedTraceOutcomeKernelAt g

@[simp] theorem pureBlockedTraceKernelGameAt_Strategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pureBlockedTraceKernelGameAt g).Strategy = pureStrategyAt g := rfl

/-- Finite PMF behavioral strategic form whose outcomes are blocked primitive
machine traces rather than just terminal public outcomes. -/
noncomputable def pmfBehavioralBlockedTraceKernelGameAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame P where
  Strategy := behavioralStrategyPMFAt g
  Outcome := syntaxBlockedTraceAt g
  utility := syntaxBlockedTraceUtility g
  outcomeKernel := behavioralBlockedTraceOutcomeKernelPMFAt g

@[simp] theorem pmfBehavioralBlockedTraceKernelGameAt_Strategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pmfBehavioralBlockedTraceKernelGameAt g).Strategy =
      behavioralStrategyPMFAt g := rfl

/-- Finite pure strategic form of a checked Vegas program. -/
noncomputable def pureKernelGameAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame P where
  Strategy := pureStrategyAt g
  Outcome := Outcome P
  utility := fun o i => (o i : ℝ)
  outcomeKernel := pureOutcomeKernelAt g

@[simp] theorem pureKernelGameAt_Strategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pureKernelGameAt g).Strategy = pureStrategyAt g := rfl

@[simp] theorem pureKernelGameAt_outcomeKernel
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) :
    (pureKernelGameAt g).outcomeKernel π = pureOutcomeKernelAt g π := rfl

/-- Finite pure strategies for the public pure kernel game. -/
noncomputable instance pureKernelGameAt.instFintypeStrategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] (who : P) :
    Fintype ((pureKernelGameAt g).Strategy who) := by
  classical
  change Fintype (pureStrategyAt g who)
  dsimp [pureStrategyAt, Machine.FOSGView.BoundedPureStrategy]
  infer_instance

/-- Finite PMF behavioral strategic form of a checked Vegas program. -/
noncomputable def pmfBehavioralKernelGameAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame P where
  Strategy := behavioralStrategyPMFAt g
  Outcome := Outcome P
  utility := fun o i => (o i : ℝ)
  outcomeKernel := behavioralOutcomeKernelPMFAt g

@[simp] theorem pmfBehavioralKernelGameAt_Strategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pmfBehavioralKernelGameAt g).Strategy =
      behavioralStrategyPMFAt g := rfl

@[simp] theorem pmfBehavioralKernelGameAt_outcomeKernel
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) :
    (pmfBehavioralKernelGameAt g).outcomeKernel β =
      behavioralOutcomeKernelPMFAt g β := rfl

/-- Projecting pure blocked-trace outcomes to public outcomes gives the public
pure strategic-form outcome kernel. -/
theorem pureBlockedTraceKernelGameAt_outcomeKernel_map_outcome
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) :
    PMF.map (syntaxBlockedTraceOutcome g)
        ((pureBlockedTraceKernelGameAt g).outcomeKernel π) =
      (pureKernelGameAt g).outcomeKernel π := by
  simpa [pureBlockedTraceKernelGameAt, pureKernelGameAt,
    syntaxBlockedTraceOutcome] using
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
    syntaxBlockedTraceOutcome] using
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
  let G := (eventGraphFOSGView g).toBoundedFOSG horizon
  let σ := GameTheory.FOSG.legalPureToBehavioral G π.extend
  let start := GameTheory.FOSG.History.nil G
  let run := GameTheory.FOSG.History.runDistFrom G σ horizon start
  let projectTrace : G.History → syntaxBlockedTraceAt g :=
    fun h' => (eventGraphFOSGHistoryEventBlocks g horizon h',
      h'.lastState.state)
  let projectOutcome : G.History → Outcome P :=
    fun h' => (eventGraphMachine g).outcome h'.lastState.state
  have htrace :
      (pureBlockedTraceKernelGameAt g).outcomeKernel π =
        PMF.map projectTrace run := by
    have h :=
      eventGraphFOSG_runDistFrom_map_eventBlocks_state_eq_blockTraceDistFrom
        (g := g) (horizon := horizon) (σ := σ) (n := horizon)
        (h := start)
    simpa [pureBlockedTraceKernelGameAt, pureBlockedTraceOutcomeKernelAt,
      eventGraphInitialHistory, projectTrace, run, start, σ, G, horizon]
      using h.symm
  have hpublic :
      (pureKernelGameAt g).outcomeKernel π =
        PMF.map projectOutcome run := by
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
  let G := (eventGraphFOSGView g).toBoundedFOSG horizon
  let σ := β.extend
  let start := GameTheory.FOSG.History.nil G
  let run := GameTheory.FOSG.History.runDistFrom G σ horizon start
  let projectTrace : G.History → syntaxBlockedTraceAt g :=
    fun h' => (eventGraphFOSGHistoryEventBlocks g horizon h',
      h'.lastState.state)
  let projectOutcome : G.History → Outcome P :=
    fun h' => (eventGraphMachine g).outcome h'.lastState.state
  have htrace :
      (pmfBehavioralBlockedTraceKernelGameAt g).outcomeKernel β =
        PMF.map projectTrace run := by
    have h :=
      eventGraphFOSG_runDistFrom_map_eventBlocks_state_eq_blockTraceDistFrom
        (g := g) (horizon := horizon) (σ := σ) (n := horizon)
        (h := start)
    simpa [pmfBehavioralBlockedTraceKernelGameAt,
      behavioralBlockedTraceOutcomeKernelPMFAt,
      eventGraphInitialHistory, projectTrace, run, start, σ, G, horizon]
      using h.symm
  have hpublic :
      (pmfBehavioralKernelGameAt g).outcomeKernel β =
        PMF.map projectOutcome run := by
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
