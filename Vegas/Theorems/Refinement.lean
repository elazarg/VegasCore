import Vegas.Machine.Refinement
import Vegas.Machine.RefinementKernelGame
import Vegas.Machine.Audited
import Vegas.Frontier.SourceAdequacy
import Vegas.Presentation.FOSG.FromCore
import GameTheory.Concepts.CorrelatedNashMixed
import Math.ProbabilityMassFunction

/-!
# Runtime refinement facts

The refinement layer is runtime-general.  It relates implementation machines
to specification machines by state/event projection, observation projection,
and payoff-preserving outcome projection.
-/

namespace Vegas

namespace Machine

namespace StochasticRefinement

open GameTheory

variable {Player : Type} {Impl Spec : Machine Player}

/-- A concrete implementation step labelled by a projected external event has
the same projected transition kernel as the specification step. -/
theorem external_step_kernel_project
    (R : StochasticRefinement Impl Spec)
    {event : Impl.Event} {specEvent : Spec.Event}
    {source : Impl.State}
    (hlabel : R.projectEvent? event = some specEvent) :
    PMF.map R.projectState (Impl.step event source) =
      Spec.step specEvent (R.projectState source) :=
  R.projected_step_eq_spec_step hlabel

/-- A concrete implementation step whose event projects to no specification
event is semantically administrative: it stutters after state projection. -/
theorem administrative_step_kernel_project
    (R : StochasticRefinement Impl Spec)
    {event : Impl.Event} {source : Impl.State}
    (hlabel : R.projectEvent? event = none) :
    PMF.map R.projectState (Impl.step event source) =
      PMF.pure (R.projectState source) :=
  R.projected_step_eq_pure_of_internal hlabel

/-- Compatible event-batch laws preserve bounded trace distributions after
projecting implementation traces to specification traces. -/
theorem compatible_laws_trace_distribution_project
    (R : StochasticRefinement Impl Spec)
    (lawSpec : Spec.EventBatchLaw) (lawImpl : Impl.EventBatchLaw)
    (compat : R.EventBatchLawCompatible lawImpl lawSpec)
    (horizon : Nat) (trace : Impl.EventBatchTrace) :
    PMF.map R.projectEventBatchTrace
        (Impl.eventBatchTraceDistFrom lawImpl horizon trace) =
      Spec.eventBatchTraceDistFrom lawSpec horizon
        (R.projectEventBatchTrace trace) :=
  R.eventBatchTraceDist_project_eq lawSpec lawImpl compat horizon trace

/-- Compatible event-batch laws preserve the payoff-vector distribution induced
by option-valued machine outcomes and an explicit cutoff policy. -/
theorem compatible_laws_utility_distribution_project
    (R : StochasticRefinement Impl Spec)
    (lawSpec : Spec.EventBatchLaw) (lawImpl : Impl.EventBatchLaw)
    (compat : R.EventBatchLawCompatible lawImpl lawSpec)
    (cutoff : Payoff Player)
    (horizon : Nat) (trace : Impl.EventBatchTrace) :
    PMF.map
        (fun implTrace =>
          RoundView.optionOutcomeUtility Impl cutoff
            (Impl.outcome implTrace.2))
        (Impl.eventBatchTraceDistFrom lawImpl horizon trace) =
      PMF.map
        (fun specTrace =>
          RoundView.optionOutcomeUtility Spec cutoff
            (Spec.outcome specTrace.2))
        (Spec.eventBatchTraceDistFrom lawSpec horizon
          (R.projectEventBatchTrace trace)) :=
  R.eventBatchOptionUtilityDist_project_eq lawSpec lawImpl compat cutoff
    horizon trace

/-- A bounded, payoff-preserving stochastic refinement pulls Nash equilibria of
the specification trace game back to compatible implementation trace games. -/
theorem bounded_trace_game_nash_pullback
    [DecidableEq Player]
    (R : StochasticRefinement Impl Spec)
    {Strategy : Player → Type}
    {specFamily : Spec.EventBatchLawFamily Strategy}
    (lift : R.EventBatchLawFamilyLift Strategy specFamily)
    (cutoff : Payoff Player) (horizon : Nat)
    {CImpl CSpec : Player → ℝ}
    (hbdImpl :
      ∀ player trace,
        |eventBatchTraceUtility Impl cutoff trace player| ≤ CImpl player)
    (hbdSpec :
      ∀ player trace,
        |eventBatchTraceUtility Spec cutoff trace player| ≤ CSpec player)
    {profile : ∀ player, Strategy player}
    (hNash :
      (eventBatchTraceKernelGame Spec Strategy specFamily cutoff horizon)
        |>.IsNash profile) :
    (eventBatchTraceKernelGame Impl Strategy lift.impl cutoff horizon)
      |>.IsNash profile :=
  R.eventBatchTraceKernelGame_nash_pullback_of_bounded
    lift cutoff horizon hbdImpl hbdSpec hNash

end StochasticRefinement

end Machine

namespace ToEventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr}

/-- A terminal implementation state of a runtime refining a compiled
primitive machine projects to the source payoff outcome of the checked Vegas
program. -/
theorem runtime_refinement_projected_terminal_outcome_eq_source
    {Impl : Machine Player}
    (program : GraphProgram Player L)
    (R :
      Machine.StochasticRefinement Impl
        (PrimitiveMachine (compile program)))
    {state : Impl.State}
    (hterminal : Impl.terminal state) :
    (PrimitiveMachine (compile program)).outcome (R.projectState state) =
      some
        (sourceOutcomeAtTerminal program (R.projectState state)
          (by
            have hspec :
                (PrimitiveMachine (compile program)).terminal
                  (R.projectState state) :=
              R.terminal_project hterminal
            simpa [PrimitiveMachine, primitiveMachineSpec] using hspec)) := by
  exact
    compile_primitiveMachine_outcome_eq_sourceAtTerminal
      program (R.projectState state)
      (R.terminal_project hterminal)

/-- The projected terminal outcome of a refining runtime is the source payoff
outcome of the compiled Vegas program. -/
theorem runtime_refinement_terminal_outcome_project_eq_source
    {Impl : Machine Player}
    (program : GraphProgram Player L)
    (R :
      Machine.StochasticRefinement Impl
        (PrimitiveMachine (compile program)))
    {state : Impl.State}
    (hterminal : Impl.terminal state) :
    Option.map R.projectOutcome (Impl.outcome state) =
      some
        (sourceOutcomeAtTerminal program (R.projectState state)
          (by
            have hspec :
                (PrimitiveMachine (compile program)).terminal
                  (R.projectState state) :=
              R.terminal_project hterminal
            simpa [PrimitiveMachine, primitiveMachineSpec] using hspec)) := by
  rw [R.outcome_project state]
  exact runtime_refinement_projected_terminal_outcome_eq_source
    program R hterminal

/-- If a refining implementation exposes a concrete terminal outcome, its
utility agrees with the source payoff projection after the runtime's outcome
projection. -/
theorem runtime_refinement_terminal_utility_eq_source
    {Impl : Machine Player}
    (program : GraphProgram Player L)
    (R :
      Machine.StochasticRefinement Impl
        (PrimitiveMachine (compile program)))
    {state : Impl.State} {implOutcome : Impl.Outcome}
    (hterminal : Impl.terminal state)
    (houtcome : Impl.outcome state = some implOutcome)
    (player : Player) :
    Impl.utility implOutcome player =
      (sourceOutcomeAtTerminal program (R.projectState state)
        (by
          have hspec :
              (PrimitiveMachine (compile program)).terminal
                (R.projectState state) :=
            R.terminal_project hterminal
          simpa [PrimitiveMachine, primitiveMachineSpec] using hspec)
        player : ℝ) := by
  have hproject :=
    runtime_refinement_terminal_outcome_project_eq_source
      program R hterminal
  rw [houtcome] at hproject
  change some (R.projectOutcome implOutcome) =
      some
        (sourceOutcomeAtTerminal program (R.projectState state)
          (by
            have hspec :
                (PrimitiveMachine (compile program)).terminal
                  (R.projectState state) :=
              R.terminal_project hterminal
            simpa [PrimitiveMachine, primitiveMachineSpec] using hspec)) at hproject
  have hout :
      R.projectOutcome implOutcome =
        sourceOutcomeAtTerminal program (R.projectState state)
          (by
            have hspec :
                (PrimitiveMachine (compile program)).terminal
                  (R.projectState state) :=
              R.terminal_project hterminal
            simpa [PrimitiveMachine, primitiveMachineSpec] using hspec) :=
    Option.some.inj hproject
  calc
    Impl.utility implOutcome player =
        (PrimitiveMachine (compile program)).utility
          (R.projectOutcome implOutcome) player := by
          exact (R.utility_project implOutcome player).symm
    _ =
        (PrimitiveMachine (compile program)).utility
          (sourceOutcomeAtTerminal program (R.projectState state)
            (by
              have hspec :
                  (PrimitiveMachine (compile program)).terminal
                    (R.projectState state) :=
                R.terminal_project hterminal
              simpa [PrimitiveMachine, primitiveMachineSpec] using hspec))
          player := by
          rw [hout]
    _ =
        (sourceOutcomeAtTerminal program (R.projectState state)
          (by
            have hspec :
                (PrimitiveMachine (compile program)).terminal
                  (R.projectState state) :=
              R.terminal_project hterminal
            simpa [PrimitiveMachine, primitiveMachineSpec] using hspec)
          player : ℝ) := by
          rfl

/-- Under a compatible runtime event-batch law, projecting concrete runtime
outcomes gives the same partial outcome distribution as projecting the
compiled Vegas source payoff over the specification traces. -/
theorem runtime_refinement_source_outcome_distribution_project
    {Impl : Machine Player}
    (program : GraphProgram Player L)
    (R :
      Machine.StochasticRefinement Impl
        (PrimitiveMachine (compile program)))
    (lawSpec : (PrimitiveMachine (compile program)).EventBatchLaw)
    (lawImpl : Impl.EventBatchLaw)
    (compat : R.EventBatchLawCompatible lawImpl lawSpec)
    (horizon : Nat) (trace : Impl.EventBatchTrace) :
    PMF.map
        (fun implTrace =>
          Option.map R.projectOutcome (Impl.outcome implTrace.2))
        (Impl.eventBatchTraceDistFrom lawImpl horizon trace) =
      PMF.map
        (sourceOutcomeOptionAtTrace program)
        ((PrimitiveMachine (compile program)).eventBatchTraceDistFrom
          lawSpec horizon (R.projectEventBatchTrace trace)) := by
  have houtcome :=
    R.eventBatchOutcomeDist_project_eq lawSpec lawImpl compat
      horizon trace
  rw [houtcome]
  congr 1
  funext specTrace
  exact compile_primitiveMachine_outcome_eq_sourceTrace program specTrace

/-- Compatible runtime scheduling laws preserve the source payoff-vector
distribution induced by bounded event-batch traces, with the supplied cutoff
used only for traces that stop before terminality. -/
theorem runtime_refinement_source_utility_distribution_project
    {Impl : Machine Player}
    (program : GraphProgram Player L)
    (R :
      Machine.StochasticRefinement Impl
        (PrimitiveMachine (compile program)))
    (lawSpec : (PrimitiveMachine (compile program)).EventBatchLaw)
    (lawImpl : Impl.EventBatchLaw)
    (compat : R.EventBatchLawCompatible lawImpl lawSpec)
    (cutoff : GameTheory.Payoff Player)
    (horizon : Nat) (trace : Impl.EventBatchTrace) :
    PMF.map
        (fun implTrace =>
          Machine.RoundView.optionOutcomeUtility Impl cutoff
            (Impl.outcome implTrace.2))
        (Impl.eventBatchTraceDistFrom lawImpl horizon trace) =
      PMF.map
        (fun specTrace =>
          Machine.RoundView.optionOutcomeUtility
            (PrimitiveMachine (compile program)) cutoff
            (sourceOutcomeOptionAtTrace program specTrace))
        ((PrimitiveMachine (compile program)).eventBatchTraceDistFrom
          lawSpec horizon (R.projectEventBatchTrace trace)) := by
  have hutility :=
    R.eventBatchOptionUtilityDist_project_eq lawSpec lawImpl compat
      cutoff horizon trace
  rw [hutility]
  congr 1
  funext specTrace
  rw [compile_primitiveMachine_outcome_eq_sourceTrace program specTrace]

end ToEventGraph

namespace WFProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-! ## Checked-program runtime refinement surface -/

/-- For a runtime refining the checked program's primitive compiled machine,
projected terminal runtime outcomes are exactly the checked source payoff
projection. -/
theorem runtimeRefinement_terminalOutcome_project_eq_source
    {Impl : Machine Player}
    (program : WFProgram Player L)
    (R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core)))
    {state : Impl.State}
    (hterminal : Impl.terminal state) :
    Option.map R.projectOutcome (Impl.outcome state) =
      some
        (ToEventGraph.sourceOutcomeAtTerminal program.core
          (R.projectState state)
          (by
            have hspec :
                (ToEventGraph.PrimitiveMachine
                    (ToEventGraph.compile program.core)).terminal
                  (R.projectState state) :=
              R.terminal_project hterminal
            simpa [ToEventGraph.PrimitiveMachine,
              ToEventGraph.primitiveMachineSpec] using hspec)) :=
  ToEventGraph.runtime_refinement_terminal_outcome_project_eq_source
    program.core R hterminal

/-- If a refining runtime exposes a concrete terminal outcome, its utility is
the checked source payoff after projection. -/
theorem runtimeRefinement_terminalUtility_eq_source
    {Impl : Machine Player}
    (program : WFProgram Player L)
    (R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core)))
    {state : Impl.State} {implOutcome : Impl.Outcome}
    (hterminal : Impl.terminal state)
    (houtcome : Impl.outcome state = some implOutcome)
    (player : Player) :
    Impl.utility implOutcome player =
      (ToEventGraph.sourceOutcomeAtTerminal program.core
        (R.projectState state)
        (by
          have hspec :
              (ToEventGraph.PrimitiveMachine
                  (ToEventGraph.compile program.core)).terminal
                (R.projectState state) :=
            R.terminal_project hterminal
          simpa [ToEventGraph.PrimitiveMachine,
            ToEventGraph.primitiveMachineSpec] using hspec)
        player : ℝ) :=
  ToEventGraph.runtime_refinement_terminal_utility_eq_source
    program.core R hterminal houtcome player

/-- Compatible runtime event-batch laws preserve the checked program's partial
source-outcome distribution after projection. -/
theorem runtimeRefinement_sourceOutcomeDistribution_project
    {Impl : Machine Player}
    (program : WFProgram Player L)
    (R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core)))
    (lawSpec :
      (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).EventBatchLaw)
    (lawImpl : Impl.EventBatchLaw)
    (compat : R.EventBatchLawCompatible lawImpl lawSpec)
    (horizon : Nat) (trace : Impl.EventBatchTrace) :
    PMF.map
        (fun implTrace =>
          Option.map R.projectOutcome (Impl.outcome implTrace.2))
        (Impl.eventBatchTraceDistFrom lawImpl horizon trace) =
      PMF.map
        (ToEventGraph.sourceOutcomeOptionAtTrace program.core)
        ((ToEventGraph.PrimitiveMachine
            (ToEventGraph.compile program.core)).eventBatchTraceDistFrom
          lawSpec horizon (R.projectEventBatchTrace trace)) :=
  ToEventGraph.runtime_refinement_source_outcome_distribution_project
    program.core R lawSpec lawImpl compat horizon trace

/-- Compatible runtime event-batch laws preserve the checked program's payoff
distribution, with the supplied cutoff used only for bounded nonterminal
traces. -/
theorem runtimeRefinement_sourceUtilityDistribution_project
    {Impl : Machine Player}
    (program : WFProgram Player L)
    (R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core)))
    (lawSpec :
      (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).EventBatchLaw)
    (lawImpl : Impl.EventBatchLaw)
    (compat : R.EventBatchLawCompatible lawImpl lawSpec)
    (cutoff : GameTheory.Payoff Player)
    (horizon : Nat) (trace : Impl.EventBatchTrace) :
    PMF.map
        (fun implTrace =>
          Machine.RoundView.optionOutcomeUtility Impl cutoff
            (Impl.outcome implTrace.2))
        (Impl.eventBatchTraceDistFrom lawImpl horizon trace) =
      PMF.map
        (fun specTrace =>
          Machine.RoundView.optionOutcomeUtility
            (ToEventGraph.PrimitiveMachine
              (ToEventGraph.compile program.core)) cutoff
            (ToEventGraph.sourceOutcomeOptionAtTrace program.core specTrace))
        ((ToEventGraph.PrimitiveMachine
            (ToEventGraph.compile program.core)).eventBatchTraceDistFrom
          lawSpec horizon (R.projectEventBatchTrace trace)) :=
  ToEventGraph.runtime_refinement_source_utility_distribution_project
    program.core R lawSpec lawImpl compat cutoff horizon trace

section Strategic

variable [Fintype Player]

/-- Primitive compiled machine used as the specification runtime for a checked
program. -/
noncomputable abbrev PrimitiveSpecMachine
    (program : WFProgram Player L) :=
  ToEventGraph.PrimitiveMachine (ToEventGraph.compile program.core)

/-- Canonical primitive event-batch trace distribution extracted from the
checked program's behavioral frontier run. -/
noncomputable def behavioralFrontierEventBatchTraceKernel
    (program : WFProgram Player L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    PMF
      ((ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).EventBatchTrace) :=
  PMF.map
    ((program.frontierSemantics.behavioral.view).boundedHistoryTrace
      program.frontierSemantics.horizon)
    (program.frontierSemantics.behavioralHistoryKernel profile)

/-- Primitive event-batch trace distribution induced by a pure frontier
profile through its degenerate behavioral realization. -/
noncomputable def pureFrontierEventBatchTraceKernel
    (program : WFProgram Player L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) :
    PMF
      ((ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).EventBatchTrace) :=
  behavioralFrontierEventBatchTraceKernel program
    ((program.frontierSemantics.behavioral.view).legalPureToBehavioral
      program.frontierSemantics.horizon profile)

/-- Primitive event-batch trace distribution induced by a product mixed-pure
frontier profile through the canonical Kuhn behavioral realization. -/
noncomputable def mixedPureFrontierEventBatchTraceKernel
    (program : WFProgram Player L) [FiniteDomains program]
    (profile : program.MixedPureFrontierProfile) :
    PMF
      ((ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).EventBatchTrace) :=
  behavioralFrontierEventBatchTraceKernel program
    (program.mixedPureToBehavioralFrontierProfile profile)

/-- The canonical behavioral frontier primitive-trace kernel has the same
joint utility distribution as the checked behavioral frontier game. -/
theorem behavioralFrontierEventBatchTraceKernel_udist
    (program : WFProgram Player L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    (behavioralFrontierEventBatchTraceKernel program profile).bind
        (fun trace =>
          PMF.pure
            (Machine.eventBatchTraceUtility
              (ToEventGraph.PrimitiveMachine
                (ToEventGraph.compile program.core))
              (fun _ => 0) trace)) =
      program.behavioralFrontierGame.udist profile := by
  classical
  let M :=
    ToEventGraph.PrimitiveMachine
      (ToEventGraph.compile program.core)
  let semantics := program.frontierSemantics
  change
    (PMF.map
        ((semantics.behavioral.view).boundedHistoryTrace
          semantics.horizon)
        (semantics.behavioralHistoryKernel profile)).bind
      (fun trace =>
        PMF.pure (Machine.eventBatchTraceUtility M (fun _ => 0) trace)) =
      program.behavioralFrontierGame.udist profile
  rw [PMF.bind_map]
  change
    (semantics.behavioralHistoryKernel profile).bind
      (fun history : semantics.BehavioralHistory =>
        PMF.pure
          (Machine.eventBatchTraceUtility M (fun _ => 0)
            ((semantics.behavioral.view).boundedHistoryTrace
              semantics.horizon history))) =
      program.behavioralFrontierGame.udist profile
  change
    PMF.map semantics.behavioralHistoryUtility
        (semantics.behavioralHistoryKernel profile) =
      program.behavioralFrontierGame.udist profile
  change semantics.behavioralHistoryKernelGame.udist profile =
      program.behavioralFrontierGame.udist profile
  exact semantics.behavioralHistoryKernelGame_udist profile

/-- The pure frontier primitive-trace kernel has the same joint utility
distribution as the checked pure frontier game. -/
theorem pureFrontierEventBatchTraceKernel_udist
    (program : WFProgram Player L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) :
    (pureFrontierEventBatchTraceKernel program profile).bind
        (fun trace =>
          PMF.pure
            (Machine.eventBatchTraceUtility
              (ToEventGraph.PrimitiveMachine
                (ToEventGraph.compile program.core))
              (fun _ => 0) trace)) =
      program.pureFrontierGame.udist profile := by
  simpa [pureFrontierEventBatchTraceKernel] using
    (behavioralFrontierEventBatchTraceKernel_udist program
        ((program.frontierSemantics.behavioral.view).legalPureToBehavioral
          program.frontierSemantics.horizon profile)).trans
      (program.pureToBehavioralFrontierUdist profile)

/-- The product mixed-pure frontier primitive-trace kernel has the same joint
utility distribution as the checked product mixed-pure frontier game. -/
theorem mixedPureFrontierEventBatchTraceKernel_udist
    (program : WFProgram Player L) [FiniteDomains program]
    (profile : program.MixedPureFrontierProfile) :
    (mixedPureFrontierEventBatchTraceKernel program profile).bind
        (fun trace =>
          PMF.pure
            (Machine.eventBatchTraceUtility
              (ToEventGraph.PrimitiveMachine
                (ToEventGraph.compile program.core))
              (fun _ => 0) trace)) =
      program.mixedPureFrontierGame.udist profile := by
  have hbehavioral :
      program.behavioralFrontierGame.udist
          (program.mixedPureToBehavioralFrontierProfile profile) =
        program.mixedPureFrontierGame.udist profile := by
    change
      (program.behavioralFrontierGame.outcomeKernel
          (program.mixedPureToBehavioralFrontierProfile profile)).bind
          (fun outcome =>
            PMF.pure
              (program.behavioralFrontierGame.utility outcome)) =
        (program.mixedPureFrontierGame.outcomeKernel profile).bind
          (fun outcome =>
            PMF.pure
              (program.mixedPureFrontierGame.utility outcome))
    rw [program.mixedPureToBehavioralFrontierProfile_outcomeKernel profile]
    rfl
  simpa [mixedPureFrontierEventBatchTraceKernel] using
    (behavioralFrontierEventBatchTraceKernel_udist program
        (program.mixedPureToBehavioralFrontierProfile profile)).trans
      hbehavioral

/-- A strategy-indexed game surface realized by primitive traces.

The surface specifies the strategy-indexed game to preserve and the canonical
primitive-trace kernel that realizes that game on the compiled specification
machine. Behavioral, pure, and product mixed-pure frontier play are canonical
instances, but the abstraction itself is exactly trace adequacy for a game
surface. -/
structure TraceGameSurface
    (program : WFProgram Player L) [FiniteDomains program] where
  game : GameTheory.KernelGame Player
  traceKernel :
    (∀ player, game.Strategy player) →
      PMF
        ((ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core)).EventBatchTrace)
  traceKernel_udist :
    ∀ profile,
      (traceKernel profile).bind
          (fun trace =>
            PMF.pure
              (Machine.eventBatchTraceUtility
                (ToEventGraph.PrimitiveMachine
                  (ToEventGraph.compile program.core))
                (fun _ => 0) trace)) =
        game.udist profile

/-- Payoff-vector law induced by a distribution over strategy profiles.

This is the utility-distribution view of a correlated profile law; it is the
right object for comparing trace/runtime presentations when the outcome
carriers differ but utilities agree. -/
noncomputable def correlatedUtilityLaw
    (G : GameTheory.KernelGame Player) (profileLaw : PMF G.Profile) :
    PMF (GameTheory.Payoff Player) :=
  profileLaw.bind G.udist

/-- Behavioral frontier play as a primitive-trace game surface. -/
noncomputable def behavioralFrontierTraceSurface
    (program : WFProgram Player L) [FiniteDomains program] :
    TraceGameSurface program where
  game := program.behavioralFrontierGame
  traceKernel := behavioralFrontierEventBatchTraceKernel program
  traceKernel_udist := behavioralFrontierEventBatchTraceKernel_udist program

/-- Pure frontier play as a primitive-trace game surface. -/
noncomputable def pureFrontierTraceSurface
    (program : WFProgram Player L) [FiniteDomains program] :
    TraceGameSurface program where
  game := program.pureFrontierGame
  traceKernel := pureFrontierEventBatchTraceKernel program
  traceKernel_udist := pureFrontierEventBatchTraceKernel_udist program

/-- Product mixed-pure frontier play as a primitive-trace game surface. -/
noncomputable def mixedPureFrontierTraceSurface
    (program : WFProgram Player L) [FiniteDomains program] :
    TraceGameSurface program where
  game := program.mixedPureFrontierGame
  traceKernel := mixedPureFrontierEventBatchTraceKernel program
  traceKernel_udist := mixedPureFrontierEventBatchTraceKernel_udist program

/-- A specification-side event-batch law family whose primitive trace
distribution realizes a trace game surface. -/
structure TraceSpecEventBatchLaw
    (program : WFProgram Player L) [FiniteDomains program]
    (surface : TraceGameSurface program) where
  specLaw :
    (∀ player, surface.game.Strategy player) →
      (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).EventBatchLaw
  legal :
    ∀ profile,
      (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).IsLegalEventBatchLaw
        (specLaw profile)
  trace_eq :
    ∀ profile,
      (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).eventBatchTraceDist
        (specLaw profile) program.frontierSemantics.horizon =
        surface.traceKernel profile

namespace TraceSpecEventBatchLaw

variable {program : WFProgram Player L} [FiniteDomains program]
variable {surface : TraceGameSurface program}

/-- Forget a trace-adequate spec law to the generic profile-indexed law family
used by machine refinement. -/
noncomputable def toFamily
    (law : TraceSpecEventBatchLaw program surface) :
    (ToEventGraph.PrimitiveMachine
      (ToEventGraph.compile program.core)).EventBatchLawFamily
      surface.game.Strategy where
  law := law.specLaw
  legal := law.legal

/-- Primitive trace game induced by a trace-adequate frontier law. -/
noncomputable def traceGame
    (law : TraceSpecEventBatchLaw program surface) :
    GameTheory.KernelGame Player :=
  Machine.eventBatchTraceKernelGame
    (ToEventGraph.PrimitiveMachine
      (ToEventGraph.compile program.core))
    surface.game.Strategy law.toFamily (fun _ => 0)
    program.frontierSemantics.horizon

/-- The explicit spec law has the same joint utility distribution as its
frontier surface. -/
theorem traceGame_udist_surface
    (law : TraceSpecEventBatchLaw program surface)
    (profile : ∀ player, surface.game.Strategy player) :
    law.traceGame.udist profile =
      surface.game.udist profile := by
  change
    ((ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).eventBatchTraceDist
        (law.specLaw profile) program.frontierSemantics.horizon).bind
      (fun trace =>
        PMF.pure
          (Machine.eventBatchTraceUtility
            (ToEventGraph.PrimitiveMachine
              (ToEventGraph.compile program.core))
            (fun _ => 0) trace)) =
      surface.game.udist profile
  rw [law.trace_eq profile]
  exact surface.traceKernel_udist profile

end TraceSpecEventBatchLaw

/-- A runtime refinement plus trace-adequate specification and implementation
law families for one trace game surface.

The refinement itself only relates primitive machines.  The trace game surface
and spec law witness provide the game-facing obligation: running the
specification primitive machine under that law realizes the surface game.
Runtime backends then prove only compatibility of their
implementation law with this spec law. -/
structure RuntimeTraceAdequacy
    (program : WFProgram Player L) [FiniteDomains program]
    (surface : TraceGameSurface program)
    {Impl : Machine Player}
    (R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))) where
  spec : TraceSpecEventBatchLaw program surface
  impl : Impl.EventBatchLawFamily surface.game.Strategy
  compatible :
    ∀ profile,
      R.EventBatchLawCompatible
        (impl.law profile) (spec.specLaw profile)

namespace RuntimeTraceAdequacy

variable {program : WFProgram Player L} [FiniteDomains program]
variable {surface : TraceGameSurface program}
variable {Impl : Machine Player}
variable {R :
    Machine.StochasticRefinement Impl
    (ToEventGraph.PrimitiveMachine
      (ToEventGraph.compile program.core))}

/-- Identity runtime adequacy for a trace-adequate primitive specification
law. This is the canonical smoke-test bridge: no runtime behavior is added,
so compatibility is reflexive event-batch-law compatibility. -/
noncomputable def identity
    (law : TraceSpecEventBatchLaw program surface) :
    RuntimeTraceAdequacy program surface
      (Machine.StochasticRefinement.refl (PrimitiveSpecMachine program)) where
  spec := law
  impl := law.toFamily
  compatible := by
    intro profile
    exact
      Machine.StochasticRefinement.refl_eventBatchLawCompatible
        (PrimitiveSpecMachine program) (law.specLaw profile)

/-- Audited runtime adequacy for any trace-adequate primitive specification
law. The implementation runtime executes one administrative audit tick before
each specification event batch, and the audited refinement erases those ticks. -/
noncomputable def audited
    (law : TraceSpecEventBatchLaw program surface) :
    RuntimeTraceAdequacy program surface
      (Machine.audited.refinement (PrimitiveSpecMachine program)) where
  spec := law
  impl :=
    (Machine.audited.liftEventBatchLawFamily
      (PrimitiveSpecMachine program) law.toFamily).impl
  compatible := by
    intro profile
    exact
      (Machine.audited.liftEventBatchLawFamily
        (PrimitiveSpecMachine program) law.toFamily).compatible profile

/-- Generic refinement lift induced by the bridge's explicit spec and
implementation law families. -/
noncomputable def lift
    (bridge : RuntimeTraceAdequacy program surface R) :
    R.EventBatchLawFamilyLift surface.game.Strategy bridge.spec.toFamily where
  impl := bridge.impl
  compatible := bridge.compatible

variable {Mid Low : Machine Player}
variable {Rmid :
    Machine.StochasticRefinement Mid
    (ToEventGraph.PrimitiveMachine
      (ToEventGraph.compile program.core))}
variable {Rlow : Machine.StochasticRefinement Low Mid}

/-- The composed law-family lift induced by lowering a runtime bridge through
one more implementation layer. -/
noncomputable def lowerLift
    (bridge : RuntimeTraceAdequacy program surface Rmid)
    (lower :
      Rlow.EventBatchLawFamilyLift surface.game.Strategy bridge.impl) :
    (Rmid.compose Rlow).EventBatchLawFamilyLift surface.game.Strategy
      bridge.spec.toFamily :=
  Machine.StochasticRefinement.EventBatchLawFamilyLift.compose
    bridge.lift lower

/-- Lower an existing runtime adequacy bridge through one more implementation
layer. This is the tower-composition operation for runtime trace adequacy:
the lower law family implements the bridge's current implementation law
family, and refinement composition collapses both implementation layers back
to the same primitive specification machine. -/
noncomputable def lowerImpl
    (bridge : RuntimeTraceAdequacy program surface Rmid)
    (lower :
      Rlow.EventBatchLawFamilyLift surface.game.Strategy bridge.impl) :
    RuntimeTraceAdequacy program surface (Rmid.compose Rlow) where
  spec := bridge.spec
  impl := (lowerLift bridge lower).impl
  compatible := (lowerLift bridge lower).compatible

@[simp] theorem lowerLift_impl
    (bridge : RuntimeTraceAdequacy program surface Rmid)
    (lower :
      Rlow.EventBatchLawFamilyLift surface.game.Strategy bridge.impl) :
    (lowerLift bridge lower).impl = lower.impl :=
  rfl

@[simp] theorem lowerImpl_impl
    (bridge : RuntimeTraceAdequacy program surface Rmid)
    (lower :
      Rlow.EventBatchLawFamilyLift surface.game.Strategy bridge.impl) :
    (lowerImpl bridge lower).impl = lower.impl :=
  rfl

/-- Specification primitive trace game realized by the strategy law family. -/
noncomputable def specTraceGame
    (bridge : RuntimeTraceAdequacy program surface R) :
    GameTheory.KernelGame Player :=
  bridge.spec.traceGame

/-- Implementation primitive trace game realized by the lifted runtime law
family. -/
noncomputable def implTraceGame
    (bridge : RuntimeTraceAdequacy program surface R) :
    GameTheory.KernelGame Player :=
  Machine.eventBatchTraceKernelGame
    Impl surface.game.Strategy bridge.lift.impl
    (fun _ => 0) program.frontierSemantics.horizon

/-- The implementation trace game has the same joint utility distribution as
the surface game. -/
theorem implTraceGame_udist_surface
    (bridge : RuntimeTraceAdequacy program surface R)
    (profile : ∀ player, surface.game.Strategy player) :
    bridge.implTraceGame.udist profile =
      surface.game.udist profile := by
  have hproject :=
    (R.eventBatchTraceMorphism
      bridge.lift (fun _ => 0)
      program.frontierSemantics.horizon).udist_preserved profile
  exact
    hproject.symm.trans
      (bridge.spec.traceGame_udist_surface profile)

/-- Trace adequacy preserves the payoff-vector law induced by any correlated
distribution over the shared strategy-profile space. -/
theorem implTraceGame_correlatedUtilityLaw_surface
    (bridge : RuntimeTraceAdequacy program surface R)
    (profileLaw : PMF surface.game.Profile) :
    correlatedUtilityLaw bridge.implTraceGame profileLaw =
      correlatedUtilityLaw surface.game profileLaw := by
  unfold correlatedUtilityLaw
  exact
    Math.ProbabilityMassFunction.bind_congr_on_support
      profileLaw bridge.implTraceGame.udist surface.game.udist
      (fun profile _ => bridge.implTraceGame_udist_surface profile)

/- Expected utilities agree between a trace-adequate implementation law and
the frontier surface under bounded-utility hypotheses. -/
private theorem implTraceGame_eu_surface_of_bounded
    (bridge : RuntimeTraceAdequacy program surface R)
    {CImpl CFrontier : Player → ℝ}
    (hbdImpl :
      ∀ player trace,
        |Machine.eventBatchTraceUtility Impl (fun _ => 0) trace player| ≤
          CImpl player)
    (hbdFrontier :
      ∀ player outcome,
        |surface.game.utility outcome player| ≤ CFrontier player)
    (profile : ∀ player, surface.game.Strategy player) (player : Player) :
    bridge.implTraceGame.eu profile player =
      surface.game.eu profile player := by
  calc
    bridge.implTraceGame.eu profile player =
        Math.Probability.expect
          (bridge.implTraceGame.udist profile) (fun payoff => payoff player) := by
          exact
            (bridge.implTraceGame.expect_udist_eq_eu_of_bounded
              profile player (hbdImpl player)).symm
    _ =
        Math.Probability.expect
          (surface.game.udist profile) (fun payoff => payoff player) := by
          rw [bridge.implTraceGame_udist_surface profile]
    _ = surface.game.eu profile player := by
          exact
            surface.game.expect_udist_eq_eu_of_bounded
              profile player (hbdFrontier player)

/- Correlated expected utilities agree between a trace-adequate implementation
law and the frontier surface under bounded-utility hypotheses. -/
private theorem implTraceGame_correlatedEu_surface_of_bounded
    (bridge : RuntimeTraceAdequacy program surface R)
    {CImpl CFrontier : Player → ℝ}
    (hbdImpl :
      ∀ player trace,
        |Machine.eventBatchTraceUtility Impl (fun _ => 0) trace player| ≤
          CImpl player)
    (hbdFrontier :
      ∀ player outcome,
        |surface.game.utility outcome player| ≤ CFrontier player)
    (profileLaw : PMF surface.game.Profile) (player : Player) :
    bridge.implTraceGame.correlatedEu profileLaw player =
      surface.game.correlatedEu profileLaw player := by
  rw [bridge.implTraceGame.correlatedEu_eq_expect_eu_of_bounded
    profileLaw player (hbdImpl player)]
  rw [surface.game.correlatedEu_eq_expect_eu_of_bounded
    profileLaw player (hbdFrontier player)]
  exact
    Math.ProbabilityMassFunction.expect_congr_on_support
      profileLaw
      (fun profile => bridge.implTraceGame.eu profile player)
      (fun profile => surface.game.eu profile player)
      (fun profile _ =>
        bridge.implTraceGame_eu_surface_of_bounded
          hbdImpl hbdFrontier profile player)

/-- Correlated-equilibrium status is invariant between a trace-adequate
implementation trace game and the frontier surface when utilities are bounded
and the strategy-profile law is shared. -/
theorem implTraceGame_correlatedEq_iff_surface_correlatedEq_of_bounded
    (bridge : RuntimeTraceAdequacy program surface R)
    {CImpl CFrontier : Player → ℝ}
    (hbdImpl :
      ∀ player trace,
        |Machine.eventBatchTraceUtility Impl (fun _ => 0) trace player| ≤
          CImpl player)
    (hbdFrontier :
      ∀ player outcome,
        |surface.game.utility outcome player| ≤ CFrontier player)
    (profileLaw : PMF surface.game.Profile) :
    bridge.implTraceGame.IsCorrelatedEq profileLaw ↔
      surface.game.IsCorrelatedEq profileLaw := by
  constructor
  · intro hCE player dev
    calc
      surface.game.correlatedEu profileLaw player =
          bridge.implTraceGame.correlatedEu profileLaw player := by
            exact
              (bridge.implTraceGame_correlatedEu_surface_of_bounded
                hbdImpl hbdFrontier profileLaw player).symm
      _ ≥ bridge.implTraceGame.correlatedEu
            (bridge.implTraceGame.unilateralDeviationDistribution
              profileLaw player dev) player := hCE player dev
      _ = surface.game.correlatedEu
            (surface.game.unilateralDeviationDistribution
              profileLaw player dev) player := by
            simpa [GameTheory.KernelGame.unilateralDeviationDistribution,
              GameTheory.KernelGame.deviationDistribution,
              GameTheory.KernelGame.unilateralDeviation] using
              bridge.implTraceGame_correlatedEu_surface_of_bounded
                hbdImpl hbdFrontier
                (bridge.implTraceGame.unilateralDeviationDistribution
                  profileLaw player dev) player
  · intro hCE player dev
    calc
      bridge.implTraceGame.correlatedEu profileLaw player =
          surface.game.correlatedEu profileLaw player := by
            exact
              bridge.implTraceGame_correlatedEu_surface_of_bounded
                hbdImpl hbdFrontier profileLaw player
      _ ≥ surface.game.correlatedEu
            (surface.game.unilateralDeviationDistribution
              profileLaw player dev) player := hCE player dev
      _ = bridge.implTraceGame.correlatedEu
            (bridge.implTraceGame.unilateralDeviationDistribution
              profileLaw player dev) player := by
            simpa [GameTheory.KernelGame.unilateralDeviationDistribution,
              GameTheory.KernelGame.deviationDistribution,
              GameTheory.KernelGame.unilateralDeviation] using
              (bridge.implTraceGame_correlatedEu_surface_of_bounded
                hbdImpl hbdFrontier
                (bridge.implTraceGame.unilateralDeviationDistribution
                  profileLaw player dev) player).symm

/-- Coarse-correlated-equilibrium status is invariant between a trace-adequate
implementation trace game and the frontier surface when utilities are bounded
and the strategy-profile law is shared. -/
theorem implTraceGame_coarseCorrelatedEq_iff_surface_coarseCorrelatedEq_of_bounded
    (bridge : RuntimeTraceAdequacy program surface R)
    {CImpl CFrontier : Player → ℝ}
    (hbdImpl :
      ∀ player trace,
        |Machine.eventBatchTraceUtility Impl (fun _ => 0) trace player| ≤
          CImpl player)
    (hbdFrontier :
      ∀ player outcome,
        |surface.game.utility outcome player| ≤ CFrontier player)
    (profileLaw : PMF surface.game.Profile) :
    bridge.implTraceGame.IsCoarseCorrelatedEq profileLaw ↔
      surface.game.IsCoarseCorrelatedEq profileLaw := by
  constructor
  · intro hCCE player alternative
    calc
      surface.game.correlatedEu profileLaw player =
          bridge.implTraceGame.correlatedEu profileLaw player := by
            exact
              (bridge.implTraceGame_correlatedEu_surface_of_bounded
                hbdImpl hbdFrontier profileLaw player).symm
      _ ≥ bridge.implTraceGame.correlatedEu
            (bridge.implTraceGame.constantDeviationDistribution
              profileLaw player alternative) player := hCCE player alternative
      _ = surface.game.correlatedEu
            (surface.game.constantDeviationDistribution
              profileLaw player alternative) player := by
            simpa [GameTheory.KernelGame.constantDeviationDistribution,
              GameTheory.KernelGame.deviationDistribution,
              GameTheory.KernelGame.constantDeviation] using
              bridge.implTraceGame_correlatedEu_surface_of_bounded
                hbdImpl hbdFrontier
                (bridge.implTraceGame.constantDeviationDistribution
                  profileLaw player alternative) player
  · intro hCCE player alternative
    calc
      bridge.implTraceGame.correlatedEu profileLaw player =
          surface.game.correlatedEu profileLaw player := by
            exact
              bridge.implTraceGame_correlatedEu_surface_of_bounded
                hbdImpl hbdFrontier profileLaw player
      _ ≥ surface.game.correlatedEu
            (surface.game.constantDeviationDistribution
              profileLaw player alternative) player := hCCE player alternative
      _ = bridge.implTraceGame.correlatedEu
            (bridge.implTraceGame.constantDeviationDistribution
              profileLaw player alternative) player := by
            simpa [GameTheory.KernelGame.constantDeviationDistribution,
              GameTheory.KernelGame.deviationDistribution,
              GameTheory.KernelGame.constantDeviation] using
              (bridge.implTraceGame_correlatedEu_surface_of_bounded
                hbdImpl hbdFrontier
                (bridge.implTraceGame.constantDeviationDistribution
                  profileLaw player alternative) player).symm

/-- Expected utilities agree between a trace-adequate specification law and
the frontier surface under bounded-utility hypotheses. -/
theorem specTraceGame_eu_surface_of_bounded
    (bridge : RuntimeTraceAdequacy program surface R)
    {CSpec CFrontier : Player → ℝ}
    (hbdSpec :
      ∀ player trace,
        |Machine.eventBatchTraceUtility
            (ToEventGraph.PrimitiveMachine
              (ToEventGraph.compile program.core))
            (fun _ => 0) trace player| ≤ CSpec player)
    (hbdFrontier :
      ∀ player outcome,
        |surface.game.utility outcome player| ≤ CFrontier player)
    (profile : ∀ player, surface.game.Strategy player) (player : Player) :
    bridge.specTraceGame.eu profile player =
      surface.game.eu profile player := by
  calc
    bridge.specTraceGame.eu profile player =
        Math.Probability.expect
          (bridge.specTraceGame.udist profile) (fun payoff => payoff player) := by
          exact
            (bridge.specTraceGame.expect_udist_eq_eu_of_bounded
              profile player (hbdSpec player)).symm
    _ =
        Math.Probability.expect
          (surface.game.udist profile)
          (fun payoff => payoff player) := by
          change
            Math.Probability.expect
              (bridge.spec.traceGame.udist profile)
              (fun payoff => payoff player) =
            Math.Probability.expect
              (surface.game.udist profile)
              (fun payoff => payoff player)
          rw [bridge.spec.traceGame_udist_surface profile]
    _ = surface.game.eu profile player := by
          exact
            surface.game.expect_udist_eq_eu_of_bounded
              profile player (hbdFrontier player)

/-- Specification trace games adequate for a trace game surface inherit that
surface game's Nash equilibria. -/
theorem specTraceGame_nash_of_surface_nash
    (bridge : RuntimeTraceAdequacy program surface R)
    {CSpec CFrontier : Player → ℝ}
    (hbdSpec :
      ∀ player trace,
        |Machine.eventBatchTraceUtility
            (ToEventGraph.PrimitiveMachine
              (ToEventGraph.compile program.core))
            (fun _ => 0) trace player| ≤ CSpec player)
    (hbdFrontier :
      ∀ player outcome,
        |surface.game.utility outcome player| ≤ CFrontier player)
    {profile : ∀ player, surface.game.Strategy player}
    (hNash : surface.game.IsNash profile) :
    bridge.specTraceGame.IsNash profile := by
  intro player alternative
  have hfrontier := hNash player alternative
  calc
    bridge.specTraceGame.eu profile player =
        surface.game.eu profile player :=
      bridge.specTraceGame_eu_surface_of_bounded
        hbdSpec hbdFrontier profile player
    _ ≥ surface.game.eu
          (Function.update profile player alternative) player :=
      hfrontier
    _ = bridge.specTraceGame.eu
          (Function.update profile player alternative) player :=
      (bridge.specTraceGame_eu_surface_of_bounded
        hbdSpec hbdFrontier
        (Function.update profile player alternative) player).symm

/-- A runtime refinement whose strategy-indexed laws adequately realize a trace
game surface pulls surface Nash profiles back to the implementation trace game. -/
theorem implTraceGame_nash_of_surface_nash
    (bridge : RuntimeTraceAdequacy program surface R)
    {CImpl CSpec CFrontier : Player → ℝ}
    (hbdImpl :
      ∀ player trace,
        |Machine.eventBatchTraceUtility Impl (fun _ => 0) trace player| ≤
          CImpl player)
    (hbdSpec :
      ∀ player trace,
        |Machine.eventBatchTraceUtility
            (ToEventGraph.PrimitiveMachine
              (ToEventGraph.compile program.core))
            (fun _ => 0) trace player| ≤ CSpec player)
    (hbdFrontier :
      ∀ player outcome,
        |surface.game.utility outcome player| ≤ CFrontier player)
    {profile : ∀ player, surface.game.Strategy player}
    (hNash : surface.game.IsNash profile) :
    bridge.implTraceGame.IsNash profile := by
  simpa [implTraceGame, specTraceGame] using
    R.eventBatchTraceKernelGame_nash_pullback_of_bounded
      bridge.lift (fun _ => 0) program.frontierSemantics.horizon
      hbdImpl hbdSpec
      (bridge.specTraceGame_nash_of_surface_nash
        hbdSpec hbdFrontier hNash)

end RuntimeTraceAdequacy

end Strategic

end WFProgram

end Vegas
