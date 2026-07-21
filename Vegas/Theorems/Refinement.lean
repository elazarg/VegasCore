import Vegas.Machine.Refinement
import Vegas.Machine.RefinementKernelGame
import Vegas.Machine.Audited
import Vegas.Machine.MessageInFlight
import Vegas.Runtime.CodecMachine
import Vegas.Runtime.TraceAdequacy
import Vegas.Frontier.SourceAdequacy
import GameTheory.Concepts.Transport.Corners
import GameTheory.Concepts.Correlation.CorrelatedNashMixed
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
            exact hspec)) := by
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
            exact hspec)) := by
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
          exact hspec)
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
            exact hspec)) at hproject
  have hout :
      R.projectOutcome implOutcome =
        sourceOutcomeAtTerminal program (R.projectState state)
          (by
            have hspec :
                (PrimitiveMachine (compile program)).terminal
                  (R.projectState state) :=
              R.terminal_project hterminal
            exact hspec) :=
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
              exact hspec))
          player := by
          rw [hout]
    _ =
        (sourceOutcomeAtTerminal program (R.projectState state)
          (by
            have hspec :
                (PrimitiveMachine (compile program)).terminal
                  (R.projectState state) :=
              R.terminal_project hterminal
            exact hspec)
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
            exact hspec)) :=
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
          exact hspec)
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

end WFProgram

end Vegas
