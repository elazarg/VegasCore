import Vegas.Machine.Refinement
import GameTheory.Core.GameMorphism
import GameTheory.Concepts.SolutionConcepts

/-!
# Kernel games induced by machine refinements

This module turns a probability-preserving machine refinement into a
kernel-game morphism for bounded event-batch trace games.

The strategic surface is deliberately supplied as data: a profile selects a
history-dependent event-batch law for the specification and a compatible law
for the implementation. This keeps runtime refinement independent of any
particular scheduler or strategic presentation.
-/

namespace Vegas

open GameTheory

namespace Machine

variable {Player : Type}

/-- A profile-indexed family of event-batch laws for a machine. -/
structure EventBatchLawFamily
    (M : Machine Player) (Strategy : Player → Type) where
  law : (∀ player, Strategy player) → M.EventBatchLaw
  legal : ∀ profile, M.IsLegalEventBatchLaw (law profile)

namespace EventBatchLawFamily

variable {M : Machine Player} {Strategy : Player → Type}

/-- Law selected by a strategy profile. -/
abbrev lawAt
    (family : M.EventBatchLawFamily Strategy)
    (profile : ∀ player, Strategy player) : M.EventBatchLaw :=
  family.law profile

end EventBatchLawFamily

/-- Payoff vector read from the terminal state of an event-batch trace, with an
explicit cutoff payoff for bounded runs that stop before a machine outcome is
defined. -/
noncomputable def eventBatchTraceUtility
    (M : Machine Player) (cutoff : Payoff Player) :
    M.EventBatchTrace → Payoff Player :=
  fun trace => RoundView.optionOutcomeUtility M cutoff (M.outcome trace.2)

/-- Kernel game whose outcomes are full event-batch traces of a machine under
a profile-indexed law family. -/
noncomputable def eventBatchTraceKernelGame
    (M : Machine Player) (Strategy : Player → Type)
    (family : M.EventBatchLawFamily Strategy)
    (cutoff : Payoff Player) (horizon : Nat) :
    KernelGame Player where
  Strategy := Strategy
  Outcome := M.EventBatchTrace
  utility := eventBatchTraceUtility M cutoff
  outcomeKernel := fun profile =>
    M.eventBatchTraceDist (family.law profile) horizon

namespace StochasticRefinement

variable {Impl Spec : Machine Player}

/-- A profile-indexed lift of specification event-batch laws to implementation
event-batch laws through a stochastic refinement. -/
structure EventBatchLawFamilyLift
    (R : StochasticRefinement Impl Spec)
    (Strategy : Player → Type) where
  spec : Spec.EventBatchLawFamily Strategy
  impl : Impl.EventBatchLawFamily Strategy
  compatible :
    ∀ profile,
      R.EventBatchLawCompatible
        (impl.law profile) (spec.law profile)

namespace EventBatchLawFamilyLift

variable {Strategy : Player → Type}

/-- Identity lift for a law family on a machine. -/
def refl (M : Machine Player)
    (family : M.EventBatchLawFamily Strategy) :
    (StochasticRefinement.refl M).EventBatchLawFamilyLift Strategy where
  spec := family
  impl := family
  compatible := by
    intro profile
    exact StochasticRefinement.refl_eventBatchLawCompatible M
      (family.law profile)

end EventBatchLawFamilyLift

variable {Strategy : Player → Type}

/-- Projecting implementation event-batch traces gives the specification trace
distribution for compatible law families. -/
theorem eventBatchTraceKernelGame_projectTrace_eq
    (R : StochasticRefinement Impl Spec)
    (lift : R.EventBatchLawFamilyLift Strategy)
    (cutoff : Payoff Player) (horizon : Nat)
    (profile : ∀ player, Strategy player) :
    PMF.map R.projectEventBatchTrace
        ((eventBatchTraceKernelGame Impl Strategy lift.impl cutoff horizon)
          |>.outcomeKernel profile) =
      ((eventBatchTraceKernelGame Spec Strategy lift.spec cutoff horizon)
        |>.outcomeKernel profile) := by
  have h :=
    R.eventBatchTraceDist_project_eq
      (lift.spec.law profile) (lift.impl.law profile)
      (lift.compatible profile) horizon ([], Impl.init)
  simpa [eventBatchTraceKernelGame, Machine.eventBatchTraceDist,
    projectEventBatchTrace, R.init_project] using h

/-- Utility assigned to a projected implementation trace is exactly the
implementation trace utility. -/
theorem eventBatchTraceUtility_project
    (R : StochasticRefinement Impl Spec)
    (cutoff : Payoff Player) (trace : Impl.EventBatchTrace) :
    eventBatchTraceUtility Spec cutoff
        (R.projectEventBatchTrace trace) =
      eventBatchTraceUtility Impl cutoff trace := by
  unfold eventBatchTraceUtility
  change
    RoundView.optionOutcomeUtility Spec cutoff
        (Spec.outcome (R.projectState trace.2)) =
      RoundView.optionOutcomeUtility Impl cutoff (Impl.outcome trace.2)
  rw [← R.outcome_project trace.2]
  exact R.optionOutcomeUtility_project cutoff (Impl.outcome trace.2)

/-- Compatible event-batch law families induce a utility-distribution
preserving kernel-game morphism from implementation traces to specification
traces. -/
noncomputable def eventBatchTraceMorphism
    (R : StochasticRefinement Impl Spec)
    (lift : R.EventBatchLawFamilyLift Strategy)
    (cutoff : Payoff Player) (horizon : Nat) :
    KernelGame.Morphism
      (eventBatchTraceKernelGame Impl Strategy lift.impl cutoff horizon)
      (eventBatchTraceKernelGame Spec Strategy lift.spec cutoff horizon) :=
  KernelGame.Morphism.ofOutcomeEmbedding
    (fun _ strategy => strategy)
    R.projectEventBatchTrace
    (fun profile =>
      (R.eventBatchTraceKernelGame_projectTrace_eq
        lift cutoff horizon profile).symm)
    (fun trace => R.eventBatchTraceUtility_project cutoff trace)

/-- Bounded utility hypotheses upgrade the trace morphism to the
EU-preserving morphism needed for Nash transport. -/
noncomputable def eventBatchTraceEUMorphismOfBounded
    (R : StochasticRefinement Impl Spec)
    (lift : R.EventBatchLawFamilyLift Strategy)
    (cutoff : Payoff Player) (horizon : Nat)
    {CImpl CSpec : Player → ℝ}
    (hbdImpl :
      ∀ player trace,
        |eventBatchTraceUtility Impl cutoff trace player| ≤ CImpl player)
    (hbdSpec :
      ∀ player trace,
        |eventBatchTraceUtility Spec cutoff trace player| ≤ CSpec player) :
    KernelGame.EUMorphism
      (eventBatchTraceKernelGame Impl Strategy lift.impl cutoff horizon)
      (eventBatchTraceKernelGame Spec Strategy lift.spec cutoff horizon) :=
  (R.eventBatchTraceMorphism lift cutoff horizon)
    |>.toEUMorphismOfBounded hbdImpl hbdSpec

/-- Nash equilibria of the specification trace game pull back to compatible
implementation trace games under bounded payoff hypotheses. -/
theorem eventBatchTraceKernelGame_nash_pullback_of_bounded
    [DecidableEq Player]
    (R : StochasticRefinement Impl Spec)
    (lift : R.EventBatchLawFamilyLift Strategy)
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
      (eventBatchTraceKernelGame Spec Strategy lift.spec cutoff horizon)
        |>.IsNash profile) :
    (eventBatchTraceKernelGame Impl Strategy lift.impl cutoff horizon)
      |>.IsNash profile := by
  exact
    (R.eventBatchTraceEUMorphismOfBounded
      lift cutoff horizon hbdImpl hbdSpec).nash_of_nash hNash

end StochasticRefinement

end Machine

end Vegas
