/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.Refinement
import GameTheory.Concepts.Foundations.GameMorphism
import GameTheory.Concepts.Foundations.InertExtension
import GameTheory.Concepts.Equilibrium.SolutionConcepts

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

/-- An enriched strategy-indexed law family that is inert over a base law
family: enriched strategies have a projection to base strategies, and the
enriched machine law only depends on that projected profile. -/
structure StrategyInertLawFamily
    (M : Machine Player)
    (BaseStrategy EnrichedStrategy : Player → Type)
    (base : M.EventBatchLawFamily BaseStrategy) where
  proj : ∀ player, EnrichedStrategy player → BaseStrategy player
  embed : ∀ player, BaseStrategy player → EnrichedStrategy player
  section_proj : ∀ player strategy, proj player (embed player strategy) = strategy
  enriched : M.EventBatchLawFamily EnrichedStrategy
  law_inert :
    ∀ profile,
      enriched.law profile =
        base.law (fun player => proj player (profile player))

namespace StrategyInertLawFamily

variable {M : Machine Player}
variable {BaseStrategy EnrichedStrategy : Player → Type}
variable {base : M.EventBatchLawFamily BaseStrategy}

/-- The base trace game associated with an inert strategy enrichment. -/
noncomputable def baseTraceGame
    (_extension : StrategyInertLawFamily M BaseStrategy EnrichedStrategy base)
    (cutoff : Payoff Player) (horizon : Nat) : KernelGame Player :=
  eventBatchTraceKernelGame M BaseStrategy base cutoff horizon

/-- The enriched trace game associated with an inert strategy enrichment. -/
noncomputable def enrichedTraceGame
    (extension : StrategyInertLawFamily M BaseStrategy EnrichedStrategy base)
    (cutoff : Payoff Player) (horizon : Nat) : KernelGame Player :=
  eventBatchTraceKernelGame M EnrichedStrategy extension.enriched cutoff horizon

/-- An inert strategy-law enrichment induces a `GameTheory` inert extension of
the base event-batch trace game. This is the reusable bridge for future
message/restricted-strategy layers whose concrete law factors through an
erasure/projection to source strategies. -/
noncomputable def toInertExtension
    (extension : StrategyInertLawFamily M BaseStrategy EnrichedStrategy base)
    (cutoff : Payoff Player) (horizon : Nat) :
    (extension.baseTraceGame cutoff horizon).InertExtension where
  Strategy' := EnrichedStrategy
  proj := extension.proj
  embed := extension.embed
  section_proj := extension.section_proj
  outcomeKernel' := fun profile =>
    (extension.enrichedTraceGame cutoff horizon).outcomeKernel profile
  outcome_inert := by
    intro profile
    simp [baseTraceGame, enrichedTraceGame, eventBatchTraceKernelGame,
      extension.law_inert profile]

@[simp] theorem toInertExtension_game
    (extension : StrategyInertLawFamily M BaseStrategy EnrichedStrategy base)
    (cutoff : Payoff Player) (horizon : Nat) :
    (extension.toInertExtension cutoff horizon).game =
      extension.enrichedTraceGame cutoff horizon :=
  rfl

/-- Base Nash equilibria embed into inert enriched trace games. -/
theorem nash_embedProfile
    [DecidableEq Player]
    (extension : StrategyInertLawFamily M BaseStrategy EnrichedStrategy base)
    (cutoff : Payoff Player) (horizon : Nat)
    {profile : ∀ player, BaseStrategy player}
    (hNash : (extension.baseTraceGame cutoff horizon).IsNash profile) :
    (extension.enrichedTraceGame cutoff horizon).IsNash
      ((extension.toInertExtension cutoff horizon).embedProfile profile) := by
  simpa using
    (extension.toInertExtension cutoff horizon).nash_embedProfile hNash

/-- Any enriched profile whose projection is a base Nash equilibrium is a Nash
equilibrium of the inert enriched trace game. -/
theorem nash_of_projected_nash
    [DecidableEq Player]
    (extension : StrategyInertLawFamily M BaseStrategy EnrichedStrategy base)
    (cutoff : Payoff Player) (horizon : Nat)
    {profile : ∀ player, EnrichedStrategy player}
    (hNash :
      (extension.baseTraceGame cutoff horizon).IsNash
        ((extension.toInertExtension cutoff horizon).projectProfile
          profile)) :
    (extension.enrichedTraceGame cutoff horizon).IsNash profile := by
  simpa using
    (extension.toInertExtension cutoff horizon).nash_of_projected_nash
      hNash

/-- Nash equilibria of inert enriched trace games project to base Nash
equilibria. -/
theorem projected_nash_of_nash
    [DecidableEq Player]
    (extension : StrategyInertLawFamily M BaseStrategy EnrichedStrategy base)
    (cutoff : Payoff Player) (horizon : Nat)
    {profile : ∀ player, EnrichedStrategy player}
    (hNash : (extension.enrichedTraceGame cutoff horizon).IsNash profile) :
    (extension.baseTraceGame cutoff horizon).IsNash
      ((extension.toInertExtension cutoff horizon).projectProfile profile) := by
  simpa using
    (extension.toInertExtension cutoff horizon).projected_nash_of_nash
      hNash

/-- In inert enriched trace games, Nash equilibria are exactly base Nash
equilibria after projection. -/
theorem nash_iff
    [DecidableEq Player]
    (extension : StrategyInertLawFamily M BaseStrategy EnrichedStrategy base)
    (cutoff : Payoff Player) (horizon : Nat)
    {profile : ∀ player, EnrichedStrategy player} :
    (extension.enrichedTraceGame cutoff horizon).IsNash profile ↔
      (extension.baseTraceGame cutoff horizon).IsNash
        ((extension.toInertExtension cutoff horizon).projectProfile profile) := by
  simpa using (extension.toInertExtension cutoff horizon).nash_iff

end StrategyInertLawFamily

namespace StochasticRefinement

variable {Impl Spec : Machine Player}

/-- A profile-indexed lift of specification event-batch laws to implementation
event-batch laws through a stochastic refinement. -/
structure EventBatchLawFamilyLift
    (R : StochasticRefinement Impl Spec)
    (Strategy : Player → Type)
    (spec : Spec.EventBatchLawFamily Strategy) where
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
    (StochasticRefinement.refl M).EventBatchLawFamilyLift Strategy
      family where
  impl := family
  compatible := by
    intro profile
    exact StochasticRefinement.refl_eventBatchLawCompatible M
      (family.law profile)

variable {Low Mid : Machine Player}

/-- Compose two profile-indexed law-family lifts through composed stochastic
refinements. The lower lift must implement the upper lift's implementation law
family; this is the tower law-composition operation. -/
def compose
    {R₂ : StochasticRefinement Mid Spec}
    {R₁ : StochasticRefinement Low Mid}
    {spec : Spec.EventBatchLawFamily Strategy}
    (upper : R₂.EventBatchLawFamilyLift Strategy spec)
    (lower : R₁.EventBatchLawFamilyLift Strategy upper.impl) :
    (R₂.compose R₁).EventBatchLawFamilyLift Strategy spec where
  impl := lower.impl
  compatible := by
    intro profile
    exact
      StochasticRefinement.EventBatchLawCompatible.trans R₂ R₁
        (lower.compatible profile) (upper.compatible profile)

@[simp] theorem compose_impl
    {R₂ : StochasticRefinement Mid Spec}
    {R₁ : StochasticRefinement Low Mid}
    {spec : Spec.EventBatchLawFamily Strategy}
    (upper : R₂.EventBatchLawFamilyLift Strategy spec)
    (lower : R₁.EventBatchLawFamilyLift Strategy upper.impl) :
    (compose upper lower).impl = lower.impl :=
  rfl

variable {BaseStrategy EnrichedStrategy : Player → Type}

/-- Reindex a law-family lift along a strategy projection. This is the
mechanical step needed when a later runtime/presentation layer enriches
strategies but the lifted event-batch laws still factor through a smaller base
strategy space. -/
def reindex
    {R : StochasticRefinement Impl Spec}
    {spec : Spec.EventBatchLawFamily BaseStrategy}
    (lift : R.EventBatchLawFamilyLift BaseStrategy spec)
    (proj : ∀ player, EnrichedStrategy player → BaseStrategy player)
    (spec' : Spec.EventBatchLawFamily EnrichedStrategy)
    (spec_law_eq :
      ∀ profile,
        spec'.law profile =
          spec.law (fun player => proj player (profile player))) :
    R.EventBatchLawFamilyLift EnrichedStrategy spec' where
  impl :=
    { law := fun profile =>
        lift.impl.law (fun player => proj player (profile player))
      legal := fun profile =>
        lift.impl.legal (fun player => proj player (profile player)) }
  compatible := by
    intro profile trace
    rw [spec_law_eq profile]
    exact lift.compatible
      (fun player => proj player (profile player)) trace

/-- Reindex a lift through inert strategy enrichments on both the specification
and implementation machines. Unlike `reindexInertSpec`, this keeps an explicit
enriched implementation law family; the proof obligation is that both enriched
law families factor through the same base-strategy projection. -/
def reindexInert
    {R : StochasticRefinement Impl Spec}
    {base : Spec.EventBatchLawFamily BaseStrategy}
    (lift : R.EventBatchLawFamilyLift BaseStrategy base)
    (specExtension :
      Spec.StrategyInertLawFamily BaseStrategy EnrichedStrategy base)
    (implExtension :
      Impl.StrategyInertLawFamily BaseStrategy EnrichedStrategy lift.impl)
    (same_proj :
      ∀ player strategy,
        implExtension.proj player strategy =
          specExtension.proj player strategy) :
    R.EventBatchLawFamilyLift EnrichedStrategy specExtension.enriched where
  impl := implExtension.enriched
  compatible := by
    intro profile trace
    rw [implExtension.law_inert profile]
    have hprofile :
        (fun player => implExtension.proj player (profile player)) =
          (fun player => specExtension.proj player (profile player)) := by
      funext player
      exact same_proj player (profile player)
    rw [hprofile]
    rw [specExtension.law_inert profile]
    exact lift.compatible
      (fun player => specExtension.proj player (profile player)) trace

/-- Reindex a lift through an inert strategy enrichment on the specification
machine. -/
def reindexInertSpec
    {R : StochasticRefinement Impl Spec}
    {base : Spec.EventBatchLawFamily BaseStrategy}
    (lift : R.EventBatchLawFamilyLift BaseStrategy base)
    (extension :
      Spec.StrategyInertLawFamily BaseStrategy EnrichedStrategy base) :
    R.EventBatchLawFamilyLift EnrichedStrategy extension.enriched :=
  lift.reindex extension.proj extension.enriched extension.law_inert

@[simp] theorem reindexInert_impl
    {R : StochasticRefinement Impl Spec}
    {base : Spec.EventBatchLawFamily BaseStrategy}
    (lift : R.EventBatchLawFamilyLift BaseStrategy base)
    (specExtension :
      Spec.StrategyInertLawFamily BaseStrategy EnrichedStrategy base)
    (implExtension :
      Impl.StrategyInertLawFamily BaseStrategy EnrichedStrategy lift.impl)
    (same_proj :
      ∀ player strategy,
        implExtension.proj player strategy =
          specExtension.proj player strategy) :
    (lift.reindexInert specExtension implExtension same_proj).impl =
      implExtension.enriched :=
  rfl

end EventBatchLawFamilyLift

variable {Strategy : Player → Type}
variable {specFamily : Spec.EventBatchLawFamily Strategy}

/-- Projecting implementation event-batch traces gives the specification trace
distribution for compatible law families. -/
theorem eventBatchTraceKernelGame_projectTrace_eq
    (R : StochasticRefinement Impl Spec)
    (lift : R.EventBatchLawFamilyLift Strategy specFamily)
    (cutoff : Payoff Player) (horizon : Nat)
    (profile : ∀ player, Strategy player) :
    PMF.map R.projectEventBatchTrace
        ((eventBatchTraceKernelGame Impl Strategy lift.impl cutoff horizon)
          |>.outcomeKernel profile) =
      ((eventBatchTraceKernelGame Spec Strategy specFamily cutoff horizon)
        |>.outcomeKernel profile) := by
  have h :=
    R.eventBatchTraceDist_project_eq
      (specFamily.law profile) (lift.impl.law profile)
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

/-- Utility bounds pull back along a trace refinement. -/
theorem eventBatchTraceUtility_bound_project
    (R : StochasticRefinement Impl Spec)
    (cutoff : Payoff Player) {C : Player → ℝ}
    (hbdSpec :
      ∀ player trace,
        |eventBatchTraceUtility Spec cutoff trace player| ≤ C player)
    (player : Player) (trace : Impl.EventBatchTrace) :
    |eventBatchTraceUtility Impl cutoff trace player| ≤ C player := by
  rw [← R.eventBatchTraceUtility_project cutoff trace]
  exact hbdSpec player (R.projectEventBatchTrace trace)

/-- Compatible event-batch law families induce a utility-distribution
preserving kernel-game morphism from implementation traces to specification
traces. -/
noncomputable def eventBatchTraceMorphism
    (R : StochasticRefinement Impl Spec)
    (lift : R.EventBatchLawFamilyLift Strategy specFamily)
    (cutoff : Payoff Player) (horizon : Nat) :
    KernelGame.Morphism
      (eventBatchTraceKernelGame Impl Strategy lift.impl cutoff horizon)
      (eventBatchTraceKernelGame Spec Strategy specFamily cutoff horizon) :=
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
    (lift : R.EventBatchLawFamilyLift Strategy specFamily)
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
      (eventBatchTraceKernelGame Spec Strategy specFamily cutoff horizon) :=
  (R.eventBatchTraceMorphism lift cutoff horizon)
    |>.toEUMorphismOfBounded hbdImpl hbdSpec

/-- Nash equilibria of the specification trace game pull back to compatible
implementation trace games under bounded payoff hypotheses. -/
theorem eventBatchTraceKernelGame_nash_pullback_of_bounded
    [DecidableEq Player]
    (R : StochasticRefinement Impl Spec)
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
      |>.IsNash profile := by
  exact
    (R.eventBatchTraceEUMorphismOfBounded
      lift cutoff horizon hbdImpl hbdSpec).nash_of_nash hNash

theorem eventBatchTraceKernelGame_nash_pullback_of_inert_projected_nash
    [DecidableEq Player]
    (R : StochasticRefinement Impl Spec)
    {BaseStrategy EnrichedStrategy : Player → Type}
    {base : Spec.EventBatchLawFamily BaseStrategy}
    (extension :
      Spec.StrategyInertLawFamily BaseStrategy EnrichedStrategy base)
    (lift : R.EventBatchLawFamilyLift EnrichedStrategy extension.enriched)
    (cutoff : Payoff Player) (horizon : Nat)
    {CImpl CSpec : Player → ℝ}
    (hbdImpl :
      ∀ player trace,
        |eventBatchTraceUtility Impl cutoff trace player| ≤ CImpl player)
    (hbdSpec :
      ∀ player trace,
        |eventBatchTraceUtility Spec cutoff trace player| ≤ CSpec player)
    {profile : ∀ player, EnrichedStrategy player}
    (hNash :
      (extension.baseTraceGame cutoff horizon).IsNash
        ((extension.toInertExtension cutoff horizon).projectProfile
          profile)) :
    (eventBatchTraceKernelGame Impl EnrichedStrategy lift.impl cutoff horizon)
      |>.IsNash profile := by
  exact
    R.eventBatchTraceKernelGame_nash_pullback_of_bounded
      lift cutoff horizon hbdImpl hbdSpec
      (extension.nash_of_projected_nash cutoff horizon hNash)

end StochasticRefinement

end Machine

end Vegas
