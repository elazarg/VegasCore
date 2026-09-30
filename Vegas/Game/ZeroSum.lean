/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ParameterOutcomes
import GameTheory.Core.ZeroSum

/-! # Zero-sum values through the pending-message compiler

The existing source-to-pending certificate supplies a native profile that no
finitely branching unilateral deviation improves on. In a two-player zero-sum
game, every native coarse correlated equilibrium recommending finitely branching
policies has the same expected payoff, even when its policies are outside the
compiler image.
This theorem uses the paper's public epoch service. It does not identify that
service with the finite reactive protocol or construct sequential equilibria.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Math.Probability

variable {L : IExpr} [IExpr.ResultTypes L] {Parameter : Type}

/-- Source equilibrium values agree with every coarse correlated native
equilibrium recommending finitely branching policies under the actual
pending-message compiler. Utilities may depend on initial private parameters
jointly with final public results. -/
theorem valueBindingParameterPendingGame_coarseCorrelated_value
    (setup : Setup (Player := Fin 2) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (parameter : State L setup.context → Parameter)
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List (Fin 2)) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (wireFinite : wire.FiniteSupport)
    (order : runtime.ServiceOrderPolicy) (orderFinite : order.FiniteSupport)
    (utility : Parameter × PublicOutcome setup.program → Fin 2 → ℝ)
    (zeroSum : IsZeroSum utility)
    (source : Profile (setup.valueBindingParameterGame parameter).sig)
    (sourceNash : IsNash (setup.valueBindingParameterGame parameter)
      (euPreference utility) source)
    (target : PMF (Profile
      (setup.eventPendingGame mode runtime roster reactionRounds wire order).sig))
    (targetCorrelated : IsCoarseCorrelatedEq
      (setup.eventPendingGame mode runtime roster reactionRounds wire order)
      (euPreference fun outcome who =>
        (setup.eventPendingParameterOutcome parameter mode runtime outcome).elim
          0 (fun result => utility result who)) target)
    (recommendedFinite : ∀ recommended ∈ target.support, ∀ who,
      Interaction.MessageApplication.PlayerPolicy.FiniteSupport (recommended who))
    (who : Fin 2) :
    extendedExpect ((setup.eventPendingGame mode runtime roster reactionRounds wire order
      ).outcomeLaw target) (fun outcome =>
        (setup.eventPendingParameterOutcome parameter mode runtime outcome).elim
          0 (fun result => utility result who)) =
      extendedExpect ((setup.valueBindingParameterGame parameter).play source)
        (fun result => utility result who) := by
  let nativeUtility := fun outcome player =>
    (setup.eventPendingParameterOutcome parameter mode runtime outcome).elim
      0 (fun result => utility result player)
  have nativeZeroSum : IsZeroSum nativeUtility := by
    intro outcome
    change (∑ player, nativeUtility outcome player) = 0
    dsimp only [nativeUtility]
    cases setup.eventPendingParameterOutcome parameter mode runtime outcome with
    | none => simp
    | some result => exact zeroSum result
  have nativeNash := (setup.valueBindingParameterPendingGame_nash_iff finite parameter mode
    runtime feasible roster reactionRounds wire wireFinite order orderFinite utility
    (fun _ => 0) source).mpr sourceNash
  have same := targetCorrelated.extendedExpectedUtility_eq_of_zeroSum_considered nativeZeroSum
    nativeNash recommendedFinite who
  have honest := (setup.valueBindingParameterPendingSimulation finite parameter mode runtime
    feasible roster reactionRounds wire wireFinite order orderFinite).honest_law source
  have value := congrArg (fun law => extendedExpect law
    (fun outcome => outcome.elim 0 (fun result => utility result who))) honest
  refine same.trans ?_
  simp only [extendedExpectedUtility, extendedExpect_map] at value ⊢
  exact value

end Vegas.SourceProgram.Setup
