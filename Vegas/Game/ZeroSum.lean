/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ParameterOutcomes
import GameTheoryExtensions.Core.ZeroSum

/-! # Zero-sum values through the pending-message compiler

The existing source-to-pending certificate supplies a native Nash equilibrium.
In a two-player zero-sum game, every native coarse correlated equilibrium has
the same expected payoff, even when its policies are outside the compiler image.
This theorem uses the paper's public epoch service. It does not identify that
service with the finite reactive protocol or construct sequential equilibria.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Math.Probability

variable {L : IExpr} [IExpr.ResultTypes L] {Parameter : Type}

/-- Source equilibrium values agree with every coarse correlated native
equilibrium under the actual pending-message compiler. Utilities may depend on
initial private parameters jointly with final public results. -/
theorem valueBindingParameterPendingGame_coarseCorrelated_value
    (setup : Setup (Player := Fin 2) (L := L))
    (parameter : State L setup.context → Parameter)
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List (Fin 2)) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (utility : Parameter × PublicOutcome setup.program → Fin 2 → ℝ)
    (zeroSum : IsZeroSum utility)
    (source : Profile (setup.valueBindingParameterGame parameter).sig)
    (sourceNash : IsNash (setup.valueBindingParameterGame parameter)
      (euPreference utility) source)
    (target : FinDist (Profile
      (setup.eventPendingGame mode runtime roster reactionRounds wire order).sig))
    (targetCorrelated : IsCoarseCorrelatedEq
      (setup.eventPendingGame mode runtime roster reactionRounds wire order)
      (euPreference fun outcome who =>
        (setup.eventPendingParameterOutcome parameter mode runtime outcome).elim
          0 (fun result => utility result who)) target)
    (who : Fin 2) :
    ((setup.eventPendingGame mode runtime roster reactionRounds wire order).outcomeLaw
      target).expect (fun outcome =>
        (setup.eventPendingParameterOutcome parameter mode runtime outcome).elim
          0 (fun result => utility result who)) =
      ((setup.valueBindingParameterGame parameter).play source).expect
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
  have nativeNash := (setup.valueBindingParameterPendingGame_nash_iff parameter mode
    runtime feasible roster reactionRounds wire order utility (fun _ => 0) source).mpr sourceNash
  have same := targetCorrelated.expectedUtility_eq_of_zeroSum nativeNash nativeZeroSum who
  have honest := (setup.valueBindingParameterPendingSimulation parameter mode runtime
    feasible roster reactionRounds wire order).honest_law source
  have value := congrArg (fun law => law.expect
    (fun outcome => outcome.elim 0 (fun result => utility result who))) honest
  have compileEq (player : Fin 2) :
      (setup.valueBindingParameterPendingSimulation parameter mode runtime feasible roster
        reactionRounds wire order).compileStrategy player (source player) =
        setup.compileValueBindingPendingProfile mode runtime player (source player) := rfl
  simp_rw [compileEq] at value
  exact same.trans (by
    simpa only [expectedUtility, FinDist.expect_map, Option.elim_some] using value)

end Vegas.SourceProgram.Setup
