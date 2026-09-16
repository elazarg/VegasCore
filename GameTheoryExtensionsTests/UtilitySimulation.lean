/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Core.UtilitySimulation
import GameTheoryExtensionsTests.MixtureSimulation

/-! # Utility-simulation regressions

The existing three-layer finite-mixture fixture is interpreted with a concrete
Boolean utility.  Its composed utility simulation must bound the genuinely
mixed target deviation by the profitable pure source action and preserve the
same approximate-Nash error at the compiled profile.
-/

noncomputable section

namespace GameTheory.GameForm.MixtureSimulationOn.Tests

open GameTheory.Math.Probability

def booleanUtility (value : Bool) (_player : Unit) : ℝ :=
  if value then 2 else 0

def firstUtility : UtilitySimulation source middle
    (fun outcome player => booleanUtility (sourceObserve outcome) player)
    (fun outcome player => booleanUtility (middleObserve outcome) player) :=
  first.toUtilitySimulation booleanUtility (fun _ _ => trivial)

def secondUtility : UtilitySimulation middle target
    (fun outcome player => booleanUtility (middleObserve outcome) player)
    (fun outcome player => booleanUtility (targetObserve outcome) player) :=
  second.toUtilitySimulation booleanUtility (fun _ _ => trivial)

def layeredUtility : UtilitySimulation source target
    (fun outcome player => booleanUtility (sourceObserve outcome) player)
    (fun outcome player => booleanUtility (targetObserve outcome) player) :=
  firstUtility.trans secondUtility

/-- The fair target deviation has utility one, so the composed bound must pick
the source action with utility two rather than the action with utility zero. -/
example :
    ∃ alternative : source.sig.Strategy (), alternative = true ∧
      (target.play (Profile.update (layeredUtility.compileProfile (fun _ => false))
        () (2 : Fin 3))).expect
          (fun outcome => booleanUtility (targetObserve outcome) ()) ≤
        (source.play (Profile.update (fun _ => false) () alternative)).expect
          (fun outcome => booleanUtility (sourceObserve outcome) ()) := by
  obtain ⟨alternative, bound⟩ :=
    layeredUtility.deviation_bound (fun _ => false) () (2 : Fin 3)
  refine ⟨alternative, ?_, bound⟩
  cases alternative
  · norm_num [source, target, targetObserve, sourceObserve, booleanUtility, coin,
      Fin.isValue, Fin.reduceEq, FinDist.expect_map, FinDist.expect_mix] at bound
    simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
      if_false] at bound
    norm_num [coin, FinDist.expect_map, FinDist.expect_mix, targetObserve,
      booleanUtility] at bound
  · rfl

/-- Error two is sufficient at the compiled false profile, and the utility
simulation transfers that concrete source calculation through both layers. -/
example : IsεNash target
    (fun outcome player => booleanUtility (targetObserve outcome) player) 2
    (layeredUtility.compileProfile (fun _ => false)) := by
  rw [layeredUtility.isεNash_compileProfile_iff]
  rw [isεNash_iff]
  intro who alternative
  cases who
  cases alternative <;>
    norm_num [source, sourceObserve, booleanUtility, expectedUtility]

end GameTheory.GameForm.MixtureSimulationOn.Tests
