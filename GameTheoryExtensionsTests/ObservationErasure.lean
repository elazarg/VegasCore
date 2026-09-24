/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.ObservationAbstraction

/-! # Relevant facts, irrelevant private detail, and unreachable states

An observation can erase a real state distinction and still preserve all
optimal fact/action outcome laws. The criterion also ignores distinctions
supported only at states of zero prior probability. Both are stronger checks
than requiring the observation function to be globally injective.
-/

noncomputable section

namespace GameTheoryExtensionsTests.ObservationErasure

open GameTheory.DecisionExperiment GameTheory.Math.Probability

def twoBits : FinDist (Bool × Bool) := FinDist.uniformOfFintype

theorem firstBit_determines : Determines twoBits Prod.fst Prod.fst := by
  intro first _ second _ same
  exact same

theorem firstBit_not_injective : ¬ Function.Injective (Prod.fst : Bool × Bool → Bool) := by
  intro injective
  have same := injective (show (false, false).1 = (false, true).1 from rfl)
  have impossible := congrArg Prod.snd same
  cases impossible

/-- The erased second bit is a genuine supported distinction, yet every
utility on the retained first bit and arbitrary public actions is preserved. -/
theorem firstBit_preserves_every_optimal_law {Action : Type*}
    (utility : Bool → Action → ℝ) (law : FinDist (Bool × Action)) :
    (∃ policy : Bool → FinDist Action,
      IsBayesOptimal twoBits Prod.fst (fun state => utility state.1) policy ∧
        resultLaw twoBits Prod.fst Prod.fst policy = law) ↔
    (∃ policy : (Bool × Bool) → FinDist Action,
      IsBayesOptimal twoBits id (fun state => utility state.1) policy ∧
        resultLaw twoBits id Prod.fst policy = law) :=
  optimal_result_law_iff twoBits Prod.fst Prod.fst firstBit_determines utility law

theorem constant_determines_on_singleton :
    Determines (FinDist.pure false) (fun _ : Bool => ()) id := by
  intro first firstPresent second secondPresent _
  rw [FinDist.mem_support_pure] at firstPresent secondPresent
  exact firstPresent.trans secondPresent.symm

/-- Global collisions are harmless if they concern states outside the prior support. -/
theorem unreachable_merge_preserves {Action : Type*} (utility : Bool → Action → ℝ)
    (law : FinDist (Bool × Action)) :
    (∃ policy : Unit → FinDist Action,
      IsBayesOptimal (FinDist.pure false) (fun _ => ()) utility policy ∧
        resultLaw (FinDist.pure false) (fun _ => ()) id policy = law) ↔
    (∃ policy : Bool → FinDist Action,
      IsBayesOptimal (FinDist.pure false) id utility policy ∧
        resultLaw (FinDist.pure false) id id policy = law) :=
  optimal_result_law_iff (FinDist.pure false) (fun _ => ()) id
    constant_determines_on_singleton utility law

/-- With both bits possible, removing the bit forbids all-optimum preservation.
The quantifier allows an arbitrary utility-dependent strategy translator. -/
theorem supported_merge_does_not_preserve :
    ¬ (∀ utility : Bool → Bool → ℝ, ∀ source : Unit → FinDist Bool,
      IsBayesOptimal (FinDist.uniformOfFintype : FinDist Bool) (fun _ => ()) utility source →
        ∃ target : Bool → FinDist Bool,
          IsBayesOptimal (FinDist.uniformOfFintype : FinDist Bool) id utility target ∧
            resultLaw FinDist.uniformOfFintype id id target =
              resultLaw FinDist.uniformOfFintype (fun _ => ()) id source) := by
  intro preserves
  have determines := (preserves_all_optima_iff_determines
    (FinDist.uniformOfFintype : FinDist Bool) (fun _ => ()) id).mp preserves
  have impossible := determines false (FinDist.mem_support_uniformOfFintype false)
    true (FinDist.mem_support_uniformOfFintype true) rfl
  cases impossible

end GameTheoryExtensionsTests.ObservationErasure
