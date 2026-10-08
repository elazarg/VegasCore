/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.FinitePayoffBounds
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheory.Core.Mixed

/-! # Positive collection over finite contingent plans

If every pure continuation plan has positive expected collection, finiteness
gives one strictly positive floor for every distribution over complete plans.
The mixing law may correlate players' plans. A bounded source horizon alone
does not make physical plans finite: the backend must also bound actions,
physical opportunities and relevant observations.
-/

noncomputable section

namespace GameTheory.Enforcement

open Math.Probability

variable {Plan Outcome : Type*} [Fintype Plan] [Nonempty Plan] [Finite Outcome]

/-- The minimum of pure-plan expected charges bounds all joint mixtures,
including correlated mixtures, of those complete continuation plans. -/
theorem pure_collection_floor_le_mixture (execute : Plan → PMF Outcome)
    (collected : Outcome → ℝ) (plans : PMF Plan) :
    FinitePayoffBounds.lower (fun plan => expect (execute plan) collected) ≤
      expect (plans.bind execute) collected := by
  rw [expect_bind_of_finite,
    ← expect_constant plans
      (FinitePayoffBounds.lower (fun plan => expect (execute plan) collected))]
  apply expect_mono _ (payoffIntegrable_constant _ _) (payoffIntegrable_of_finite _ _)
  intro plan _
  exact FinitePayoffBounds.lower_le _ plan

omit [Fintype Plan] in
/-- Strictly positive collection for each finite pure plan supplies a single
positive rate before the continuation's randomization is chosen. -/
theorem exists_positive_collection_floor (execute : Plan → PMF Outcome)
    [Finite Plan]
    (collected : Outcome → ℝ)
    (positive : ∀ plan, 0 < expect (execute plan) collected) :
    ∃ rate : ℝ, 0 < rate ∧
      ∀ plans : PMF Plan, rate ≤ expect (plans.bind execute) collected := by
  let := Fintype.ofFinite Plan
  refine ⟨FinitePayoffBounds.lower (fun plan => expect (execute plan) collected),
    (FinitePayoffBounds.lt_lower_iff _ 0).mpr positive, ?_⟩
  exact pure_collection_floor_le_mixture execute collected

end GameTheory.Enforcement

namespace GameTheory.GameForm

open Math.Probability

variable {Player : Type*} [Fintype Player] (form : GameForm Player)
  [∀ who, Finite (form.sig.Strategy who)] [∀ who, Nonempty (form.sig.Strategy who)]
  [Finite form.sig.Outcome]

/-- Positive pure-profile collection in a finite game form is uniform over
all mixed profiles. This is a mixture theorem, not a protocol realization. -/
theorem exists_positive_mixed_collection_floor (collected : form.sig.Outcome → ℝ)
    (positive : ∀ profile : Profile form.sig, 0 < expect (form.play profile) collected) :
    ∃ rate : ℝ, 0 < rate ∧
      ∀ profile : Profile form.sig.mixed, rate ≤ expect (form.mixed.play profile) collected := by
  classical
  obtain ⟨rate, positiveRate, floor⟩ :=
    Enforcement.exists_positive_collection_floor form.play collected positive
  refine ⟨rate, positiveRate, fun profile => ?_⟩
  exact floor (independentProduct profile)

end GameTheory.GameForm
