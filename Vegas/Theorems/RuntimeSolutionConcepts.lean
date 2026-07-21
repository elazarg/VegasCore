/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Frontier.SolutionConcepts
import Vegas.Runtime.SolutionConcepts

/-!
# Runtime refinement claims for frontier solution concepts

Program-facing corollaries carrying expected-utility solution concepts from
pure and behavioral frontier games to trace-adequate implementation games.
-/

namespace Vegas

namespace WFProgram

open GameTheory

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

section Behavioral

variable (program : WFProgram P L) [FiniteDomains program]
  {Impl : Machine P}
  {R : Machine.StochasticRefinement Impl
    (ToEventGraph.PrimitiveMachine (ToEventGraph.compile program.core))}
  (bridge : RuntimeTraceAdequacy program
    (behavioralFrontierTraceSurface program) R)

/-- Behavioral ε-Nash status is invariant under runtime trace adequacy. -/
theorem claim_runtime_refinement_preserves_behavioral_epsilon_nash_iff
    (epsilon : ℝ) (profile : program.BehavioralFrontierProfile) :
    bridge.implTraceGame.IsεNash epsilon profile ↔
      program.BehavioralFrontierεNash epsilon profile := by
  simpa [behavioralFrontierTraceSurface,
    BehavioralFrontierεNash] using
    bridge.implTraceGame_epsilonNash_iff_surface_epsilonNash
      epsilon profile

/-- Behavioral Pareto dominance is invariant under runtime trace adequacy. -/
theorem claim_runtime_refinement_preserves_behavioral_pareto_dominance_iff
    (left right : program.BehavioralFrontierProfile) :
    bridge.implTraceGame.ParetoDominates left right ↔
      program.BehavioralFrontierParetoDominates left right := by
  simpa [behavioralFrontierTraceSurface,
    BehavioralFrontierParetoDominates] using
    bridge.implTraceGame_paretoDominates_iff_surface_paretoDominates
      left right

/-- Behavioral Pareto efficiency is invariant under runtime trace adequacy. -/
theorem claim_runtime_refinement_preserves_behavioral_pareto_efficiency_iff
    (profile : program.BehavioralFrontierProfile) :
    bridge.implTraceGame.IsParetoEfficient profile ↔
      program.BehavioralFrontierParetoEfficient profile := by
  simpa [behavioralFrontierTraceSurface,
    BehavioralFrontierParetoEfficient] using
    bridge.implTraceGame_paretoEfficient_iff_surface_paretoEfficient profile

/-- Behavioral individual rationality is invariant under runtime trace
adequacy. -/
theorem claim_runtime_refinement_preserves_behavioral_individual_rationality_iff
    (reservation : P → ℝ)
    (profile : program.BehavioralFrontierProfile) :
    bridge.implTraceGame.IsIndividuallyRational reservation profile ↔
      program.BehavioralFrontierIndividuallyRational reservation profile := by
  simpa [behavioralFrontierTraceSurface,
    BehavioralFrontierIndividuallyRational] using
    bridge.implTraceGame_individuallyRational_iff_surface_individuallyRational
      reservation profile

/-- A behavioral exact potential is valid for the runtime game exactly when it
is valid for the frontier game. -/
theorem claim_runtime_refinement_preserves_behavioral_exact_potential_iff
    (potential : program.BehavioralFrontierProfile → ℝ) :
    bridge.implTraceGame.IsExactPotential potential ↔
      program.BehavioralFrontierExactPotential potential := by
  simpa [behavioralFrontierTraceSurface,
    BehavioralFrontierExactPotential] using
    bridge.implTraceGame_exactPotential_iff_surface_exactPotential potential

/-- A behavioral weighted exact potential is valid for the runtime game
exactly when it is valid for the frontier game. -/
theorem claim_runtime_refinement_preserves_behavioral_weighted_exact_potential_iff
    (potential : program.BehavioralFrontierProfile → ℝ)
    (weight : P → ℝ) :
    bridge.implTraceGame.IsWeightedExactPotential potential weight ↔
      program.BehavioralFrontierWeightedExactPotential potential weight := by
  simpa [behavioralFrontierTraceSurface,
    BehavioralFrontierWeightedExactPotential] using
    bridge.implTraceGame_weightedExactPotential_iff_surface_weightedExactPotential
      potential weight

/-- A behavioral ordinal potential is valid for the runtime game exactly when
it is valid for the frontier game. -/
theorem claim_runtime_refinement_preserves_behavioral_ordinal_potential_iff
    (potential : program.BehavioralFrontierProfile → ℝ) :
    bridge.implTraceGame.IsOrdinalPotential potential ↔
      program.BehavioralFrontierOrdinalPotential potential := by
  simpa [behavioralFrontierTraceSurface,
    BehavioralFrontierOrdinalPotential] using
    bridge.implTraceGame_ordinalPotential_iff_surface_ordinalPotential
      potential

/-- Behavioral dominant-strategy solvability is invariant under runtime trace
adequacy. -/
theorem claim_runtime_refinement_preserves_behavioral_dominance_solvability_iff :
    bridge.implTraceGame.IsDominantStrategySolvable ↔
      program.BehavioralFrontierDominanceSolvable := by
  simpa [behavioralFrontierTraceSurface,
    BehavioralFrontierDominanceSolvable] using
    bridge.implTraceGame_dominanceSolvable_iff_surface_dominanceSolvable

/-- Behavioral survival under iterated pure strict-dominance elimination is
invariant under runtime trace adequacy. -/
theorem claim_runtime_refinement_preserves_behavioral_strict_dominance_survival_iff
    (round : Nat) (player : P)
    (strategy : program.BehavioralFrontierStrategy player) :
    bridge.implTraceGame.SurvivesStrictDominance round player strategy ↔
      program.BehavioralFrontierSurvivesStrictDominance
        round player strategy := by
  simpa [behavioralFrontierTraceSurface,
    BehavioralFrontierSurvivesStrictDominance] using
    bridge.implTraceGame_survivesStrictDominance_iff_surface_survivesStrictDominance
      round player strategy

/-- Behavioral IESDS solvability at a profile is invariant under runtime trace
adequacy. -/
theorem claim_runtime_refinement_preserves_behavioral_iesds_solvability_iff
    (profile : program.BehavioralFrontierProfile) :
    bridge.implTraceGame.IsIESDSSolvable profile ↔
      program.BehavioralFrontierIESDSSolvable profile := by
  simpa [behavioralFrontierTraceSurface,
    BehavioralFrontierIESDSSolvable] using
    bridge.implTraceGame_iesdsSolvable_iff_surface_iesdsSolvable profile

/-- Behavioral survival under iterated pure-strategy dominance elimination is
invariant under runtime trace adequacy. -/
theorem claim_runtime_refinement_preserves_behavioral_pure_survival_iff
    (round : Nat) (player : P)
    (strategy : program.BehavioralFrontierStrategy player) :
    bridge.implTraceGame.SurvivesPure round player strategy ↔
      program.BehavioralFrontierSurvivesPure round player strategy := by
  simpa [behavioralFrontierTraceSurface,
    BehavioralFrontierSurvivesPure] using
    bridge.implTraceGame_survivesPure_iff_surface_survivesPure
      round player strategy

/-- Behavioral pure rationalizability is invariant under runtime trace
adequacy. -/
theorem claim_runtime_refinement_preserves_behavioral_pure_rationalizability_iff
    (player : P)
    (strategy : program.BehavioralFrontierStrategy player) :
    bridge.implTraceGame.IsPureRationalizable player strategy ↔
      program.BehavioralFrontierPureRationalizable player strategy := by
  simpa [behavioralFrontierTraceSurface,
    BehavioralFrontierPureRationalizable] using
    bridge.implTraceGame_pureRationalizable_iff_surface_pureRationalizable
      player strategy

/-- Behavioral survival under iterated mixed-dominance elimination is
invariant under runtime trace adequacy. -/
theorem claim_runtime_refinement_preserves_behavioral_survival_iff
    (round : Nat) (player : P)
    (strategy : program.BehavioralFrontierStrategy player) :
    bridge.implTraceGame.Survives round player strategy ↔
      program.BehavioralFrontierSurvives round player strategy := by
  simpa [behavioralFrontierTraceSurface,
    BehavioralFrontierSurvives] using
    bridge.implTraceGame_survives_iff_surface_survives
      round player strategy

/-- Behavioral rationalizability is invariant under runtime trace adequacy. -/
theorem claim_runtime_refinement_preserves_behavioral_rationalizability_iff
    (player : P)
    (strategy : program.BehavioralFrontierStrategy player) :
    bridge.implTraceGame.IsRationalizable player strategy ↔
      program.BehavioralFrontierRationalizable player strategy := by
  simpa [behavioralFrontierTraceSurface,
    BehavioralFrontierRationalizable] using
    bridge.implTraceGame_rationalizable_iff_surface_rationalizable
      player strategy

/-- Behavioral payoff guarantees are invariant under runtime trace adequacy. -/
theorem claim_runtime_refinement_preserves_behavioral_guarantees_iff
    (player : P) (strategy : program.BehavioralFrontierStrategy player)
    (value : ℝ) :
    bridge.implTraceGame.Guarantees player strategy value ↔
      program.BehavioralFrontierGuarantees player strategy value := by
  simpa [behavioralFrontierTraceSurface,
    BehavioralFrontierGuarantees] using
    bridge.implTraceGame_guarantees_iff_surface_guarantees
      player strategy value

/-- Behavioral order-theoretic maximin values are preserved by runtime trace
adequacy. -/
theorem claim_runtime_refinement_preserves_behavioral_security_level
    (player : P) :
    bridge.implTraceGame.securityLevelSup player =
      program.behavioralFrontierSecurityLevelSup player := by
  simpa [behavioralFrontierTraceSurface,
    behavioralFrontierSecurityLevelSup] using
    bridge.implTraceGame_securityLevelSup_eq_surface_securityLevelSup player

/-- Behavioral order-theoretic security strategies are invariant under runtime
trace adequacy. -/
theorem claim_runtime_refinement_preserves_behavioral_security_strategy_iff
    (player : P) (strategy : program.BehavioralFrontierStrategy player) :
    bridge.implTraceGame.IsSecurityStrategySup player strategy ↔
      program.BehavioralFrontierSecurityStrategySup player strategy := by
  simpa [behavioralFrontierTraceSurface,
    BehavioralFrontierSecurityStrategySup] using
    bridge.implTraceGame_securityStrategySup_iff_surface_securityStrategySup
      player strategy

/-- Behavioral order-theoretic security profiles are invariant under runtime
trace adequacy. -/
theorem claim_runtime_refinement_preserves_behavioral_security_profile_iff
    (profile : program.BehavioralFrontierProfile) :
    bridge.implTraceGame.IsSecurityProfileSup profile ↔
      program.BehavioralFrontierSecurityProfileSup profile := by
  simpa [behavioralFrontierTraceSurface,
    BehavioralFrontierSecurityProfileSup] using
    bridge.implTraceGame_securityProfileSup_iff_surface_securityProfileSup
      profile

/-- Behavioral mixed maximin values are preserved by runtime trace adequacy. -/
theorem claim_runtime_refinement_preserves_behavioral_mixed_security_level
    (player : P) :
    bridge.implTraceGame.mixedSecurityLevel player =
      program.behavioralFrontierGame.mixedSecurityLevel player := by
  simpa [behavioralFrontierTraceSurface] using
    bridge.implTraceGame_mixedSecurityLevel_eq_surface_mixedSecurityLevel
      player

end Behavioral

section Pure

variable (program : WFProgram P L) [FiniteDomains program]
  {Impl : Machine P}
  {R : Machine.StochasticRefinement Impl
    (ToEventGraph.PrimitiveMachine (ToEventGraph.compile program.core))}
  (bridge : RuntimeTraceAdequacy program
    (pureFrontierTraceSurface program) R)

/-- Pure ε-Nash status is invariant under runtime trace adequacy. -/
theorem claim_runtime_refinement_preserves_pure_epsilon_nash_iff
    (epsilon : ℝ) (profile : program.PureFrontierProfile) :
    bridge.implTraceGame.IsεNash epsilon profile ↔
      program.PureFrontierεNash epsilon profile := by
  simpa [pureFrontierTraceSurface, PureFrontierεNash] using
    bridge.implTraceGame_epsilonNash_iff_surface_epsilonNash
      epsilon profile

/-- Pure Pareto dominance is invariant under runtime trace adequacy. -/
theorem claim_runtime_refinement_preserves_pure_pareto_dominance_iff
    (left right : program.PureFrontierProfile) :
    bridge.implTraceGame.ParetoDominates left right ↔
      program.PureFrontierParetoDominates left right := by
  simpa [pureFrontierTraceSurface, PureFrontierParetoDominates] using
    bridge.implTraceGame_paretoDominates_iff_surface_paretoDominates
      left right

/-- Pure Pareto efficiency is invariant under runtime trace adequacy. -/
theorem claim_runtime_refinement_preserves_pure_pareto_efficiency_iff
    (profile : program.PureFrontierProfile) :
    bridge.implTraceGame.IsParetoEfficient profile ↔
      program.PureFrontierParetoEfficient profile := by
  simpa [pureFrontierTraceSurface, PureFrontierParetoEfficient] using
    bridge.implTraceGame_paretoEfficient_iff_surface_paretoEfficient profile

/-- Pure individual rationality is invariant under runtime trace adequacy. -/
theorem claim_runtime_refinement_preserves_pure_individual_rationality_iff
    (reservation : P → ℝ) (profile : program.PureFrontierProfile) :
    bridge.implTraceGame.IsIndividuallyRational reservation profile ↔
      program.PureFrontierIndividuallyRational reservation profile := by
  simpa [pureFrontierTraceSurface,
    PureFrontierIndividuallyRational] using
    bridge.implTraceGame_individuallyRational_iff_surface_individuallyRational
      reservation profile

/-- A pure exact potential is valid for the runtime game exactly when it is
valid for the frontier game. -/
theorem claim_runtime_refinement_preserves_pure_exact_potential_iff
    (potential : program.PureFrontierProfile → ℝ) :
    bridge.implTraceGame.IsExactPotential potential ↔
      program.PureFrontierExactPotential potential := by
  simpa [pureFrontierTraceSurface, PureFrontierExactPotential] using
    bridge.implTraceGame_exactPotential_iff_surface_exactPotential potential

/-- A pure weighted exact potential is valid for the runtime game exactly when
it is valid for the frontier game. -/
theorem claim_runtime_refinement_preserves_pure_weighted_exact_potential_iff
    (potential : program.PureFrontierProfile → ℝ) (weight : P → ℝ) :
    bridge.implTraceGame.IsWeightedExactPotential potential weight ↔
      program.PureFrontierWeightedExactPotential potential weight := by
  simpa [pureFrontierTraceSurface,
    PureFrontierWeightedExactPotential] using
    bridge.implTraceGame_weightedExactPotential_iff_surface_weightedExactPotential
      potential weight

/-- A pure ordinal potential is valid for the runtime game exactly when it is
valid for the frontier game. -/
theorem claim_runtime_refinement_preserves_pure_ordinal_potential_iff
    (potential : program.PureFrontierProfile → ℝ) :
    bridge.implTraceGame.IsOrdinalPotential potential ↔
      program.PureFrontierOrdinalPotential potential := by
  simpa [pureFrontierTraceSurface, PureFrontierOrdinalPotential] using
    bridge.implTraceGame_ordinalPotential_iff_surface_ordinalPotential
      potential

/-- Pure dominant-strategy solvability is invariant under runtime trace
adequacy. -/
theorem claim_runtime_refinement_preserves_pure_dominance_solvability_iff :
    bridge.implTraceGame.IsDominantStrategySolvable ↔
      program.PureFrontierDominanceSolvable := by
  simpa [pureFrontierTraceSurface, PureFrontierDominanceSolvable] using
    bridge.implTraceGame_dominanceSolvable_iff_surface_dominanceSolvable

/-- Pure-frontier survival under iterated strict-dominance elimination is
invariant under runtime trace adequacy. -/
theorem claim_runtime_refinement_preserves_pure_strict_dominance_survival_iff
    (round : Nat) (player : P)
    (strategy : program.PureFrontierStrategy player) :
    bridge.implTraceGame.SurvivesStrictDominance round player strategy ↔
      program.PureFrontierSurvivesStrictDominance round player strategy := by
  simpa [pureFrontierTraceSurface,
    PureFrontierSurvivesStrictDominance] using
    bridge.implTraceGame_survivesStrictDominance_iff_surface_survivesStrictDominance
      round player strategy

/-- Pure-frontier IESDS solvability at a profile is invariant under runtime
trace adequacy. -/
theorem claim_runtime_refinement_preserves_pure_iesds_solvability_iff
    (profile : program.PureFrontierProfile) :
    bridge.implTraceGame.IsIESDSSolvable profile ↔
      program.PureFrontierIESDSSolvable profile := by
  simpa [pureFrontierTraceSurface, PureFrontierIESDSSolvable] using
    bridge.implTraceGame_iesdsSolvable_iff_surface_iesdsSolvable profile

/-- IESDS solvability of the finite pure frontier pins every correlated
equilibrium of a trace-adequate implementation to the surviving profile. -/
theorem claim_runtime_refinement_pure_correlated_eq_eq_pure_of_iesds
    (profile : program.PureFrontierProfile)
    (hsolvable : program.PureFrontierIESDSSolvable profile)
    {distribution : program.PureFrontierCorrelatedProfile}
    (hcorrelated : bridge.implTraceGame.IsCorrelatedEq distribution) :
    distribution = PMF.pure profile := by
  apply program.pureFrontier_correlatedEq_eq_pure_of_iesds hsolvable
  simpa [pureFrontierTraceSurface, PureFrontierCorrelatedEq] using
    (bridge.implTraceGame_correlatedEq_iff_surface_correlatedEq
      distribution).mp hcorrelated

/-- Pure-frontier survival under iterated pure-strategy dominance elimination
is invariant under runtime trace adequacy. -/
theorem claim_runtime_refinement_preserves_pure_pure_survival_iff
    (round : Nat) (player : P)
    (strategy : program.PureFrontierStrategy player) :
    bridge.implTraceGame.SurvivesPure round player strategy ↔
      program.PureFrontierSurvivesPure round player strategy := by
  simpa [pureFrontierTraceSurface, PureFrontierSurvivesPure] using
    bridge.implTraceGame_survivesPure_iff_surface_survivesPure
      round player strategy

/-- Pure-frontier pure rationalizability is invariant under runtime trace
adequacy. -/
theorem claim_runtime_refinement_preserves_pure_pure_rationalizability_iff
    (player : P) (strategy : program.PureFrontierStrategy player) :
    bridge.implTraceGame.IsPureRationalizable player strategy ↔
      program.PureFrontierPureRationalizable player strategy := by
  simpa [pureFrontierTraceSurface, PureFrontierPureRationalizable] using
    bridge.implTraceGame_pureRationalizable_iff_surface_pureRationalizable
      player strategy

/-- Pure survival under iterated mixed-dominance elimination is invariant
under runtime trace adequacy. -/
theorem claim_runtime_refinement_preserves_pure_survival_iff
    (round : Nat) (player : P)
    (strategy : program.PureFrontierStrategy player) :
    bridge.implTraceGame.Survives round player strategy ↔
      program.PureFrontierSurvives round player strategy := by
  simpa [pureFrontierTraceSurface, PureFrontierSurvives] using
    bridge.implTraceGame_survives_iff_surface_survives
      round player strategy

/-- Pure rationalizability is invariant under runtime trace adequacy. -/
theorem claim_runtime_refinement_preserves_pure_rationalizability_iff
    (player : P) (strategy : program.PureFrontierStrategy player) :
    bridge.implTraceGame.IsRationalizable player strategy ↔
      program.PureFrontierRationalizable player strategy := by
  simpa [pureFrontierTraceSurface, PureFrontierRationalizable] using
    bridge.implTraceGame_rationalizable_iff_surface_rationalizable
      player strategy

/-- Pure payoff guarantees are invariant under runtime trace adequacy. -/
theorem claim_runtime_refinement_preserves_pure_guarantees_iff
    (player : P) (strategy : program.PureFrontierStrategy player)
    (value : ℝ) :
    bridge.implTraceGame.Guarantees player strategy value ↔
      program.PureFrontierGuarantees player strategy value := by
  simpa [pureFrontierTraceSurface, PureFrontierGuarantees] using
    bridge.implTraceGame_guarantees_iff_surface_guarantees
      player strategy value

/-- Pure order-theoretic maximin values are preserved by runtime trace
adequacy. -/
theorem claim_runtime_refinement_preserves_pure_security_level_sup
    (player : P) :
    bridge.implTraceGame.securityLevelSup player =
      program.pureFrontierSecurityLevelSup player := by
  simpa [pureFrontierTraceSurface, pureFrontierSecurityLevelSup] using
    bridge.implTraceGame_securityLevelSup_eq_surface_securityLevelSup player

/-- Pure-frontier order-theoretic security strategies are invariant under
runtime trace adequacy. -/
theorem claim_runtime_refinement_preserves_pure_security_strategy_sup_iff
    (player : P) (strategy : program.PureFrontierStrategy player) :
    bridge.implTraceGame.IsSecurityStrategySup player strategy ↔
      program.PureFrontierSecurityStrategySup player strategy := by
  simpa [pureFrontierTraceSurface, PureFrontierSecurityStrategySup] using
    bridge.implTraceGame_securityStrategySup_iff_surface_securityStrategySup
      player strategy

/-- Pure-frontier order-theoretic security profiles are invariant under
runtime trace adequacy. -/
theorem claim_runtime_refinement_preserves_pure_security_profile_sup_iff
    (profile : program.PureFrontierProfile) :
    bridge.implTraceGame.IsSecurityProfileSup profile ↔
      program.PureFrontierSecurityProfileSup profile := by
  simpa [pureFrontierTraceSurface, PureFrontierSecurityProfileSup] using
    bridge.implTraceGame_securityProfileSup_iff_surface_securityProfileSup
      profile

/-- Pure mixed maximin values are preserved by runtime trace adequacy. -/
theorem claim_runtime_refinement_preserves_pure_mixed_security_level
    (player : P) :
    bridge.implTraceGame.mixedSecurityLevel player =
      program.pureFrontierGame.mixedSecurityLevel player := by
  simpa [pureFrontierTraceSurface] using
    bridge.implTraceGame_mixedSecurityLevel_eq_surface_mixedSecurityLevel
      player

/-- The finite pure-strategy maximin value is preserved by runtime trace
adequacy. -/
theorem claim_runtime_refinement_preserves_pure_security_level
    (player : P) :
    bridge.pureImplTraceGameSecurityLevel player =
      program.pureFrontierSecurityLevel player := by
  classical
  letI : ∀ who, Fintype (program.PureFrontierStrategy who) :=
    fun who => program.pureFrontierStrategyFintype who
  letI : ∀ who, Nonempty (program.PureFrontierStrategy who) :=
    fun who => program.pureFrontierStrategyNonempty who
  letI : Fintype (pureFrontierTraceSurface program).game.Profile := by
    change Fintype program.PureFrontierProfile
    infer_instance
  letI : Nonempty (pureFrontierTraceSurface program).game.Profile := by
    change Nonempty program.PureFrontierProfile
    infer_instance
  letI : ∀ who,
      Fintype ((pureFrontierTraceSurface program).game.Strategy who) := by
    intro who
    change Fintype (program.PureFrontierStrategy who)
    infer_instance
  letI : ∀ who,
      Nonempty ((pureFrontierTraceSurface program).game.Strategy who) := by
    intro who
    change Nonempty (program.PureFrontierStrategy who)
    infer_instance
  unfold RuntimeTraceAdequacy.pureImplTraceGameSecurityLevel
    pureFrontierSecurityLevel
  convert
    bridge.implTraceGame_securityLevel_eq_surface_securityLevel player using 1
  simp [pureFrontierTraceSurface]

/-- Price of anarchy is identical in the pure frontier and every
trace-adequate implementation game. -/
theorem claim_runtime_refinement_preserves_pure_price_of_anarchy
    (hImpl : ∃ profile : program.PureFrontierProfile,
      bridge.implTraceGame.IsNash profile)
    (hFrontier : ∃ profile : program.PureFrontierProfile,
      program.PureFrontierNash profile) :
    bridge.pureImplTraceGamePriceOfAnarchy hImpl =
      program.pureFrontierPriceOfAnarchy hFrontier := by
  classical
  letI : ∀ who, Fintype (program.PureFrontierStrategy who) :=
    fun who => program.pureFrontierStrategyFintype who
  letI : Fintype (pureFrontierTraceSurface program).game.Profile := by
    change Fintype program.PureFrontierProfile
    infer_instance
  have hSurface :
      ∃ profile : (pureFrontierTraceSurface program).game.Profile,
        (pureFrontierTraceSurface program).game.IsNash profile := by
    simpa [pureFrontierTraceSurface, PureFrontierNash] using hFrontier
  unfold RuntimeTraceAdequacy.pureImplTraceGamePriceOfAnarchy
    pureFrontierPriceOfAnarchy
  convert
    bridge.implTraceGame_priceOfAnarchy_eq_surface_priceOfAnarchy
      hImpl hSurface using 1
  simp [pureFrontierTraceSurface]

/-- Price of stability is identical in the pure frontier and every
trace-adequate implementation game. -/
theorem claim_runtime_refinement_preserves_pure_price_of_stability
    (hImpl : ∃ profile : program.PureFrontierProfile,
      bridge.implTraceGame.IsNash profile)
    (hFrontier : ∃ profile : program.PureFrontierProfile,
      program.PureFrontierNash profile) :
    bridge.pureImplTraceGamePriceOfStability hImpl =
      program.pureFrontierPriceOfStability hFrontier := by
  classical
  letI : ∀ who, Fintype (program.PureFrontierStrategy who) :=
    fun who => program.pureFrontierStrategyFintype who
  letI : Fintype (pureFrontierTraceSurface program).game.Profile := by
    change Fintype program.PureFrontierProfile
    infer_instance
  have hSurface :
      ∃ profile : (pureFrontierTraceSurface program).game.Profile,
        (pureFrontierTraceSurface program).game.IsNash profile := by
    simpa [pureFrontierTraceSurface, PureFrontierNash] using hFrontier
  unfold RuntimeTraceAdequacy.pureImplTraceGamePriceOfStability
    pureFrontierPriceOfStability
  convert
    bridge.implTraceGame_priceOfStability_eq_surface_priceOfStability
      hImpl hSurface using 1
  simp [pureFrontierTraceSurface]

end Pure

/-- Two-player behavioral saddle-point status is invariant under runtime trace
adequacy. -/
theorem claim_runtime_refinement_preserves_behavioral_saddle_point_iff
    (program : WFProgram (Fin 2) L) [FiniteDomains program]
    {Impl : Machine (Fin 2)}
    {R : Machine.StochasticRefinement Impl
      (ToEventGraph.PrimitiveMachine (ToEventGraph.compile program.core))}
    (bridge : RuntimeTraceAdequacy program
      (behavioralFrontierTraceSurface program) R)
    (profile : program.BehavioralFrontierProfile) :
    bridge.implTraceGame.IsSaddlePoint profile ↔
      program.BehavioralFrontierSaddlePoint profile := by
  simpa [behavioralFrontierTraceSurface,
    BehavioralFrontierSaddlePoint] using
    bridge.implTraceGame_saddlePoint_iff_surface_saddlePoint profile

/-- Two-player pure saddle-point status is invariant under runtime trace
adequacy. -/
theorem claim_runtime_refinement_preserves_pure_saddle_point_iff
    (program : WFProgram (Fin 2) L) [FiniteDomains program]
    {Impl : Machine (Fin 2)}
    {R : Machine.StochasticRefinement Impl
      (ToEventGraph.PrimitiveMachine (ToEventGraph.compile program.core))}
    (bridge : RuntimeTraceAdequacy program
      (pureFrontierTraceSurface program) R)
    (profile : program.PureFrontierProfile) :
    bridge.implTraceGame.IsSaddlePoint profile ↔
      program.PureFrontierSaddlePoint profile := by
  simpa [pureFrontierTraceSurface, PureFrontierSaddlePoint] using
    bridge.implTraceGame_saddlePoint_iff_surface_saddlePoint profile

end WFProgram

end Vegas
