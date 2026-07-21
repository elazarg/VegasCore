/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Runtime.TraceAdequacy
import GameTheory.Concepts.Transport.SolutionConcepts

/-!
# Runtime transport for solution concepts

Runtime trace adequacy gives the implementation trace game and its surface the
same strategy types and the same utility distribution at every profile. This
file specializes GameTheory's expected-utility game-isomorphism transport API
to that identity-on-strategies runtime boundary.

Outcome-level predicates such as `IsTeamGame`, `IsConstantSum`, and
`IsZeroSum` are intentionally absent: they quantify over every outcome,
including outcomes outside the support of every strategy profile, and therefore
do not follow from utility-distribution adequacy alone.
-/

namespace Vegas

namespace WFProgram

open GameTheory

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr}
  {program : WFProgram Player L} [FiniteDomains program]
  {surface : TraceGameSurface program}
  {Impl : Machine Player}
  {R : Machine.StochasticRefinement Impl
    (ToEventGraph.PrimitiveMachine (ToEventGraph.compile program.core))}

namespace RuntimeTraceAdequacy

/-- Expected utility is identical in the implementation trace game and its
adequate surface. -/
theorem implTraceGame_eu_surface
    (bridge : RuntimeTraceAdequacy program surface R)
    (profile : surface.game.Profile) (player : Player) :
    bridge.implTraceGame.eu profile player =
      surface.game.eu profile player := by
  simpa [implTraceGame_morphism_surface] using
    bridge.implTraceGame_morphism_surface.eu_preserved profile player

theorem implTraceGame_equivalence_surface_stratEquiv
    (bridge : RuntimeTraceAdequacy program surface R) (player : Player) :
    bridge.implTraceGame_equivalence_surface.stratEquiv player =
      Equiv.refl (surface.game.Strategy player) :=
  rfl

@[simp]
theorem implTraceGame_equivalence_surface_stratEquiv_apply
    (bridge : RuntimeTraceAdequacy program surface R) (player : Player)
    (strategy : surface.game.Strategy player) :
    bridge.implTraceGame_equivalence_surface.stratEquiv player strategy =
      strategy :=
  rfl

theorem implTraceGame_equivalence_surface_profileEquiv
    (bridge : RuntimeTraceAdequacy program surface R) :
    bridge.implTraceGame_equivalence_surface.profileEquiv =
      Equiv.refl surface.game.Profile := by
  apply Equiv.ext
  intro profile
  funext player
  rfl

@[simp]
theorem implTraceGame_equivalence_surface_profileEquiv_apply
    (bridge : RuntimeTraceAdequacy program surface R)
    (profile : surface.game.Profile) :
    bridge.implTraceGame_equivalence_surface.profileEquiv profile = profile := by
  funext player
  rfl

theorem implTraceGame_equivalence_surface_profileFunctionEquiv
    (bridge : RuntimeTraceAdequacy program surface R) {Value : Sort*} :
    GameTheory.KernelGame.EUGameIsomorphism.profileFunctionEquiv
        (α := Value) bridge.implTraceGame_equivalence_surface =
      Equiv.refl (surface.game.Profile → Value) := by
  rw [GameTheory.KernelGame.EUGameIsomorphism.profileFunctionEquiv,
    bridge.implTraceGame_equivalence_surface_profileEquiv]
  rfl

@[simp]
theorem implTraceGame_equivalence_surface_profileFunctionEquiv_apply
    (bridge : RuntimeTraceAdequacy program surface R) {Value : Sort*}
    (value : surface.game.Profile → Value) :
    bridge.implTraceGame_equivalence_surface.profileFunctionEquiv value =
      value := by
  funext profile
  rfl

theorem implTraceGame_equivalence_surface_strategyPMFEquiv
    (bridge : RuntimeTraceAdequacy program surface R) (player : Player) :
    bridge.implTraceGame_equivalence_surface.strategyPMFEquiv player =
      Equiv.refl (PMF (surface.game.Strategy player)) := by
  rw [GameTheory.KernelGame.EUGameIsomorphism.strategyPMFEquiv,
    bridge.implTraceGame_equivalence_surface_stratEquiv]
  exact Math.ProbabilityMassFunction.mapEquiv_refl _

@[simp]
theorem implTraceGame_equivalence_surface_strategyPMFEquiv_apply
    (bridge : RuntimeTraceAdequacy program surface R) (player : Player)
    (distribution : PMF (surface.game.Strategy player)) :
    bridge.implTraceGame_equivalence_surface.strategyPMFEquiv player
        distribution = distribution := by
  change PMF.map (fun strategy => strategy) distribution = distribution
  exact PMF.map_id distribution

@[simp]
theorem implTraceGame_equivalence_surface_map_stratEquiv
    (bridge : RuntimeTraceAdequacy program surface R) (player : Player)
    (distribution : PMF (surface.game.Strategy player)) :
    distribution.map
        (bridge.implTraceGame_equivalence_surface.stratEquiv player) =
      distribution := by
  change PMF.map (fun strategy => strategy) distribution = distribution
  exact PMF.map_id distribution

/-- Best-response status is invariant under runtime trace adequacy. -/
theorem implTraceGame_bestResponse_iff_surface_bestResponse
    (bridge : RuntimeTraceAdequacy program surface R)
    (player : Player) (profile : surface.game.Profile)
    (strategy : surface.game.Strategy player) :
    bridge.implTraceGame.IsBestResponse player profile strategy ↔
      surface.game.IsBestResponse player profile strategy := by
  simpa using
    bridge.implTraceGame_equivalence_surface.isBestResponse_iff
      player profile strategy

/-- Dominant-strategy status is invariant under runtime trace adequacy. -/
theorem implTraceGame_dominant_iff_surface_dominant
    (bridge : RuntimeTraceAdequacy program surface R)
    (player : Player) (strategy : surface.game.Strategy player) :
    bridge.implTraceGame.IsDominant player strategy ↔
      surface.game.IsDominant player strategy := by
  simpa using
    bridge.implTraceGame_equivalence_surface.dominant_iff player strategy

/-- Strict-Nash status is invariant under runtime trace adequacy. -/
theorem implTraceGame_strictNash_iff_surface_strictNash
    (bridge : RuntimeTraceAdequacy program surface R)
    (profile : surface.game.Profile) :
    bridge.implTraceGame.IsStrictNash profile ↔
      surface.game.IsStrictNash profile := by
  simpa using
    bridge.implTraceGame_equivalence_surface.isStrictNash_iff profile

/-- Strictly dominant strategies are invariant under runtime trace adequacy. -/
theorem implTraceGame_strictDominant_iff_surface_strictDominant
    (bridge : RuntimeTraceAdequacy program surface R)
    (player : Player) (strategy : surface.game.Strategy player) :
    bridge.implTraceGame.IsStrictDominant player strategy ↔
      surface.game.IsStrictDominant player strategy := by
  simpa using
    bridge.implTraceGame_equivalence_surface.isStrictDominant_iff
      player strategy

/-- Weak dominance is invariant under runtime trace adequacy. -/
theorem implTraceGame_weaklyDominates_iff_surface_weaklyDominates
    (bridge : RuntimeTraceAdequacy program surface R)
    (player : Player) (left right : surface.game.Strategy player) :
    bridge.implTraceGame.WeaklyDominates player left right ↔
      surface.game.WeaklyDominates player left right := by
  simpa using
    bridge.implTraceGame_equivalence_surface.weaklyDominates_iff
      player left right

/-- Strict dominance between two strategies is invariant under runtime trace
adequacy. -/
theorem implTraceGame_strictlyDominates_iff_surface_strictlyDominates
    (bridge : RuntimeTraceAdequacy program surface R)
    (player : Player) (left right : surface.game.Strategy player) :
    bridge.implTraceGame.StrictlyDominates player left right ↔
      surface.game.StrictlyDominates player left right := by
  simpa using
    bridge.implTraceGame_equivalence_surface.strictlyDominates_iff
      player left right

/-- Approximate Nash status is invariant under runtime trace adequacy. -/
theorem implTraceGame_epsilonNash_iff_surface_epsilonNash
    (bridge : RuntimeTraceAdequacy program surface R)
    (epsilon : ℝ) (profile : surface.game.Profile) :
    bridge.implTraceGame.IsεNash epsilon profile ↔
      surface.game.IsεNash epsilon profile := by
  simpa using
    bridge.implTraceGame_equivalence_surface.isεNash_iff epsilon profile

/-- Approximate best-response status is invariant under runtime trace
adequacy. -/
theorem implTraceGame_epsilonBestResponse_iff_surface_epsilonBestResponse
    (bridge : RuntimeTraceAdequacy program surface R)
    (epsilon : ℝ) (player : Player) (profile : surface.game.Profile)
    (strategy : surface.game.Strategy player) :
    bridge.implTraceGame.IsεBestResponse epsilon player profile strategy ↔
      surface.game.IsεBestResponse epsilon player profile strategy := by
  simpa using
    bridge.implTraceGame_equivalence_surface.isεBestResponse_iff
      epsilon player profile strategy

/-- Pareto dominance is invariant under runtime trace adequacy. -/
theorem implTraceGame_paretoDominates_iff_surface_paretoDominates
    (bridge : RuntimeTraceAdequacy program surface R)
    (left right : surface.game.Profile) :
    bridge.implTraceGame.ParetoDominates left right ↔
      surface.game.ParetoDominates left right := by
  simpa using
    bridge.implTraceGame_equivalence_surface.paretoDominates_iff left right

/-- Pareto efficiency is invariant under runtime trace adequacy. -/
theorem implTraceGame_paretoEfficient_iff_surface_paretoEfficient
    (bridge : RuntimeTraceAdequacy program surface R)
    (profile : surface.game.Profile) :
    bridge.implTraceGame.IsParetoEfficient profile ↔
      surface.game.IsParetoEfficient profile := by
  simpa using
    bridge.implTraceGame_equivalence_surface.isParetoEfficient_iff profile

/-- Individual rationality at a fixed reservation vector is invariant under
runtime trace adequacy. -/
theorem implTraceGame_individuallyRational_iff_surface_individuallyRational
    (bridge : RuntimeTraceAdequacy program surface R)
    (reservation : Player → ℝ) (profile : surface.game.Profile) :
    bridge.implTraceGame.IsIndividuallyRational reservation profile ↔
      surface.game.IsIndividuallyRational reservation profile := by
  simpa using
    bridge.implTraceGame_equivalence_surface.isIndividuallyRational_iff
      reservation profile

/-- Exact-potential status for a fixed potential is invariant under runtime
trace adequacy. -/
theorem implTraceGame_exactPotential_iff_surface_exactPotential
    (bridge : RuntimeTraceAdequacy program surface R)
    (potential : surface.game.Profile → ℝ) :
    bridge.implTraceGame.IsExactPotential potential ↔
      surface.game.IsExactPotential potential := by
  simpa using
    bridge.implTraceGame_equivalence_surface.isExactPotential_iff potential

/-- Weighted exact-potential status for a fixed potential and weight vector is
invariant under runtime trace adequacy. -/
theorem implTraceGame_weightedExactPotential_iff_surface_weightedExactPotential
    (bridge : RuntimeTraceAdequacy program surface R)
    (potential : surface.game.Profile → ℝ) (weight : Player → ℝ) :
    bridge.implTraceGame.IsWeightedExactPotential potential weight ↔
      surface.game.IsWeightedExactPotential potential weight := by
  simpa using
    bridge.implTraceGame_equivalence_surface.isWeightedExactPotential_iff
      potential weight

/-- Ordinal-potential status for a fixed potential is invariant under runtime
trace adequacy. -/
theorem implTraceGame_ordinalPotential_iff_surface_ordinalPotential
    (bridge : RuntimeTraceAdequacy program surface R)
    (potential : surface.game.Profile → ℝ) :
    bridge.implTraceGame.IsOrdinalPotential potential ↔
      surface.game.IsOrdinalPotential potential := by
  simpa using
    bridge.implTraceGame_equivalence_surface.isOrdinalPotential_iff potential

/-- Dominant-strategy solvability is invariant under runtime trace adequacy. -/
theorem implTraceGame_dominanceSolvable_iff_surface_dominanceSolvable
    (bridge : RuntimeTraceAdequacy program surface R) :
    bridge.implTraceGame.IsDominantStrategySolvable ↔
      surface.game.IsDominantStrategySolvable := by
  simpa using
    bridge.implTraceGame_equivalence_surface.isDominantStrategySolvable_iff

/-- Survival under iterated pure strict-dominance elimination is invariant
under runtime trace adequacy. -/
theorem implTraceGame_survivesStrictDominance_iff_surface_survivesStrictDominance
    (bridge : RuntimeTraceAdequacy program surface R)
    (round : Nat) (player : Player)
    (strategy : surface.game.Strategy player) :
    bridge.implTraceGame.SurvivesStrictDominance round player strategy ↔
      surface.game.SurvivesStrictDominance round player strategy := by
  simpa using
    bridge.implTraceGame_equivalence_surface.survivesStrictDominance_iff
      round player strategy

/-- IESDS solvability at a profile is invariant under runtime trace adequacy. -/
theorem implTraceGame_iesdsSolvable_iff_surface_iesdsSolvable
    (bridge : RuntimeTraceAdequacy program surface R)
    (profile : surface.game.Profile) :
    bridge.implTraceGame.IsIESDSSolvable profile ↔
      surface.game.IsIESDSSolvable profile := by
  simpa using
    bridge.implTraceGame_equivalence_surface.isIESDSSolvable_iff profile

/-- If the adequate surface is IESDS-solvable, every runtime correlated
equilibrium is the same point mass. This deliberately applies the uniqueness
theorem on the finite surface: implementation trace outcomes are lists and need
not form a finite raw outcome type. -/
theorem implTraceGame_correlatedEq_eq_pure_of_surface_iesds
    (bridge : RuntimeTraceAdequacy program surface R)
    [Finite surface.game.Profile] [Finite surface.game.Outcome]
    {profile : surface.game.Profile}
    (hsolvable : surface.game.IsIESDSSolvable profile)
    {distribution : PMF surface.game.Profile}
    (hcorrelated : bridge.implTraceGame.IsCorrelatedEq distribution) :
    distribution = PMF.pure profile :=
  hsolvable.correlatedEq_eq_pure
    ((bridge.implTraceGame_correlatedEq_iff_surface_correlatedEq
      distribution).mp hcorrelated)

/-- Survival under iterated pure-strategy dominance elimination is invariant
under runtime trace adequacy. -/
theorem implTraceGame_survivesPure_iff_surface_survivesPure
    (bridge : RuntimeTraceAdequacy program surface R)
    (round : Nat) (player : Player)
    (strategy : surface.game.Strategy player) :
    bridge.implTraceGame.SurvivesPure round player strategy ↔
      surface.game.SurvivesPure round player strategy := by
  simpa using
    bridge.implTraceGame_equivalence_surface.survivesPure_iff
      round player strategy

/-- Pure rationalizability is invariant under runtime trace adequacy. -/
theorem implTraceGame_pureRationalizable_iff_surface_pureRationalizable
    (bridge : RuntimeTraceAdequacy program surface R)
    (player : Player) (strategy : surface.game.Strategy player) :
    bridge.implTraceGame.IsPureRationalizable player strategy ↔
      surface.game.IsPureRationalizable player strategy := by
  simpa using
    bridge.implTraceGame_equivalence_surface.isPureRationalizable_iff
      player strategy

/-- Survival under iterated elimination by mixed dominance is invariant under
runtime trace adequacy. -/
theorem implTraceGame_survives_iff_surface_survives
    (bridge : RuntimeTraceAdequacy program surface R)
    (round : Nat) (player : Player)
    (strategy : surface.game.Strategy player) :
    bridge.implTraceGame.Survives round player strategy ↔
      surface.game.Survives round player strategy := by
  simpa using
    bridge.implTraceGame_equivalence_surface.survives_iff
      round player strategy

/-- Rationalizability is invariant under runtime trace adequacy. -/
theorem implTraceGame_rationalizable_iff_surface_rationalizable
    (bridge : RuntimeTraceAdequacy program surface R)
    (player : Player) (strategy : surface.game.Strategy player) :
    bridge.implTraceGame.IsRationalizable player strategy ↔
      surface.game.IsRationalizable player strategy := by
  simpa using
    bridge.implTraceGame_equivalence_surface.isRationalizable_iff
      player strategy

/-- A fixed strategy guarantees the same threshold in the implementation and
surface games. -/
theorem implTraceGame_guarantees_iff_surface_guarantees
    (bridge : RuntimeTraceAdequacy program surface R)
    (player : Player) (strategy : surface.game.Strategy player)
    (value : ℝ) :
    bridge.implTraceGame.Guarantees player strategy value ↔
      surface.game.Guarantees player strategy value := by
  simpa using
    bridge.implTraceGame_equivalence_surface.guarantees_iff
      player strategy value

/-- Order-theoretic worst-case utility is preserved by runtime trace
adequacy. -/
theorem implTraceGame_worstCaseEUInf_eq_surface_worstCaseEUInf
    (bridge : RuntimeTraceAdequacy program surface R)
    (player : Player) (strategy : surface.game.Strategy player) :
    bridge.implTraceGame.worstCaseEUInf player strategy =
      surface.game.worstCaseEUInf player strategy := by
  simpa using
    bridge.implTraceGame_equivalence_surface.worstCaseEUInf_eq
      player strategy

/-- Order-theoretic security levels are preserved by runtime trace adequacy. -/
theorem implTraceGame_securityLevelSup_eq_surface_securityLevelSup
    (bridge : RuntimeTraceAdequacy program surface R)
    (player : Player) :
    bridge.implTraceGame.securityLevelSup player =
      surface.game.securityLevelSup player := by
  simpa using
    bridge.implTraceGame_equivalence_surface.securityLevelSup_eq player

/-- Attainment of the pure order-theoretic security level is invariant under
runtime trace adequacy. -/
theorem implTraceGame_securityStrategySup_iff_surface_securityStrategySup
    (bridge : RuntimeTraceAdequacy program surface R)
    (player : Player) (strategy : surface.game.Strategy player) :
    bridge.implTraceGame.IsSecurityStrategySup player strategy ↔
      surface.game.IsSecurityStrategySup player strategy := by
  simpa using
    bridge.implTraceGame_equivalence_surface.isSecurityStrategySup_iff
      player strategy

/-- A profile consists of order-theoretic security strategies in the runtime
game exactly when it does on the adequate surface. -/
theorem implTraceGame_securityProfileSup_iff_surface_securityProfileSup
    (bridge : RuntimeTraceAdequacy program surface R)
    (profile : surface.game.Profile) :
    bridge.implTraceGame.IsSecurityProfileSup profile ↔
      surface.game.IsSecurityProfileSup profile := by
  simpa using
    bridge.implTraceGame_equivalence_surface.isSecurityProfileSup_iff profile

/-- Mixed-own-strategy worst-case utility is preserved by runtime trace
adequacy. -/
theorem implTraceGame_mixedWorstCaseEUInf_eq_surface_mixedWorstCaseEUInf
    (bridge : RuntimeTraceAdequacy program surface R)
    (player : Player) (strategy : PMF (surface.game.Strategy player)) :
    bridge.implTraceGame.mixedWorstCaseEUInf player strategy =
      surface.game.mixedWorstCaseEUInf player strategy := by
  simpa using
    bridge.implTraceGame_equivalence_surface.mixedWorstCaseEUInf_eq
      player strategy

/-- Mixed maximin values are preserved by runtime trace adequacy. -/
theorem implTraceGame_mixedSecurityLevel_eq_surface_mixedSecurityLevel
    (bridge : RuntimeTraceAdequacy program surface R)
    (player : Player) :
    bridge.implTraceGame.mixedSecurityLevel player =
      surface.game.mixedSecurityLevel player := by
  simpa using
    bridge.implTraceGame_equivalence_surface.mixedSecurityLevel_eq player

/-- A finite profile type on an adequate surface induces one on the
implementation trace game through their shared strategy types. -/
noncomputable instance implTraceGameProfileFintype
    (bridge : RuntimeTraceAdequacy program surface R)
    [Fintype surface.game.Profile] :
    Fintype bridge.implTraceGame.Profile := by
  change Fintype surface.game.Profile
  infer_instance

/-- Finiteness of an adequate surface profile type transfers to the
implementation trace game. -/
instance implTraceGameProfileFinite
    (bridge : RuntimeTraceAdequacy program surface R)
    [Finite surface.game.Profile] :
    Finite bridge.implTraceGame.Profile := by
  change Finite surface.game.Profile
  infer_instance

/-- Nonemptiness of an adequate surface profile type transfers to the
implementation trace game. -/
noncomputable instance implTraceGameProfileNonempty
    (bridge : RuntimeTraceAdequacy program surface R)
    [Nonempty surface.game.Profile] :
    Nonempty bridge.implTraceGame.Profile := by
  change Nonempty surface.game.Profile
  infer_instance

/-- A finite surface strategy type induces the corresponding finite runtime
strategy type. -/
noncomputable instance implTraceGameStrategyFintype
    (bridge : RuntimeTraceAdequacy program surface R)
    (player : Player) [Fintype (surface.game.Strategy player)] :
    Fintype (bridge.implTraceGame.Strategy player) := by
  change Fintype (surface.game.Strategy player)
  infer_instance

/-- A finite surface strategy type induces the corresponding finite runtime
strategy type. -/
instance implTraceGameStrategyFinite
    (bridge : RuntimeTraceAdequacy program surface R)
    (player : Player) [Finite (surface.game.Strategy player)] :
    Finite (bridge.implTraceGame.Strategy player) := by
  change Finite (surface.game.Strategy player)
  infer_instance

/-- Nonemptiness of a surface strategy type transfers to the runtime game. -/
noncomputable instance implTraceGameStrategyNonempty
    (bridge : RuntimeTraceAdequacy program surface R)
    (player : Player) [Nonempty (surface.game.Strategy player)] :
    Nonempty (bridge.implTraceGame.Strategy player) := by
  change Nonempty (surface.game.Strategy player)
  infer_instance

/-- Finite-game worst-case utility is preserved by runtime trace adequacy. -/
theorem implTraceGame_worstCaseEU_eq_surface_worstCaseEU
    (bridge : RuntimeTraceAdequacy program surface R)
    [Finite surface.game.Profile] [Nonempty surface.game.Profile]
    (player : Player) (strategy : surface.game.Strategy player) :
    bridge.implTraceGame.worstCaseEU player strategy =
      surface.game.worstCaseEU player strategy := by
  simpa using
    bridge.implTraceGame_equivalence_surface.worstCaseEU_eq player strategy

/-- Finite-game security levels are preserved by runtime trace adequacy. -/
theorem implTraceGame_securityLevel_eq_surface_securityLevel
    (bridge : RuntimeTraceAdequacy program surface R)
    [Finite surface.game.Profile] [Nonempty surface.game.Profile]
    [∀ player, Finite (surface.game.Strategy player)]
    [∀ player, Nonempty (surface.game.Strategy player)]
    (player : Player) :
    bridge.implTraceGame.securityLevel player =
      surface.game.securityLevel player := by
  simpa using
    bridge.implTraceGame_equivalence_surface.securityLevel_eq player

/-- Attainment of the finite security level is invariant under runtime trace
adequacy. -/
theorem implTraceGame_securityStrategy_iff_surface_securityStrategy
    (bridge : RuntimeTraceAdequacy program surface R)
    [Finite surface.game.Profile] [Nonempty surface.game.Profile]
    [∀ player, Finite (surface.game.Strategy player)]
    [∀ player, Nonempty (surface.game.Strategy player)]
    (player : Player) (strategy : surface.game.Strategy player) :
    bridge.implTraceGame.IsSecurityStrategy player strategy ↔
      surface.game.IsSecurityStrategy player strategy := by
  simpa using
    bridge.implTraceGame_equivalence_surface.isSecurityStrategy_iff
      player strategy

/-- A finite security profile is invariant under runtime trace adequacy. -/
theorem implTraceGame_securityProfile_iff_surface_securityProfile
    (bridge : RuntimeTraceAdequacy program surface R)
    [Finite surface.game.Profile] [Nonempty surface.game.Profile]
    [∀ player, Finite (surface.game.Strategy player)]
    [∀ player, Nonempty (surface.game.Strategy player)]
    (profile : surface.game.Profile) :
    bridge.implTraceGame.IsSecurityProfile profile ↔
      surface.game.IsSecurityProfile profile := by
  simpa using
    bridge.implTraceGame_equivalence_surface.isSecurityProfile_iff profile

/-- Social welfare is identical at every profile under runtime trace
adequacy. -/
theorem implTraceGame_socialWelfare_eq_surface_socialWelfare
    (bridge : RuntimeTraceAdequacy program surface R)
    (profile : surface.game.Profile) :
    bridge.implTraceGame.socialWelfare profile =
      surface.game.socialWelfare profile := by
  simpa using
    bridge.implTraceGame_equivalence_surface.socialWelfare_eq profile

/-- Optimal social welfare is preserved by runtime trace adequacy. -/
theorem implTraceGame_optimalWelfare_eq_surface_optimalWelfare
    (bridge : RuntimeTraceAdequacy program surface R) :
    bridge.implTraceGame.optimalWelfare = surface.game.optimalWelfare := by
  simpa using
    bridge.implTraceGame_equivalence_surface.optimalWelfare_eq

/-- Best Nash welfare is preserved by runtime trace adequacy. -/
theorem implTraceGame_bestNashWelfare_eq_surface_bestNashWelfare
    (bridge : RuntimeTraceAdequacy program surface R)
    [Finite surface.game.Profile]
    (hImpl : ∃ profile, bridge.implTraceGame.IsNash profile)
    (hSurface : ∃ profile, surface.game.IsNash profile) :
    bridge.implTraceGame.bestNashWelfare hImpl =
      surface.game.bestNashWelfare hSurface := by
  simpa using
    bridge.implTraceGame_equivalence_surface.bestNashWelfare_eq hImpl

/-- Worst Nash welfare is preserved by runtime trace adequacy. -/
theorem implTraceGame_worstNashWelfare_eq_surface_worstNashWelfare
    (bridge : RuntimeTraceAdequacy program surface R)
    [Finite surface.game.Profile]
    (hImpl : ∃ profile, bridge.implTraceGame.IsNash profile)
    (hSurface : ∃ profile, surface.game.IsNash profile) :
    bridge.implTraceGame.worstNashWelfare hImpl =
      surface.game.worstNashWelfare hSurface := by
  simpa using
    bridge.implTraceGame_equivalence_surface.worstNashWelfare_eq hImpl

/-- Price of anarchy is preserved by runtime trace adequacy. -/
theorem implTraceGame_priceOfAnarchy_eq_surface_priceOfAnarchy
    (bridge : RuntimeTraceAdequacy program surface R)
    [Finite surface.game.Profile]
    (hImpl : ∃ profile, bridge.implTraceGame.IsNash profile)
    (hSurface : ∃ profile, surface.game.IsNash profile) :
    bridge.implTraceGame.priceOfAnarchy hImpl =
      surface.game.priceOfAnarchy hSurface := by
  simpa using
    bridge.implTraceGame_equivalence_surface.priceOfAnarchy_eq hImpl

/-- Price of stability is preserved by runtime trace adequacy. -/
theorem implTraceGame_priceOfStability_eq_surface_priceOfStability
    (bridge : RuntimeTraceAdequacy program surface R)
    [Finite surface.game.Profile]
    (hImpl : ∃ profile, bridge.implTraceGame.IsNash profile)
    (hSurface : ∃ profile, surface.game.IsNash profile) :
    bridge.implTraceGame.priceOfStability hImpl =
      surface.game.priceOfStability hSurface := by
  simpa using
    bridge.implTraceGame_equivalence_surface.priceOfStability_eq hImpl

/-- Two-player saddle-point status is invariant under runtime trace adequacy. -/
theorem implTraceGame_saddlePoint_iff_surface_saddlePoint
    {L : IExpr}
    {program : WFProgram (Fin 2) L} [FiniteDomains program]
    {surface : TraceGameSurface program}
    {Impl : Machine (Fin 2)}
    {R : Machine.StochasticRefinement Impl
      (ToEventGraph.PrimitiveMachine (ToEventGraph.compile program.core))}
    (bridge : RuntimeTraceAdequacy program surface R)
    (profile : surface.game.Profile) :
    bridge.implTraceGame.IsSaddlePoint profile ↔
      surface.game.IsSaddlePoint profile := by
  simpa using
    bridge.implTraceGame_equivalence_surface.isSaddlePoint_iff profile

/-! ## Finite pure-frontier runtime values -/

/-- The finite maximin value of the implementation trace game for a pure
frontier adequacy bridge.  The finite instances are constructed from the
checked program rather than installed globally. -/
noncomputable def pureImplTraceGameSecurityLevel
    {program : WFProgram Player L} [FiniteDomains program]
    {Impl : Machine Player}
    {R : Machine.StochasticRefinement Impl
      (ToEventGraph.PrimitiveMachine (ToEventGraph.compile program.core))}
    (bridge : RuntimeTraceAdequacy program
      (pureFrontierTraceSurface program) R)
    (player : Player) : ℝ := by
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
  exact bridge.implTraceGame.securityLevel player

/-- Price of anarchy of a trace-adequate implementation game over the finite
pure-frontier strategy space. -/
noncomputable def pureImplTraceGamePriceOfAnarchy
    {program : WFProgram Player L} [FiniteDomains program]
    {Impl : Machine Player}
    {R : Machine.StochasticRefinement Impl
      (ToEventGraph.PrimitiveMachine (ToEventGraph.compile program.core))}
    (bridge : RuntimeTraceAdequacy program
      (pureFrontierTraceSurface program) R)
    (hNash : ∃ profile : program.PureFrontierProfile,
      bridge.implTraceGame.IsNash profile) : ℝ := by
  classical
  letI : ∀ who, Fintype (program.PureFrontierStrategy who) :=
    fun who => program.pureFrontierStrategyFintype who
  letI : Fintype (pureFrontierTraceSurface program).game.Profile := by
    change Fintype program.PureFrontierProfile
    infer_instance
  exact bridge.implTraceGame.priceOfAnarchy hNash

/-- Price of stability of a trace-adequate implementation game over the finite
pure-frontier strategy space. -/
noncomputable def pureImplTraceGamePriceOfStability
    {program : WFProgram Player L} [FiniteDomains program]
    {Impl : Machine Player}
    {R : Machine.StochasticRefinement Impl
      (ToEventGraph.PrimitiveMachine (ToEventGraph.compile program.core))}
    (bridge : RuntimeTraceAdequacy program
      (pureFrontierTraceSurface program) R)
    (hNash : ∃ profile : program.PureFrontierProfile,
      bridge.implTraceGame.IsNash profile) : ℝ := by
  classical
  letI : ∀ who, Fintype (program.PureFrontierStrategy who) :=
    fun who => program.pureFrontierStrategyFintype who
  letI : Fintype (pureFrontierTraceSurface program).game.Profile := by
    change Fintype program.PureFrontierProfile
    infer_instance
  exact bridge.implTraceGame.priceOfStability hNash

end RuntimeTraceAdequacy

end WFProgram

end Vegas
