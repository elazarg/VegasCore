/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Frontier.SolutionConcepts
import GameTheory.Concepts.Equilibrium.NashCorrelatedEq
import GameTheory.Concepts.Correlation.CorrelatedNashMixed

/-!
# Solution-concept vocabulary

This module exposes the checked-program solution-concept surface for completed
frontier games.  The definitions live next to the canonical frontier game
construction; this file is the theorem-index entry point.
-/

namespace Vegas

namespace Theorems
namespace SolutionConcepts

open GameTheory

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

namespace WFProgram

/-! ## Pure frontier claims -/

/-- Pure frontier Nash is exactly Nash for the pure frontier game's expected
utility preference relation. Preference-parametric variants live on
`KernelGame`; this theorem pins the expected-utility specialization for checked
programs. -/
theorem pure_frontier_nash_iff_nash_for_eu_pref
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) :
    program.PureFrontierNash profile ↔
      program.PureFrontierNashFor
        program.PureFrontierEuPref profile := by
  exact
    GameTheory.KernelGame.IsNash_iff_IsNashFor_eu
      program.pureFrontierGame profile

/-- Pure frontier best response is exactly best response for the pure frontier
game's expected-utility preference relation. -/
theorem pure_frontier_best_response_iff_best_response_for_eu_pref
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (player : P) (profile : program.PureFrontierProfile)
    (strategy : program.PureFrontierStrategy player) :
    program.PureFrontierBestResponse player profile strategy ↔
      program.PureFrontierBestResponseFor
        program.PureFrontierEuPref player profile strategy := by
  exact
    GameTheory.KernelGame.IsBestResponse_iff_IsBestResponseFor_eu
      program.pureFrontierGame player profile strategy

/-- Pure frontier dominance is exactly dominance for the pure frontier game's
expected-utility preference relation. -/
theorem pure_frontier_dominant_iff_dominant_for_eu_pref
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (player : P) (strategy : program.PureFrontierStrategy player) :
    program.PureFrontierDominant player strategy ↔
      program.PureFrontierDominantFor
        program.PureFrontierEuPref player strategy := by
  exact
    GameTheory.KernelGame.IsDominant_iff_IsDominantFor_eu
      program.pureFrontierGame player strategy

/-- Pure frontier strict Nash is exactly strict Nash for the pure frontier
game's expected-utility strict preference relation. -/
theorem pure_frontier_strict_nash_iff_strict_nash_for_eu_pref
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) :
    program.PureFrontierStrictNash profile ↔
      program.PureFrontierStrictNashFor
        program.PureFrontierEuStrictPref profile := by
  exact
    GameTheory.KernelGame.IsStrictNash_iff_IsStrictNashFor_eu
      program.pureFrontierGame profile

/-- Pure frontier strict dominance is exactly strict dominance for the pure
frontier game's expected-utility strict preference relation. -/
theorem pure_frontier_strict_dominant_iff_strict_dominant_for_eu_pref
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (player : P) (strategy : program.PureFrontierStrategy player) :
    program.PureFrontierStrictDominant player strategy ↔
      program.PureFrontierStrictDominantFor
        program.PureFrontierEuStrictPref player strategy := by
  exact
    GameTheory.KernelGame.IsStrictDominant_iff_IsStrictDominantFor_eu
      program.pureFrontierGame player strategy

/-- Pure frontier correlated equilibrium is exactly correlated equilibrium
for the pure frontier game's expected-utility preference relation. -/
theorem pure_frontier_correlated_eq_iff_correlated_eq_for_eu_pref
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierCorrelatedProfile) :
    program.PureFrontierCorrelatedEq profile ↔
      program.PureFrontierCorrelatedEqFor
        program.PureFrontierEuPref profile := by
  exact
    GameTheory.KernelGame.IsCorrelatedEq_iff_IsCorrelatedEqFor_eu
      program.pureFrontierGame profile

/-- Pure frontier coarse correlated equilibrium is exactly coarse correlated
equilibrium for the pure frontier game's expected-utility preference
relation. -/
theorem pure_frontier_coarse_correlated_eq_iff_coarse_correlated_eq_for_eu_pref
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierCorrelatedProfile) :
    program.PureFrontierCoarseCorrelatedEq profile ↔
      program.PureFrontierCoarseCorrelatedEqFor
        program.PureFrontierEuPref profile := by
  exact
    GameTheory.KernelGame.IsCoarseCorrelatedEq_iff_IsCoarseCorrelatedEqFor_eu
      program.pureFrontierGame profile

/-- A pure frontier Nash equilibrium, read as a point-mass distribution over
pure frontier profiles, is a correlated equilibrium. -/
theorem pure_frontier_nash_is_correlated_eq
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    {profile : program.PureFrontierProfile}
    (hNash : program.PureFrontierNash profile) :
    program.PureFrontierCorrelatedEq (PMF.pure profile) := by
  have hNash' : program.pureFrontierGame.IsNash profile := by
    simpa [Vegas.WFProgram.PureFrontierNash] using hNash
  simpa [Vegas.WFProgram.PureFrontierCorrelatedEq] using
    GameTheory.KernelGame.nash_pure_isCorrelatedEq
      (G := program.pureFrontierGame) hNash'

/-- A pure frontier Nash equilibrium, read as a point-mass distribution over
pure frontier profiles, is a coarse correlated equilibrium. -/
theorem pure_frontier_nash_is_coarse_correlated_eq
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    {profile : program.PureFrontierProfile}
    (hNash : program.PureFrontierNash profile) :
    program.PureFrontierCoarseCorrelatedEq (PMF.pure profile) := by
  have hNash' : program.pureFrontierGame.IsNash profile := by
    simpa [Vegas.WFProgram.PureFrontierNash] using hNash
  simpa [Vegas.WFProgram.PureFrontierCoarseCorrelatedEq] using
    GameTheory.KernelGame.nash_pure_isCoarseCorrelatedEq
      (G := program.pureFrontierGame) hNash'

/-- Every pure frontier correlated equilibrium is a pure frontier coarse
correlated equilibrium. -/
theorem pure_frontier_correlated_eq_is_coarse_correlated_eq
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    {profile : program.PureFrontierCorrelatedProfile}
    (hCE : program.PureFrontierCorrelatedEq profile) :
    program.PureFrontierCoarseCorrelatedEq profile := by
  have hCE' : program.pureFrontierGame.IsCorrelatedEq profile := by
    simpa [Vegas.WFProgram.PureFrontierCorrelatedEq] using hCE
  simpa [Vegas.WFProgram.PureFrontierCoarseCorrelatedEq] using
    GameTheory.KernelGame.IsCorrelatedEq.toCoarseCorrelatedEq hCE'

/-- A pure profile whose components are dominant frontier strategies is a
frontier Nash equilibrium. -/
theorem dominant_profile_is_pure_frontier_nash
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile)
    (hdom :
      ∀ player, program.PureFrontierDominant player (profile player)) :
    program.PureFrontierNash profile :=
  program.pureFrontier_dominant_profile_is_nash profile hdom

/-- A pure profile whose components are strictly dominant frontier strategies
is the unique pure frontier Nash equilibrium. -/
theorem strict_dominant_profile_unique_pure_frontier_nash
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (profile other : program.PureFrontierProfile)
    (hdom :
      ∀ player, program.PureFrontierStrictDominant player
        (profile player))
    (hother : program.PureFrontierNash other) :
    other = profile :=
  program.pureFrontier_strictDominant_unique_nash profile other hdom
    hother

/-- A pure profile whose components are strictly dominant frontier strategies
is a pure frontier Nash equilibrium. -/
theorem strict_dominant_profile_is_pure_frontier_nash
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile)
    (hdom :
      ∀ player, program.PureFrontierStrictDominant player
        (profile player)) :
    program.PureFrontierNash profile :=
  program.pureFrontier_strictDominant_profile_is_nash profile hdom

/-- A dominance-solvable pure frontier game has a unique pure Nash
equilibrium. -/
theorem dominance_solvable_unique_pure_frontier_nash
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (h : program.PureFrontierDominanceSolvable) :
    ∃! profile : program.PureFrontierProfile,
      program.PureFrontierNash profile :=
  program.pureFrontier_dominanceSolvable_exists_unique_nash h

/-- The dominant profile selected by pure-frontier dominance solvability is a
pure frontier Nash equilibrium. -/
theorem dominance_solvable_profile_is_pure_frontier_nash
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (h : program.PureFrontierDominanceSolvable) :
    program.PureFrontierNash
      (program.pureFrontierDominantProfile h) :=
  program.pureFrontier_dominanceSolvable_is_nash h

/-- Any pure frontier Nash equilibrium of a dominance-solvable game is the
selected dominant profile. -/
theorem dominance_solvable_pure_frontier_nash_unique
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (h : program.PureFrontierDominanceSolvable)
    {profile : program.PureFrontierProfile}
    (hNash : program.PureFrontierNash profile) :
    profile = program.pureFrontierDominantProfile h :=
  program.pureFrontier_dominanceSolvable_nash_unique h hNash

/-- Pure frontier Nash equilibria are ε-Nash for every nonnegative ε. -/
theorem pure_frontier_nash_is_epsilon_nash
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    {profile : program.PureFrontierProfile}
    (hNash : program.PureFrontierNash profile)
    {ε : ℝ} (hε : ε ≥ 0) :
    program.PureFrontierεNash ε profile :=
  program.pureFrontier_nash_is_epsilonNash hNash hε

/-- Pure frontier Nash strategies are rationalizable. -/
theorem pure_frontier_nash_strategy_rationalizable
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    {profile : program.PureFrontierProfile}
    (hNash : program.PureFrontierNash profile)
    (player : P) :
    program.PureFrontierRationalizable player (profile player) :=
  program.pureFrontier_nash_rationalizable hNash player

/-- A global maximizer of an exact pure-frontier potential is a pure frontier
Nash equilibrium. -/
theorem exact_potential_maximizer_is_pure_frontier_nash
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    {potential : program.PureFrontierProfile → ℝ}
    {profile : program.PureFrontierProfile}
    (hpotential : program.PureFrontierExactPotential potential)
    (hmax : ∀ other, potential profile ≥ potential other) :
    program.PureFrontierNash profile :=
  program.pureFrontier_exactPotential_nash_of_maximizer hpotential hmax

/-- Finite pure frontier games have security strategies for each player. -/
theorem pure_frontier_security_strategy_exists
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (player : P) :
    ∃ strategy : program.PureFrontierStrategy player,
      program.pureFrontierWorstCaseEU player strategy =
        program.pureFrontierSecurityLevel player :=
  program.pureFrontier_exists_securityStrategy player

/-- Pure frontier guarantees are monotone in the guaranteed lower bound. -/
theorem pure_frontier_guarantees_mono
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    {player : P} {strategy : program.PureFrontierStrategy player}
    {value lower : ℝ}
    (hlower : lower ≤ value)
    (hguarantees :
      program.PureFrontierGuarantees player strategy value) :
    program.PureFrontierGuarantees player strategy lower :=
  program.pureFrontier_guarantees_mono hlower hguarantees

/-- A pure frontier strategy guarantees its finite worst-case expected
utility. -/
theorem pure_frontier_worst_case_guarantees
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (player : P) (strategy : program.PureFrontierStrategy player) :
    program.PureFrontierGuarantees player strategy
      (program.pureFrontierWorstCaseEU player strategy) :=
  program.pureFrontier_worstCaseEU_guarantees player strategy

/-- Worst pure-frontier Nash welfare is bounded by best pure-frontier Nash
welfare. -/
theorem pure_frontier_worst_nash_welfare_le_best_nash_welfare
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (hNash : ∃ profile : program.PureFrontierProfile,
      program.PureFrontierNash profile) :
    program.pureFrontierWorstNashWelfare hNash ≤
      program.pureFrontierBestNashWelfare hNash := by
  classical
  letI : ∀ player, Fintype (program.PureFrontierStrategy player) :=
    fun player => program.pureFrontierStrategyFintype player
  simpa [Vegas.WFProgram.pureFrontierWorstNashWelfare,
    Vegas.WFProgram.pureFrontierBestNashWelfare] using
    program.pureFrontierGame.worstNashWelfare_le_bestNashWelfare hNash

/-- Best pure-frontier Nash welfare is bounded by optimal pure-frontier
welfare when social welfare is bounded above. -/
theorem pure_frontier_best_nash_welfare_le_optimal_welfare
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (hNash : ∃ profile : program.PureFrontierProfile,
      program.PureFrontierNash profile)
    (hbdd :
      BddAbove (Set.range
        (fun profile : program.PureFrontierProfile =>
          program.pureFrontierSocialWelfare profile))) :
    program.pureFrontierBestNashWelfare hNash ≤
      program.pureFrontierOptimalWelfare := by
  classical
  letI : ∀ player, Fintype (program.PureFrontierStrategy player) :=
    fun player => program.pureFrontierStrategyFintype player
  simpa [Vegas.WFProgram.pureFrontierBestNashWelfare,
    Vegas.WFProgram.pureFrontierOptimalWelfare,
    Vegas.WFProgram.pureFrontierSocialWelfare] using
    program.pureFrontierGame.bestNashWelfare_le_optimalWelfare
      hNash hbdd

/-- Pure frontier price of stability is at least one when the standard
positive-denominator hypotheses hold. -/
theorem pure_frontier_one_le_price_of_stability
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (hNash : ∃ profile : program.PureFrontierProfile,
      program.PureFrontierNash profile)
    (hbest : 0 < program.pureFrontierBestNashWelfare hNash)
    (hbest_le_opt :
      program.pureFrontierBestNashWelfare hNash ≤
        program.pureFrontierOptimalWelfare) :
    1 ≤ program.pureFrontierPriceOfStability hNash := by
  classical
  letI : ∀ player, Fintype (program.PureFrontierStrategy player) :=
    fun player => program.pureFrontierStrategyFintype player
  simpa [Vegas.WFProgram.pureFrontierPriceOfStability,
    Vegas.WFProgram.pureFrontierBestNashWelfare,
    Vegas.WFProgram.pureFrontierOptimalWelfare] using
    program.pureFrontierGame.one_le_priceOfStability
      hNash hbest hbest_le_opt

/-- Pure frontier price of anarchy is at least one when the standard
positive-denominator hypotheses hold. -/
theorem pure_frontier_one_le_price_of_anarchy
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (hNash : ∃ profile : program.PureFrontierProfile,
      program.PureFrontierNash profile)
    (hworst : 0 < program.pureFrontierWorstNashWelfare hNash)
    (hworst_le_opt :
      program.pureFrontierWorstNashWelfare hNash ≤
        program.pureFrontierOptimalWelfare) :
    1 ≤ program.pureFrontierPriceOfAnarchy hNash := by
  classical
  letI : ∀ player, Fintype (program.PureFrontierStrategy player) :=
    fun player => program.pureFrontierStrategyFintype player
  simpa [Vegas.WFProgram.pureFrontierPriceOfAnarchy,
    Vegas.WFProgram.pureFrontierWorstNashWelfare,
    Vegas.WFProgram.pureFrontierOptimalWelfare] using
    program.pureFrontierGame.one_le_priceOfAnarchy
      hNash hworst hworst_le_opt

/-- Pure frontier price of stability is at most price of anarchy whenever the
standard positive-denominator hypotheses hold. -/
theorem pure_frontier_price_of_stability_le_price_of_anarchy
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (hNash : ∃ profile : program.PureFrontierProfile,
      program.PureFrontierNash profile)
    (hopt : 0 ≤ program.pureFrontierOptimalWelfare)
    (hworst : 0 < program.pureFrontierWorstNashWelfare hNash) :
    program.pureFrontierPriceOfStability hNash ≤
      program.pureFrontierPriceOfAnarchy hNash := by
  classical
  letI : ∀ player, Fintype (program.PureFrontierStrategy player) :=
    fun player => program.pureFrontierStrategyFintype player
  simpa [Vegas.WFProgram.pureFrontierPriceOfStability,
    Vegas.WFProgram.pureFrontierPriceOfAnarchy,
    Vegas.WFProgram.pureFrontierOptimalWelfare,
    Vegas.WFProgram.pureFrontierWorstNashWelfare,
    Vegas.WFProgram.pureFrontierBestNashWelfare] using
    program.pureFrontierGame.priceOfStability_le_priceOfAnarchy
      hNash hopt hworst

/-- In a pure frontier team game, every Pareto-efficient profile is Nash. -/
theorem pure_frontier_team_pareto_efficient_is_nash
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    [Inhabited P]
    {profile : program.PureFrontierProfile}
    (hteam : program.PureFrontierTeamGame)
    (hpareto : program.PureFrontierParetoEfficient profile) :
    program.PureFrontierNash profile :=
  KernelGame.IsTeamGame.pareto_isNash
    (G := program.pureFrontierGame) hteam hpareto

/-- A pure frontier social-welfare maximizer is Pareto-efficient. -/
theorem pure_frontier_welfare_maximizer_is_pareto_efficient
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    {profile : program.PureFrontierProfile}
    (hmax :
      ∀ other,
        program.pureFrontierSocialWelfare other ≤
          program.pureFrontierSocialWelfare profile) :
    program.PureFrontierParetoEfficient profile := by
  exact
    KernelGame.welfareMax_isParetoEfficient
      (G := program.pureFrontierGame) hmax

/-- In a pure frontier team game, every social-welfare maximizer is Nash. -/
theorem pure_frontier_team_welfare_maximizer_is_nash
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    [Inhabited P]
    {profile : program.PureFrontierProfile}
    (hteam : program.PureFrontierTeamGame)
    (hmax :
      ∀ other,
        program.pureFrontierSocialWelfare other ≤
          program.pureFrontierSocialWelfare profile) :
    program.PureFrontierNash profile :=
  hteam.welfareMax_isNash hmax

/-- In a pure frontier team game, best Nash welfare equals optimal welfare. -/
theorem pure_frontier_team_best_nash_welfare_eq_optimal_welfare
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    [Inhabited P]
    (hteam : program.PureFrontierTeamGame)
    (hNash : ∃ profile : program.PureFrontierProfile,
      program.PureFrontierNash profile) :
    program.pureFrontierBestNashWelfare hNash =
      program.pureFrontierOptimalWelfare := by
  classical
  letI : ∀ player, Fintype (program.PureFrontierStrategy player) :=
    fun player => program.pureFrontierStrategyFintype player
  simpa [Vegas.WFProgram.pureFrontierBestNashWelfare,
    Vegas.WFProgram.pureFrontierOptimalWelfare] using
    hteam.bestNashWelfare_eq_optimalWelfare hNash

/-- In a pure frontier team game with positive optimal welfare, price of
stability is one. -/
theorem pure_frontier_team_price_of_stability_eq_one
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    [Inhabited P]
    (hteam : program.PureFrontierTeamGame)
    (hNash : ∃ profile : program.PureFrontierProfile,
      program.PureFrontierNash profile)
    (hopt : 0 < program.pureFrontierOptimalWelfare) :
    program.pureFrontierPriceOfStability hNash = 1 := by
  classical
  letI : ∀ player, Fintype (program.PureFrontierStrategy player) :=
    fun player => program.pureFrontierStrategyFintype player
  simpa [Vegas.WFProgram.pureFrontierPriceOfStability,
    Vegas.WFProgram.pureFrontierBestNashWelfare,
    Vegas.WFProgram.pureFrontierOptimalWelfare] using
    hteam.priceOfStability_eq_one hNash hopt

/-- In two-player pure frontier zero-sum vocabulary, saddle points and Nash
equilibria coincide. -/
theorem pure_frontier_saddle_point_iff_nash
    (program : Vegas.WFProgram (Fin 2) L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) :
    program.PureFrontierSaddlePoint profile ↔
      program.PureFrontierNash profile :=
  program.pureFrontier_saddlePoint_iff_nash profile

/-! ## Finite pure and terminal-public existence claims -/

/-- Bounded mixed Nash existence for the completed pure frontier payoff game. -/
theorem mixed_pure_frontier_nash_exists_of_bounded
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    {C : P → ℝ}
    (hbd :
      ∀ player outcome,
        |program.pureFrontierGame.utility outcome player| ≤ C player) :
    ∃ mixed : program.MixedPureFrontierProfile,
      program.MixedPureFrontierNash mixed :=
  program.mixedPureFrontier_nash_exists_of_bounded hbd

/-- A bounded mixed-pure frontier Nash equilibrium induces a correlated
equilibrium on pure frontier profiles via the independent product law. -/
theorem mixed_pure_frontier_nash_is_pure_frontier_correlated_eq_of_bounded
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    {C : P → ℝ}
    (hbd :
      ∀ player outcome,
        |program.pureFrontierGame.utility outcome player| ≤ C player)
    {profile : program.MixedPureFrontierProfile}
    (hNash : program.MixedPureFrontierNash profile) :
    program.PureFrontierCorrelatedEq
      (Math.PMFProduct.pmfPi profile) := by
  have hNash' :
      program.pureFrontierGame.mixedExtension.IsNash profile := by
    simpa [Vegas.WFProgram.MixedPureFrontierNash,
      Vegas.WFProgram.MixedPureFrontierProfile,
      Vegas.WFProgram.mixedPureFrontierGame,
      Vegas.WFProgram.pureFrontierGame,
      Vegas.ToEventGraph.FrontierGameSemantics.mixedPureGame] using hNash
  simpa [Vegas.WFProgram.PureFrontierCorrelatedEq] using
    GameTheory.KernelGame.mixed_nash_isCorrelatedEq_of_bounded
      (G := program.pureFrontierGame) profile hNash' hbd

/-- A bounded mixed-pure frontier Nash equilibrium induces a coarse correlated
equilibrium on pure frontier profiles via the independent product law. -/
theorem mixed_pure_frontier_nash_is_pure_frontier_coarse_correlated_eq_of_bounded
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    {C : P → ℝ}
    (hbd :
      ∀ player outcome,
        |program.pureFrontierGame.utility outcome player| ≤ C player)
    {profile : program.MixedPureFrontierProfile}
    (hNash : program.MixedPureFrontierNash profile) :
    program.PureFrontierCoarseCorrelatedEq
      (Math.PMFProduct.pmfPi profile) :=
  pure_frontier_correlated_eq_is_coarse_correlated_eq program
    (mixed_pure_frontier_nash_is_pure_frontier_correlated_eq_of_bounded
      program hbd hNash)

/-- Bounded correlated-equilibrium existence for the completed pure frontier
payoff game. -/
theorem pure_frontier_correlated_eq_exists_of_bounded
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    {C : P → ℝ}
    (hbd :
      ∀ player outcome,
        |program.pureFrontierGame.utility outcome player| ≤ C player) :
    ∃ correlated : program.PureFrontierCorrelatedProfile,
      program.PureFrontierCorrelatedEq correlated :=
  program.pureFrontier_correlatedEq_exists_of_bounded hbd

/-- Bounded coarse-correlated-equilibrium existence for the completed pure
frontier payoff game. -/
theorem pure_frontier_coarse_correlated_eq_exists_of_bounded
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    {C : P → ℝ}
    (hbd :
      ∀ player outcome,
        |program.pureFrontierGame.utility outcome player| ≤ C player) :
    ∃ correlated : program.PureFrontierCorrelatedProfile,
      program.PureFrontierCoarseCorrelatedEq correlated :=
  program.pureFrontier_coarseCorrelatedEq_exists_of_bounded hbd

/-- Mixed Nash existence for the finite terminal-public frontier game. -/
theorem mixed_pure_terminal_public_frontier_nash_exists
    (program : Vegas.WFProgram P L) [FiniteDomains program] :
    ∃ mixed : program.MixedPureTerminalPublicFrontierProfile,
      program.MixedPureTerminalPublicFrontierNash mixed :=
  program.mixedPureTerminalPublicFrontier_nash_exists

/-- Correlated-equilibrium existence for the finite terminal-public frontier
game. -/
theorem pure_terminal_public_frontier_correlated_eq_exists
    (program : Vegas.WFProgram P L) [FiniteDomains program] :
    ∃ correlated : program.PureTerminalPublicFrontierCorrelatedProfile,
      program.PureTerminalPublicFrontierCorrelatedEq correlated :=
  program.pureTerminalPublicFrontier_correlatedEq_exists

/-- Coarse-correlated-equilibrium existence for the finite terminal-public
frontier game. -/
theorem pure_terminal_public_frontier_coarse_correlated_eq_exists
    (program : Vegas.WFProgram P L) [FiniteDomains program] :
    ∃ correlated : program.PureTerminalPublicFrontierCorrelatedProfile,
      program.PureTerminalPublicFrontierCoarseCorrelatedEq correlated :=
  program.pureTerminalPublicFrontier_coarseCorrelatedEq_exists

/-! ## Behavioral frontier claims -/

/-- Behavioral frontier Nash is exactly Nash for the behavioral frontier
game's expected-utility preference relation. -/
theorem behavioral_frontier_nash_iff_nash_for_eu_pref
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    program.BehavioralFrontierNash profile ↔
      program.BehavioralFrontierNashFor
        program.BehavioralFrontierEuPref profile := by
  exact
    GameTheory.KernelGame.IsNash_iff_IsNashFor_eu
      program.behavioralFrontierGame profile

/-- Behavioral frontier best response is exactly best response for the
behavioral frontier game's expected-utility preference relation. -/
theorem behavioral_frontier_best_response_iff_best_response_for_eu_pref
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (player : P) (profile : program.BehavioralFrontierProfile)
    (strategy : program.BehavioralFrontierStrategy player) :
    program.BehavioralFrontierBestResponse player profile strategy ↔
      program.BehavioralFrontierBestResponseFor
        program.BehavioralFrontierEuPref player profile strategy := by
  exact
    GameTheory.KernelGame.IsBestResponse_iff_IsBestResponseFor_eu
      program.behavioralFrontierGame player profile strategy

/-- Behavioral frontier dominance is exactly dominance for the behavioral
frontier game's expected-utility preference relation. -/
theorem behavioral_frontier_dominant_iff_dominant_for_eu_pref
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (player : P) (strategy : program.BehavioralFrontierStrategy player) :
    program.BehavioralFrontierDominant player strategy ↔
      program.BehavioralFrontierDominantFor
        program.BehavioralFrontierEuPref player strategy := by
  exact
    GameTheory.KernelGame.IsDominant_iff_IsDominantFor_eu
      program.behavioralFrontierGame player strategy

/-- Behavioral frontier strict Nash is exactly strict Nash for the behavioral
frontier game's expected-utility strict preference relation. -/
theorem behavioral_frontier_strict_nash_iff_strict_nash_for_eu_pref
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    program.BehavioralFrontierStrictNash profile ↔
      program.BehavioralFrontierStrictNashFor
        program.BehavioralFrontierEuStrictPref profile := by
  exact
    GameTheory.KernelGame.IsStrictNash_iff_IsStrictNashFor_eu
      program.behavioralFrontierGame profile

/-- Behavioral frontier strict dominance is exactly strict dominance for the
behavioral frontier game's expected-utility strict preference relation. -/
theorem behavioral_frontier_strict_dominant_iff_strict_dominant_for_eu_pref
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (player : P) (strategy : program.BehavioralFrontierStrategy player) :
    program.BehavioralFrontierStrictDominant player strategy ↔
      program.BehavioralFrontierStrictDominantFor
        program.BehavioralFrontierEuStrictPref player strategy := by
  exact
    GameTheory.KernelGame.IsStrictDominant_iff_IsStrictDominantFor_eu
      program.behavioralFrontierGame player strategy

/-- Behavioral frontier correlated equilibrium is exactly correlated
equilibrium for the behavioral frontier game's expected-utility preference
relation. -/
theorem behavioral_frontier_correlated_eq_iff_correlated_eq_for_eu_pref
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierCorrelatedProfile) :
    program.BehavioralFrontierCorrelatedEq profile ↔
      program.BehavioralFrontierCorrelatedEqFor
        program.BehavioralFrontierEuPref profile := by
  exact
    GameTheory.KernelGame.IsCorrelatedEq_iff_IsCorrelatedEqFor_eu
      program.behavioralFrontierGame profile

/-- Behavioral frontier coarse correlated equilibrium is exactly coarse
correlated equilibrium for the behavioral frontier game's expected-utility
preference relation. -/
theorem behavioral_frontier_coarse_correlated_eq_iff_coarse_correlated_eq_for_eu_pref
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierCorrelatedProfile) :
    program.BehavioralFrontierCoarseCorrelatedEq profile ↔
      program.BehavioralFrontierCoarseCorrelatedEqFor
        program.BehavioralFrontierEuPref profile := by
  exact
    GameTheory.KernelGame.IsCoarseCorrelatedEq_iff_IsCoarseCorrelatedEqFor_eu
      program.behavioralFrontierGame profile

/-- A behavioral frontier Nash equilibrium, read as a point-mass distribution
over behavioral frontier profiles, is a correlated equilibrium. -/
theorem behavioral_frontier_nash_is_correlated_eq
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    {profile : program.BehavioralFrontierProfile}
    (hNash : program.BehavioralFrontierNash profile) :
    program.BehavioralFrontierCorrelatedEq (PMF.pure profile) := by
  have hNash' : program.behavioralFrontierGame.IsNash profile := by
    simpa [Vegas.WFProgram.BehavioralFrontierNash] using hNash
  simpa [Vegas.WFProgram.BehavioralFrontierCorrelatedEq] using
    GameTheory.KernelGame.nash_pure_isCorrelatedEq
      (G := program.behavioralFrontierGame) hNash'

/-- A behavioral frontier Nash equilibrium, read as a point-mass distribution
over behavioral frontier profiles, is a coarse correlated equilibrium. -/
theorem behavioral_frontier_nash_is_coarse_correlated_eq
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    {profile : program.BehavioralFrontierProfile}
    (hNash : program.BehavioralFrontierNash profile) :
    program.BehavioralFrontierCoarseCorrelatedEq (PMF.pure profile) := by
  have hNash' : program.behavioralFrontierGame.IsNash profile := by
    simpa [Vegas.WFProgram.BehavioralFrontierNash] using hNash
  simpa [Vegas.WFProgram.BehavioralFrontierCoarseCorrelatedEq] using
    GameTheory.KernelGame.nash_pure_isCoarseCorrelatedEq
      (G := program.behavioralFrontierGame) hNash'

/-- Every behavioral frontier correlated equilibrium is a behavioral frontier
coarse correlated equilibrium. -/
theorem behavioral_frontier_correlated_eq_is_coarse_correlated_eq
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    {profile : program.BehavioralFrontierCorrelatedProfile}
    (hCE : program.BehavioralFrontierCorrelatedEq profile) :
    program.BehavioralFrontierCoarseCorrelatedEq profile := by
  have hCE' : program.behavioralFrontierGame.IsCorrelatedEq profile := by
    simpa [Vegas.WFProgram.BehavioralFrontierCorrelatedEq] using hCE
  simpa [Vegas.WFProgram.BehavioralFrontierCoarseCorrelatedEq] using
    GameTheory.KernelGame.IsCorrelatedEq.toCoarseCorrelatedEq hCE'

/-- A behavioral profile whose components are dominant frontier strategies is a
frontier Nash equilibrium. -/
theorem dominant_profile_is_behavioral_frontier_nash
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile)
    (hdom :
      ∀ player, program.BehavioralFrontierDominant player
        (profile player)) :
    program.BehavioralFrontierNash profile :=
  program.behavioralFrontier_dominant_profile_is_nash profile hdom

/-- A behavioral profile whose components are strictly dominant frontier
strategies is the unique behavioral frontier Nash equilibrium. -/
theorem strict_dominant_profile_unique_behavioral_frontier_nash
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (profile other : program.BehavioralFrontierProfile)
    (hdom :
      ∀ player, program.BehavioralFrontierStrictDominant player
        (profile player))
    (hother : program.BehavioralFrontierNash other) :
    other = profile :=
  program.behavioralFrontier_strictDominant_unique_nash profile other
    hdom hother

/-- A behavioral profile whose components are strictly dominant frontier
strategies is a behavioral frontier Nash equilibrium. -/
theorem strict_dominant_profile_is_behavioral_frontier_nash
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile)
    (hdom :
      ∀ player, program.BehavioralFrontierStrictDominant player
        (profile player)) :
    program.BehavioralFrontierNash profile :=
  program.behavioralFrontier_strictDominant_profile_is_nash profile hdom

/-- A dominance-solvable behavioral frontier game has a unique behavioral Nash
equilibrium. -/
theorem dominance_solvable_unique_behavioral_frontier_nash
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (h : program.BehavioralFrontierDominanceSolvable) :
    ∃! profile : program.BehavioralFrontierProfile,
      program.BehavioralFrontierNash profile :=
  program.behavioralFrontier_dominanceSolvable_exists_unique_nash h

/-- The dominant profile selected by behavioral-frontier dominance solvability
is a behavioral frontier Nash equilibrium. -/
theorem dominance_solvable_profile_is_behavioral_frontier_nash
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (h : program.BehavioralFrontierDominanceSolvable) :
    program.BehavioralFrontierNash
      (program.behavioralFrontierDominantProfile h) :=
  program.behavioralFrontier_dominanceSolvable_is_nash h

/-- Any behavioral frontier Nash equilibrium of a dominance-solvable game is
the selected dominant profile. -/
theorem dominance_solvable_behavioral_frontier_nash_unique
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (h : program.BehavioralFrontierDominanceSolvable)
    {profile : program.BehavioralFrontierProfile}
    (hNash : program.BehavioralFrontierNash profile) :
    profile = program.behavioralFrontierDominantProfile h :=
  program.behavioralFrontier_dominanceSolvable_nash_unique h hNash

/-- Behavioral frontier Nash equilibria are ε-Nash for every nonnegative ε. -/
theorem behavioral_frontier_nash_is_epsilon_nash
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    {profile : program.BehavioralFrontierProfile}
    (hNash : program.BehavioralFrontierNash profile)
    {ε : ℝ} (hε : ε ≥ 0) :
    program.BehavioralFrontierεNash ε profile :=
  program.behavioralFrontier_nash_is_epsilonNash hNash hε

/-- A global maximizer of an exact behavioral-frontier potential is a
behavioral frontier Nash equilibrium. -/
theorem exact_potential_maximizer_is_behavioral_frontier_nash
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    {potential : program.BehavioralFrontierProfile → ℝ}
    {profile : program.BehavioralFrontierProfile}
    (hpotential : program.BehavioralFrontierExactPotential potential)
    (hmax : ∀ other, potential profile ≥ potential other) :
    program.BehavioralFrontierNash profile :=
  program.behavioralFrontier_exactPotential_nash_of_maximizer hpotential
    hmax

/-- In a behavioral frontier team game, every Pareto-efficient profile is
Nash. -/
theorem behavioral_frontier_team_pareto_efficient_is_nash
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    [Inhabited P]
    {profile : program.BehavioralFrontierProfile}
    (hteam : program.BehavioralFrontierTeamGame)
    (hpareto : program.BehavioralFrontierParetoEfficient profile) :
    program.BehavioralFrontierNash profile :=
  KernelGame.IsTeamGame.pareto_isNash
    (G := program.behavioralFrontierGame) hteam hpareto

/-- A behavioral frontier social-welfare maximizer is Pareto-efficient. -/
theorem behavioral_frontier_welfare_maximizer_is_pareto_efficient
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    {profile : program.BehavioralFrontierProfile}
    (hmax :
      ∀ other,
        program.behavioralFrontierSocialWelfare other ≤
          program.behavioralFrontierSocialWelfare profile) :
    program.BehavioralFrontierParetoEfficient profile := by
  exact
    KernelGame.welfareMax_isParetoEfficient
      (G := program.behavioralFrontierGame) hmax

/-- In a behavioral frontier team game, every social-welfare maximizer is
Nash. -/
theorem behavioral_frontier_team_welfare_maximizer_is_nash
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    [Inhabited P]
    {profile : program.BehavioralFrontierProfile}
    (hteam : program.BehavioralFrontierTeamGame)
    (hmax :
      ∀ other,
        program.behavioralFrontierSocialWelfare other ≤
          program.behavioralFrontierSocialWelfare profile) :
    program.BehavioralFrontierNash profile :=
  hteam.welfareMax_isNash hmax

/-- Behavioral frontier guarantees are monotone in the guaranteed lower
bound. -/
theorem behavioral_frontier_guarantees_mono
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    {player : P}
    {strategy : program.BehavioralFrontierStrategy player}
    {value lower : ℝ}
    (hlower : lower ≤ value)
    (hguarantees :
      program.BehavioralFrontierGuarantees player strategy value) :
    program.BehavioralFrontierGuarantees player strategy lower :=
  program.behavioralFrontier_guarantees_mono hlower hguarantees

/-- In two-player behavioral frontier zero-sum vocabulary, saddle points and
Nash equilibria coincide. -/
theorem behavioral_frontier_saddle_point_iff_nash
    (program : Vegas.WFProgram (Fin 2) L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    program.BehavioralFrontierSaddlePoint profile ↔
      program.BehavioralFrontierNash profile :=
  program.behavioralFrontier_saddlePoint_iff_nash profile

/-- With bounded compiled payoff utilities, the canonical mixed-pure to
behavioral Kuhn simulation yields behavioral Nash existence. -/
theorem behavioral_frontier_nash_exists_of_bounded
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    {C : P → ℝ}
    (hbd :
      ∀ player outcome,
        |program.pureFrontierGame.utility outcome player| ≤ C player) :
    ∃ behavioral : program.BehavioralFrontierProfile,
      program.BehavioralFrontierNash behavioral :=
  program.behavioralFrontier_nash_exists_of_bounded
    program.canonicalMixedPureToBehavioralFrontierDeviationSimulation hbd

end WFProgram

end SolutionConcepts
end Theorems

end Vegas
