/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Frontier.Games
import GameTheory.Core.GameProperties
import GameTheory.Concepts.Equilibrium.ApproximateNash
import GameTheory.Concepts.Dominance.DominanceSolvability
import GameTheory.Concepts.ZeroSum.Minimax
import GameTheory.Concepts.Potential.PotentialFIP
import GameTheory.Concepts.Welfare.PriceOfAnarchy
import GameTheory.Concepts.Dominance.Rationalizability
import GameTheory.Concepts.ZeroSum.SecurityStrategy
import GameTheory.Concepts.Dominance.StrictDominance
import GameTheory.Concepts.Welfare.WelfareTheorems

/-!
# Frontier solution concepts

Program-facing solution-concept vocabulary for the completed frontier games
generated from checked Vegas programs.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

namespace WFProgram

/-! ## Pure frontier game -/

def PureFrontierEuPref
    (program : WFProgram P L) [FiniteDomains program] :
    P → PMF program.pureFrontierGame.Outcome →
      PMF program.pureFrontierGame.Outcome → Prop :=
  program.pureFrontierGame.euPref

def PureFrontierEuStrictPref
    (program : WFProgram P L) [FiniteDomains program] :
    P → PMF program.pureFrontierGame.Outcome →
      PMF program.pureFrontierGame.Outcome → Prop :=
  program.pureFrontierGame.euStrictPref

def PureFrontierNashFor
    (program : WFProgram P L) [FiniteDomains program]
    (pref :
      P → PMF program.pureFrontierGame.Outcome →
        PMF program.pureFrontierGame.Outcome → Prop)
    (profile : program.PureFrontierProfile) : Prop :=
  program.pureFrontierGame.IsNashFor pref profile

def PureFrontierBestResponseFor
    (program : WFProgram P L) [FiniteDomains program]
    (pref :
      P → PMF program.pureFrontierGame.Outcome →
        PMF program.pureFrontierGame.Outcome → Prop)
    (player : P) (profile : program.PureFrontierProfile)
    (strategy : program.PureFrontierStrategy player) : Prop :=
  program.pureFrontierGame.IsBestResponseFor
    pref player profile strategy

def PureFrontierDominantFor
    (program : WFProgram P L) [FiniteDomains program]
    (pref :
      P → PMF program.pureFrontierGame.Outcome →
        PMF program.pureFrontierGame.Outcome → Prop)
    (player : P) (strategy : program.PureFrontierStrategy player) : Prop :=
  program.pureFrontierGame.IsDominantFor pref player strategy

def PureFrontierStrictNashFor
    (program : WFProgram P L) [FiniteDomains program]
    (strictPref :
      P → PMF program.pureFrontierGame.Outcome →
        PMF program.pureFrontierGame.Outcome → Prop)
    (profile : program.PureFrontierProfile) : Prop :=
  program.pureFrontierGame.IsStrictNashFor strictPref profile

def PureFrontierStrictDominantFor
    (program : WFProgram P L) [FiniteDomains program]
    (strictPref :
      P → PMF program.pureFrontierGame.Outcome →
        PMF program.pureFrontierGame.Outcome → Prop)
    (player : P) (strategy : program.PureFrontierStrategy player) :
    Prop :=
  program.pureFrontierGame.IsStrictDominantFor
    strictPref player strategy

def PureFrontierCorrelatedEqFor
    (program : WFProgram P L) [FiniteDomains program]
    (pref :
      P → PMF program.pureFrontierGame.Outcome →
        PMF program.pureFrontierGame.Outcome → Prop)
    (profile : program.PureFrontierCorrelatedProfile) : Prop :=
  program.pureFrontierGame.IsCorrelatedEqFor pref profile

def PureFrontierCoarseCorrelatedEqFor
    (program : WFProgram P L) [FiniteDomains program]
    (pref :
      P → PMF program.pureFrontierGame.Outcome →
        PMF program.pureFrontierGame.Outcome → Prop)
    (profile : program.PureFrontierCorrelatedProfile) : Prop :=
  program.pureFrontierGame.IsCoarseCorrelatedEqFor pref profile

def PureFrontierBestResponse
    (program : WFProgram P L) [FiniteDomains program]
    (player : P) (profile : program.PureFrontierProfile)
    (strategy : program.PureFrontierStrategy player) : Prop :=
  program.pureFrontierGame.IsBestResponse player profile strategy

def PureFrontierDominant
    (program : WFProgram P L) [FiniteDomains program]
    (player : P) (strategy : program.PureFrontierStrategy player) : Prop :=
  program.pureFrontierGame.IsDominant player strategy

def PureFrontierStrictNash
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) : Prop :=
  program.pureFrontierGame.IsStrictNash profile

def PureFrontierStrictDominant
    (program : WFProgram P L) [FiniteDomains program]
    (player : P) (strategy : program.PureFrontierStrategy player) : Prop :=
  program.pureFrontierGame.IsStrictDominant player strategy

def PureFrontierWeaklyDominates
    (program : WFProgram P L) [FiniteDomains program]
    (player : P)
    (left right : program.PureFrontierStrategy player) : Prop :=
  program.pureFrontierGame.WeaklyDominates player left right

def PureFrontierStrictlyDominates
    (program : WFProgram P L) [FiniteDomains program]
    (player : P)
    (left right : program.PureFrontierStrategy player) : Prop :=
  program.pureFrontierGame.StrictlyDominates player left right

def PureFrontierεNash
    (program : WFProgram P L) [FiniteDomains program]
    (ε : ℝ) (profile : program.PureFrontierProfile) : Prop :=
  program.pureFrontierGame.IsεNash ε profile

def PureFrontierεBestResponse
    (program : WFProgram P L) [FiniteDomains program]
    (ε : ℝ) (player : P) (profile : program.PureFrontierProfile)
    (strategy : program.PureFrontierStrategy player) : Prop :=
  program.pureFrontierGame.IsεBestResponse ε player profile strategy

def PureFrontierParetoDominates
    (program : WFProgram P L) [FiniteDomains program]
    (left right : program.PureFrontierProfile) : Prop :=
  program.pureFrontierGame.ParetoDominates left right

def PureFrontierParetoEfficient
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) : Prop :=
  program.pureFrontierGame.IsParetoEfficient profile

def PureFrontierIndividuallyRational
    (program : WFProgram P L) [FiniteDomains program]
    (reservation : P → ℝ) (profile : program.PureFrontierProfile) : Prop :=
  program.pureFrontierGame.IsIndividuallyRational reservation profile

def PureFrontierSurvives
    (program : WFProgram P L) [FiniteDomains program]
    (round : Nat) (player : P)
    (strategy : program.PureFrontierStrategy player) : Prop :=
  program.pureFrontierGame.Survives round player strategy

def PureFrontierRationalizable
    (program : WFProgram P L) [FiniteDomains program]
    (player : P) (strategy : program.PureFrontierStrategy player) : Prop :=
  program.pureFrontierGame.IsRationalizable player strategy

def PureFrontierExactPotential
    (program : WFProgram P L) [FiniteDomains program]
    (potential : program.PureFrontierProfile → ℝ) : Prop :=
  program.pureFrontierGame.IsExactPotential potential

def PureFrontierOrdinalPotential
    (program : WFProgram P L) [FiniteDomains program]
    (potential : program.PureFrontierProfile → ℝ) : Prop :=
  program.pureFrontierGame.IsOrdinalPotential potential

noncomputable def pureFrontierSocialWelfare
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) : ℝ :=
  program.pureFrontierGame.socialWelfare profile

def PureFrontierConstantSum
    (program : WFProgram P L) [FiniteDomains program]
    (total : ℝ) : Prop :=
  program.pureFrontierGame.IsConstantSum total

def PureFrontierZeroSum
    (program : WFProgram P L) [FiniteDomains program] :
    Prop :=
  program.pureFrontierGame.IsZeroSum

def PureFrontierTeamGame
    (program : WFProgram P L) [FiniteDomains program] :
    Prop :=
  program.pureFrontierGame.IsTeamGame

theorem pureFrontier_dominant_profile_is_nash
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile)
    (hdom :
      ∀ player, program.PureFrontierDominant player (profile player)) :
    program.PureFrontierNash profile :=
  program.pureFrontierGame.dominant_is_nash profile hdom

theorem pureFrontier_strictDominant_profile_is_nash
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile)
    (hdom :
      ∀ player, program.PureFrontierStrictDominant player
        (profile player)) :
    program.PureFrontierNash profile :=
  program.pureFrontierGame.strictly_dominant_is_nash profile hdom

theorem pureFrontier_strictDominant_unique_nash
    (program : WFProgram P L) [FiniteDomains program]
    (profile other : program.PureFrontierProfile)
    (hdom :
      ∀ player, program.PureFrontierStrictDominant player
        (profile player))
    (hother : program.PureFrontierNash other) :
    other = profile :=
  program.pureFrontierGame.strictly_dominant_unique_nash
    profile hdom other hother

theorem pureFrontier_nash_is_epsilonNash
    (program : WFProgram P L) [FiniteDomains program]
    {profile : program.PureFrontierProfile}
    (hNash : program.PureFrontierNash profile)
    {ε : ℝ} (hε : ε ≥ 0) :
    program.PureFrontierεNash ε profile :=
  KernelGame.IsεNash.of_isNash program.pureFrontierGame hNash hε

theorem pureFrontier_nash_rationalizable
    (program : WFProgram P L) [FiniteDomains program]
    {profile : program.PureFrontierProfile}
    (hNash : program.PureFrontierNash profile)
    (player : P) :
    program.PureFrontierRationalizable player (profile player) := by
  classical
  letI : ∀ player, Fintype (program.PureFrontierStrategy player) :=
    fun player => program.pureFrontierStrategyFintype player
  exact hNash.isRationalizable player

theorem pureFrontier_exactPotential_nash_of_maximizer
    (program : WFProgram P L) [FiniteDomains program]
    {potential : program.PureFrontierProfile → ℝ}
    {profile : program.PureFrontierProfile}
    (hpotential : program.PureFrontierExactPotential potential)
    (hmax : ∀ other, potential profile ≥ potential other) :
    program.PureFrontierNash profile :=
  hpotential.nash_of_maximizer hmax

/-! ## Pure frontier guarantees, security, and welfare -/

def PureFrontierDominanceSolvable
    (program : WFProgram P L) [FiniteDomains program] : Prop :=
  program.pureFrontierGame.IsDominantStrategySolvable

noncomputable def pureFrontierDominantProfile
    (program : WFProgram P L) [FiniteDomains program]
    (h : program.PureFrontierDominanceSolvable) :
    program.PureFrontierProfile :=
  h.dominantProfile program.pureFrontierGame

theorem pureFrontier_dominanceSolvable_is_nash
    (program : WFProgram P L) [FiniteDomains program]
    (h : program.PureFrontierDominanceSolvable) :
    program.PureFrontierNash
      (program.pureFrontierDominantProfile h) :=
  h.isNash program.pureFrontierGame

theorem pureFrontier_dominanceSolvable_nash_unique
    (program : WFProgram P L) [FiniteDomains program]
    (h : program.PureFrontierDominanceSolvable)
    {profile : program.PureFrontierProfile}
    (hNash : program.PureFrontierNash profile) :
    profile = program.pureFrontierDominantProfile h :=
  h.nash_unique program.pureFrontierGame hNash

theorem pureFrontier_dominanceSolvable_exists_unique_nash
    (program : WFProgram P L) [FiniteDomains program]
    (h : program.PureFrontierDominanceSolvable) :
    ∃! profile : program.PureFrontierProfile,
      program.PureFrontierNash profile :=
  h.exists_unique_nash program.pureFrontierGame

def PureFrontierGuarantees
    (program : WFProgram P L) [FiniteDomains program]
    (player : P) (strategy : program.PureFrontierStrategy player)
    (value : ℝ) : Prop :=
  program.pureFrontierGame.Guarantees player strategy value

theorem pureFrontier_guarantees_mono
    (program : WFProgram P L) [FiniteDomains program]
    {player : P} {strategy : program.PureFrontierStrategy player}
    {value lower : ℝ}
    (hlower : lower ≤ value)
    (hguarantees :
      program.PureFrontierGuarantees player strategy value) :
    program.PureFrontierGuarantees player strategy lower :=
  KernelGame.Guarantees.mono hlower hguarantees

noncomputable def pureFrontierWorstCaseEUInf
    (program : WFProgram P L) [FiniteDomains program]
    (player : P) (strategy : program.PureFrontierStrategy player) :
    ℝ :=
  program.pureFrontierGame.worstCaseEUInf player strategy

noncomputable def pureFrontierSecurityLevelSup
    (program : WFProgram P L) [FiniteDomains program]
    (player : P) : ℝ :=
  program.pureFrontierGame.securityLevelSup player

noncomputable def pureFrontierWorstCaseEU
    (program : WFProgram P L) [FiniteDomains program]
    (player : P) (strategy : program.PureFrontierStrategy player) :
    ℝ := by
  classical
  letI : ∀ player, Fintype (program.PureFrontierStrategy player) :=
    fun player => program.pureFrontierStrategyFintype player
  letI : ∀ player, Nonempty (program.PureFrontierStrategy player) :=
    fun player => program.pureFrontierStrategyNonempty player
  exact program.pureFrontierGame.worstCaseEU player strategy

noncomputable def pureFrontierSecurityLevel
    (program : WFProgram P L) [FiniteDomains program]
    (player : P) : ℝ := by
  classical
  letI : ∀ player, Fintype (program.PureFrontierStrategy player) :=
    fun player => program.pureFrontierStrategyFintype player
  letI : ∀ player, Nonempty (program.PureFrontierStrategy player) :=
    fun player => program.pureFrontierStrategyNonempty player
  exact program.pureFrontierGame.securityLevel player

theorem pureFrontier_worstCaseEU_guarantees
    (program : WFProgram P L) [FiniteDomains program]
    (player : P) (strategy : program.PureFrontierStrategy player) :
    program.PureFrontierGuarantees player strategy
      (program.pureFrontierWorstCaseEU player strategy) := by
  let decEqP : DecidableEq P := inferInstance
  classical
  letI : ∀ player, Fintype (program.PureFrontierStrategy player) :=
    fun player => program.pureFrontierStrategyFintype player
  letI : ∀ player, Nonempty (program.PureFrontierStrategy player) :=
    fun player => program.pureFrontierStrategyNonempty player
  unfold PureFrontierGuarantees pureFrontierWorstCaseEU KernelGame.Guarantees
  intro profile
  have hdec : decEqP = Classical.decEq P := Subsingleton.elim _ _
  have h :
      program.pureFrontierGame.eu
          (@Function.update P program.pureFrontierGame.Strategy
            (Classical.decEq P) profile player strategy) player ≥
        program.pureFrontierGame.worstCaseEU player strategy :=
    program.pureFrontierGame.worstCaseEU_guarantees player strategy profile
  rw [← hdec] at h
  exact h

theorem pureFrontier_exists_securityStrategy
    (program : WFProgram P L) [FiniteDomains program]
    (player : P) :
    ∃ strategy : program.PureFrontierStrategy player,
      program.pureFrontierWorstCaseEU player strategy =
        program.pureFrontierSecurityLevel player := by
  classical
  letI : ∀ player, Fintype (program.PureFrontierStrategy player) :=
    fun player => program.pureFrontierStrategyFintype player
  letI : ∀ player, Nonempty (program.PureFrontierStrategy player) :=
    fun player => program.pureFrontierStrategyNonempty player
  change
    ∃ strategy : program.PureFrontierStrategy player,
      program.pureFrontierGame.worstCaseEU player strategy =
        program.pureFrontierGame.securityLevel player
  exact
    program.pureFrontierGame.exists_securityStrategy player

noncomputable def pureFrontierOptimalWelfare
    (program : WFProgram P L) [FiniteDomains program] :
    ℝ :=
  program.pureFrontierGame.optimalWelfare

noncomputable def pureFrontierBestNashWelfare
    (program : WFProgram P L) [FiniteDomains program]
    (hNash : ∃ profile : program.PureFrontierProfile,
      program.PureFrontierNash profile) :
    ℝ := by
  classical
  letI : ∀ player, Fintype (program.PureFrontierStrategy player) :=
    fun player => program.pureFrontierStrategyFintype player
  exact program.pureFrontierGame.bestNashWelfare hNash

noncomputable def pureFrontierWorstNashWelfare
    (program : WFProgram P L) [FiniteDomains program]
    (hNash : ∃ profile : program.PureFrontierProfile,
      program.PureFrontierNash profile) :
    ℝ := by
  classical
  letI : ∀ player, Fintype (program.PureFrontierStrategy player) :=
    fun player => program.pureFrontierStrategyFintype player
  exact program.pureFrontierGame.worstNashWelfare hNash

noncomputable def pureFrontierPriceOfAnarchy
    (program : WFProgram P L) [FiniteDomains program]
    (hNash : ∃ profile : program.PureFrontierProfile,
      program.PureFrontierNash profile) :
    ℝ := by
  classical
  letI : ∀ player, Fintype (program.PureFrontierStrategy player) :=
    fun player => program.pureFrontierStrategyFintype player
  exact program.pureFrontierGame.priceOfAnarchy hNash

noncomputable def pureFrontierPriceOfStability
    (program : WFProgram P L) [FiniteDomains program]
    (hNash : ∃ profile : program.PureFrontierProfile,
      program.PureFrontierNash profile) :
    ℝ := by
  classical
  letI : ∀ player, Fintype (program.PureFrontierStrategy player) :=
    fun player => program.pureFrontierStrategyFintype player
  exact program.pureFrontierGame.priceOfStability hNash

/-! ## Two-player pure frontier minimax vocabulary -/

def PureFrontierSaddlePoint
    (program : WFProgram (Fin 2) L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) : Prop :=
  program.pureFrontierGame.IsSaddlePoint profile

theorem pureFrontier_saddlePoint_iff_nash
    (program : WFProgram (Fin 2) L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) :
    program.PureFrontierSaddlePoint profile ↔
      program.PureFrontierNash profile :=
  program.pureFrontierGame.isSaddlePoint_iff_isNash profile

/-! ## Behavioral frontier game -/

def BehavioralFrontierEuPref
    (program : WFProgram P L) [FiniteDomains program] :
    P → PMF program.behavioralFrontierGame.Outcome →
      PMF program.behavioralFrontierGame.Outcome → Prop :=
  program.behavioralFrontierGame.euPref

def BehavioralFrontierEuStrictPref
    (program : WFProgram P L) [FiniteDomains program] :
    P → PMF program.behavioralFrontierGame.Outcome →
      PMF program.behavioralFrontierGame.Outcome → Prop :=
  program.behavioralFrontierGame.euStrictPref

def BehavioralFrontierNashFor
    (program : WFProgram P L) [FiniteDomains program]
    (pref :
      P → PMF program.behavioralFrontierGame.Outcome →
        PMF program.behavioralFrontierGame.Outcome → Prop)
    (profile : program.BehavioralFrontierProfile) : Prop :=
  program.behavioralFrontierGame.IsNashFor pref profile

def BehavioralFrontierBestResponseFor
    (program : WFProgram P L) [FiniteDomains program]
    (pref :
      P → PMF program.behavioralFrontierGame.Outcome →
        PMF program.behavioralFrontierGame.Outcome → Prop)
    (player : P) (profile : program.BehavioralFrontierProfile)
    (strategy : program.BehavioralFrontierStrategy player) : Prop :=
  program.behavioralFrontierGame.IsBestResponseFor
    pref player profile strategy

def BehavioralFrontierDominantFor
    (program : WFProgram P L) [FiniteDomains program]
    (pref :
      P → PMF program.behavioralFrontierGame.Outcome →
        PMF program.behavioralFrontierGame.Outcome → Prop)
    (player : P) (strategy : program.BehavioralFrontierStrategy player) :
    Prop :=
  program.behavioralFrontierGame.IsDominantFor pref player strategy

def BehavioralFrontierStrictNashFor
    (program : WFProgram P L) [FiniteDomains program]
    (strictPref :
      P → PMF program.behavioralFrontierGame.Outcome →
        PMF program.behavioralFrontierGame.Outcome → Prop)
    (profile : program.BehavioralFrontierProfile) : Prop :=
  program.behavioralFrontierGame.IsStrictNashFor strictPref profile

def BehavioralFrontierStrictDominantFor
    (program : WFProgram P L) [FiniteDomains program]
    (strictPref :
      P → PMF program.behavioralFrontierGame.Outcome →
        PMF program.behavioralFrontierGame.Outcome → Prop)
    (player : P) (strategy : program.BehavioralFrontierStrategy player) :
    Prop :=
  program.behavioralFrontierGame.IsStrictDominantFor
    strictPref player strategy

def BehavioralFrontierCorrelatedEqFor
    (program : WFProgram P L) [FiniteDomains program]
    (pref :
      P → PMF program.behavioralFrontierGame.Outcome →
        PMF program.behavioralFrontierGame.Outcome → Prop)
    (profile : program.BehavioralFrontierCorrelatedProfile) : Prop :=
  program.behavioralFrontierGame.IsCorrelatedEqFor pref profile

def BehavioralFrontierCoarseCorrelatedEqFor
    (program : WFProgram P L) [FiniteDomains program]
    (pref :
      P → PMF program.behavioralFrontierGame.Outcome →
        PMF program.behavioralFrontierGame.Outcome → Prop)
    (profile : program.BehavioralFrontierCorrelatedProfile) : Prop :=
  program.behavioralFrontierGame.IsCoarseCorrelatedEqFor pref profile

def BehavioralFrontierWeaklyDominates
    (program : WFProgram P L) [FiniteDomains program]
    (player : P)
    (left right : program.BehavioralFrontierStrategy player) : Prop :=
  program.behavioralFrontierGame.WeaklyDominates player left right

def BehavioralFrontierStrictlyDominates
    (program : WFProgram P L) [FiniteDomains program]
    (player : P)
    (left right : program.BehavioralFrontierStrategy player) : Prop :=
  program.behavioralFrontierGame.StrictlyDominates player left right

def BehavioralFrontierεNash
    (program : WFProgram P L) [FiniteDomains program]
    (ε : ℝ) (profile : program.BehavioralFrontierProfile) : Prop :=
  program.behavioralFrontierGame.IsεNash ε profile

def BehavioralFrontierεBestResponse
    (program : WFProgram P L) [FiniteDomains program]
    (ε : ℝ) (player : P)
    (profile : program.BehavioralFrontierProfile)
    (strategy : program.BehavioralFrontierStrategy player) : Prop :=
  program.behavioralFrontierGame.IsεBestResponse ε player profile strategy

def BehavioralFrontierParetoDominates
    (program : WFProgram P L) [FiniteDomains program]
    (left right : program.BehavioralFrontierProfile) : Prop :=
  program.behavioralFrontierGame.ParetoDominates left right

def BehavioralFrontierParetoEfficient
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) : Prop :=
  program.behavioralFrontierGame.IsParetoEfficient profile

def BehavioralFrontierIndividuallyRational
    (program : WFProgram P L) [FiniteDomains program]
    (reservation : P → ℝ)
    (profile : program.BehavioralFrontierProfile) : Prop :=
  program.behavioralFrontierGame.IsIndividuallyRational
    reservation profile

def BehavioralFrontierSurvives
    (program : WFProgram P L) [FiniteDomains program]
    (round : Nat) (player : P)
    (strategy : program.BehavioralFrontierStrategy player) : Prop :=
  program.behavioralFrontierGame.Survives round player strategy

def BehavioralFrontierRationalizable
    (program : WFProgram P L) [FiniteDomains program]
    (player : P)
    (strategy : program.BehavioralFrontierStrategy player) : Prop :=
  program.behavioralFrontierGame.IsRationalizable player strategy

def BehavioralFrontierExactPotential
    (program : WFProgram P L) [FiniteDomains program]
    (potential : program.BehavioralFrontierProfile → ℝ) : Prop :=
  program.behavioralFrontierGame.IsExactPotential potential

def BehavioralFrontierOrdinalPotential
    (program : WFProgram P L) [FiniteDomains program]
    (potential : program.BehavioralFrontierProfile → ℝ) : Prop :=
  program.behavioralFrontierGame.IsOrdinalPotential potential

noncomputable def behavioralFrontierSocialWelfare
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) : ℝ :=
  program.behavioralFrontierGame.socialWelfare profile

def BehavioralFrontierConstantSum
    (program : WFProgram P L) [FiniteDomains program]
    (total : ℝ) : Prop :=
  program.behavioralFrontierGame.IsConstantSum total

def BehavioralFrontierZeroSum
    (program : WFProgram P L) [FiniteDomains program] :
    Prop :=
  program.behavioralFrontierGame.IsZeroSum

def BehavioralFrontierTeamGame
    (program : WFProgram P L) [FiniteDomains program] :
    Prop :=
  program.behavioralFrontierGame.IsTeamGame

/-! ## Behavioral frontier guarantees and dominance solvability -/

def BehavioralFrontierDominanceSolvable
    (program : WFProgram P L) [FiniteDomains program] : Prop :=
  program.behavioralFrontierGame.IsDominantStrategySolvable

noncomputable def behavioralFrontierDominantProfile
    (program : WFProgram P L) [FiniteDomains program]
    (h : program.BehavioralFrontierDominanceSolvable) :
    program.BehavioralFrontierProfile :=
  h.dominantProfile program.behavioralFrontierGame

theorem behavioralFrontier_dominanceSolvable_is_nash
    (program : WFProgram P L) [FiniteDomains program]
    (h : program.BehavioralFrontierDominanceSolvable) :
    program.BehavioralFrontierNash
      (program.behavioralFrontierDominantProfile h) :=
  h.isNash program.behavioralFrontierGame

theorem behavioralFrontier_dominanceSolvable_nash_unique
    (program : WFProgram P L) [FiniteDomains program]
    (h : program.BehavioralFrontierDominanceSolvable)
    {profile : program.BehavioralFrontierProfile}
    (hNash : program.BehavioralFrontierNash profile) :
    profile = program.behavioralFrontierDominantProfile h :=
  h.nash_unique program.behavioralFrontierGame hNash

theorem behavioralFrontier_dominanceSolvable_exists_unique_nash
    (program : WFProgram P L) [FiniteDomains program]
    (h : program.BehavioralFrontierDominanceSolvable) :
    ∃! profile : program.BehavioralFrontierProfile,
      program.BehavioralFrontierNash profile :=
  h.exists_unique_nash program.behavioralFrontierGame

def BehavioralFrontierGuarantees
    (program : WFProgram P L) [FiniteDomains program]
    (player : P)
    (strategy : program.BehavioralFrontierStrategy player)
    (value : ℝ) : Prop :=
  program.behavioralFrontierGame.Guarantees player strategy value

theorem behavioralFrontier_guarantees_mono
    (program : WFProgram P L) [FiniteDomains program]
    {player : P}
    {strategy : program.BehavioralFrontierStrategy player}
    {value lower : ℝ}
    (hlower : lower ≤ value)
    (hguarantees :
      program.BehavioralFrontierGuarantees player strategy value) :
    program.BehavioralFrontierGuarantees player strategy lower :=
  KernelGame.Guarantees.mono hlower hguarantees

noncomputable def behavioralFrontierWorstCaseEUInf
    (program : WFProgram P L) [FiniteDomains program]
    (player : P)
    (strategy : program.BehavioralFrontierStrategy player) :
    ℝ :=
  program.behavioralFrontierGame.worstCaseEUInf player strategy

noncomputable def behavioralFrontierSecurityLevelSup
    (program : WFProgram P L) [FiniteDomains program]
    (player : P) : ℝ :=
  program.behavioralFrontierGame.securityLevelSup player

/-! ## Two-player behavioral frontier minimax vocabulary -/

def BehavioralFrontierSaddlePoint
    (program : WFProgram (Fin 2) L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) : Prop :=
  program.behavioralFrontierGame.IsSaddlePoint profile

theorem behavioralFrontier_saddlePoint_iff_nash
    (program : WFProgram (Fin 2) L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    program.BehavioralFrontierSaddlePoint profile ↔
      program.BehavioralFrontierNash profile :=
  program.behavioralFrontierGame.isSaddlePoint_iff_isNash profile

theorem behavioralFrontier_dominant_profile_is_nash
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile)
    (hdom :
      ∀ player, program.BehavioralFrontierDominant player
        (profile player)) :
    program.BehavioralFrontierNash profile :=
  program.behavioralFrontierGame.dominant_is_nash profile hdom

theorem behavioralFrontier_strictDominant_profile_is_nash
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile)
    (hdom :
      ∀ player, program.BehavioralFrontierStrictDominant player
        (profile player)) :
    program.BehavioralFrontierNash profile :=
  program.behavioralFrontierGame.strictly_dominant_is_nash profile hdom

theorem behavioralFrontier_strictDominant_unique_nash
    (program : WFProgram P L) [FiniteDomains program]
    (profile other : program.BehavioralFrontierProfile)
    (hdom :
      ∀ player, program.BehavioralFrontierStrictDominant player
        (profile player))
    (hother : program.BehavioralFrontierNash other) :
    other = profile :=
  program.behavioralFrontierGame.strictly_dominant_unique_nash
    profile hdom other hother

theorem behavioralFrontier_nash_is_epsilonNash
    (program : WFProgram P L) [FiniteDomains program]
    {profile : program.BehavioralFrontierProfile}
    (hNash : program.BehavioralFrontierNash profile)
    {ε : ℝ} (hε : ε ≥ 0) :
    program.BehavioralFrontierεNash ε profile :=
  KernelGame.IsεNash.of_isNash program.behavioralFrontierGame hNash hε

theorem behavioralFrontier_exactPotential_nash_of_maximizer
    (program : WFProgram P L) [FiniteDomains program]
    {potential : program.BehavioralFrontierProfile → ℝ}
    {profile : program.BehavioralFrontierProfile}
    (hpotential : program.BehavioralFrontierExactPotential potential)
    (hmax : ∀ other, potential profile ≥ potential other) :
    program.BehavioralFrontierNash profile :=
  hpotential.nash_of_maximizer hmax

end WFProgram

end Vegas
