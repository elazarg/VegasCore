import Vegas.Core.Theorems.SolutionConcepts
import Vegas.Examples.MatchingPennies
import Vegas.Examples.PrisonersDilemma
import GameTheory.Concepts.BestResponse
import GameTheory.Concepts.PotentialGame
import GameTheory.Concepts.TeamGame
import GameTheory.Concepts.ZeroSum
import GameTheory.Concepts.BinaryMixed
import GameTheory.Languages.NFG.Compile
import GameTheory.Auctions.Vickrey

/-!
# Solution-concept examples

Small theorem checks for the reusable game-theory vocabulary used by compiled
Vegas frontier games, plus one external Vickrey smoke test for the shared
`GameTheory` mechanism library.
-/

open scoped BigOperators

namespace Vegas
namespace Examples
namespace SolutionConcepts

open GameTheory
open Math.Probability

/-! ## Deterministic kernel-game checks -/

namespace PrisonersKernel

inductive Action where
  | cooperate
  | defect
deriving DecidableEq, Fintype, Repr

open Action

/-- Prisoner's Dilemma payoffs with `defect` dominant for both players. -/
def utility (profile : Fin 2 → Action) : Payoff (Fin 2) := fun player =>
  let rowPayoff : ℝ :=
    match profile 0, profile 1 with
    | cooperate, cooperate => 3
    | cooperate, defect => 0
    | defect, cooperate => 5
    | defect, defect => 1
  let colPayoff : ℝ :=
    match profile 0, profile 1 with
    | cooperate, cooperate => 3
    | cooperate, defect => 5
    | defect, cooperate => 0
    | defect, defect => 1
  if player = 0 then rowPayoff else colPayoff

noncomputable def nfg : NFG.NFGGame (Fin 2) (fun _ => Action) where
  Outcome := Fin 2 → Action
  outcome := id
  utility := utility

noncomputable def game : KernelGame (Fin 2) :=
  nfg.toKernelGame

def defectProfile : game.Profile := fun _ => defect

theorem defect_isDominant (player : Fin 2) :
    game.IsDominant player defect := by
  intro profile alternative
  fin_cases player <;>
    cases h0 : profile 0 <;> cases h1 : profile 1 <;>
    cases alternative <;>
    simp [game, nfg, NFG.NFGGame.toKernelGame, KernelGame.eu, expect_pure,
      utility, h0, h1] <;>
    norm_num

theorem defect_isBestResponse
    (player : Fin 2) (profile : game.Profile) :
    game.IsBestResponse player profile defect :=
  fun alternative => defect_isDominant player profile alternative

theorem defectProfile_isNash : game.IsNash defectProfile :=
  KernelGame.dominant_is_nash game defectProfile
    (fun player => defect_isDominant player)

end PrisonersKernel

namespace MatchingPenniesKernel

inductive Coin where
  | heads
  | tails
deriving DecidableEq, Fintype, Repr

open Coin

private instance : Nonempty Coin := ⟨heads⟩

/-- Player 0 wants a match, player 1 wants a mismatch. -/
def utility (profile : Fin 2 → Coin) : Payoff (Fin 2) := fun player =>
  let row : ℝ := if profile 0 = profile 1 then 1 else -1
  if player = 0 then row else -row

noncomputable def nfg : NFG.NFGGame (Fin 2) (fun _ => Coin) where
  Outcome := Fin 2 → Coin
  outcome := id
  utility := utility

noncomputable def game : KernelGame (Fin 2) :=
  nfg.toKernelGame

theorem isZeroSum : game.IsZeroSum := by
  intro outcome
  cases h0 : outcome 0 <;> cases h1 : outcome 1 <;>
    simp [game, nfg, NFG.NFGGame.toKernelGame, utility, h0, h1]

theorem no_pure_nash (profile : game.Profile) :
    ¬ game.IsNash profile := by
  intro hNash
  cases h0 : profile 0 <;> cases h1 : profile 1
  · have hdev := hNash 1 tails
    simp [game, nfg, NFG.NFGGame.toKernelGame, KernelGame.eu, expect_pure,
      utility, h0, h1] at hdev
    norm_num at hdev
  · have hdev := hNash 0 tails
    simp [game, nfg, NFG.NFGGame.toKernelGame, KernelGame.eu, expect_pure,
      utility, h0, h1] at hdev
    norm_num at hdev
  · have hdev := hNash 0 heads
    simp [game, nfg, NFG.NFGGame.toKernelGame, KernelGame.eu, expect_pure,
      utility, h0, h1] at hdev
    norm_num at hdev
  · have hdev := hNash 1 heads
    simp [game, nfg, NFG.NFGGame.toKernelGame, KernelGame.eu, expect_pure,
      utility, h0, h1] at hdev
    norm_num at hdev

theorem player0_eu_neg_player1 (profile : game.Profile) :
    game.eu profile 0 = -game.eu profile 1 := by
  letI : Fintype game.Outcome := by
    change Fintype (Fin 2 → Coin)
    infer_instance
  exact isZeroSum.eu_neg profile

noncomputable instance : ∀ i : Fin 2, Nonempty (game.Strategy i) := fun _ => ⟨heads⟩
noncomputable instance : ∀ i : Fin 2, Fintype (game.Strategy i) :=
  fun _ => by change Fintype Coin; infer_instance
noncomputable instance : Finite game.Outcome := by
  change Finite (∀ _ : Fin 2, Coin); infer_instance
noncomputable instance : Finite game.mixedExtension.Outcome := by
  change Finite game.Outcome
  infer_instance

private def playerLabels : Fin 2 ≃ Bool where
  toFun i := if i = 0 then true else false
  invFun
    | true => 0
    | false => 1
  left_inv := by
    intro i
    fin_cases i <;> simp
  right_inv := by
    intro b
    cases b <;> simp

/-- The binary action labels for matching pennies: `true` is heads and `false`
is tails. -/
private def labels : KernelGame.BinaryActionLabels game where
  player := playerLabels
  toBool := fun _ =>
    { toFun := fun
        | heads => true
        | tails => false
      invFun := fun
        | true => heads
        | false => tails
      left_inv := by
        intro a
        cases a <;> rfl
      right_inv := by
        intro b
        cases b <;> rfl }

private def matchingPenniesLike : game.MatchingPenniesLike labels where
  scale := 1
  scale_pos := by norm_num
  eu_true := by
    intro a b
    cases a <;> cases b <;>
      simp [KernelGame.BinaryActionLabels.profile, KernelGame.BinaryActionLabels.action,
        KernelGame.BinaryActionLabels.playerOf, labels, playerLabels, game,
        nfg, NFG.NFGGame.toKernelGame, KernelGame.eu, expect_pure, utility]
  eu_false := by
    intro a b
    cases a <;> cases b <;>
      simp [KernelGame.BinaryActionLabels.profile, KernelGame.BinaryActionLabels.action,
        KernelGame.BinaryActionLabels.playerOf, labels, playerLabels, game,
        nfg, NFG.NFGGame.toKernelGame, KernelGame.eu, expect_pure, utility]

theorem uniform_mixed_balanced :
    game.IsUniformMixedBalanced :=
  KernelGame.MatchingPenniesLike.uniformMixed_balanced matchingPenniesLike

theorem uniform_mixed_nash :
    game.mixedExtension.IsNash game.uniformMixedProfile :=
  KernelGame.MatchingPenniesLike.uniformMixedProfile_isNash matchingPenniesLike

end MatchingPenniesKernel

namespace CoordinationKernel

inductive Venue where
  | opera
  | football
deriving DecidableEq, Fintype, Repr

open Venue

/-- A common-interest coordination game. -/
def utility (profile : Fin 2 → Venue) : Payoff (Fin 2) := fun _ =>
  if profile 0 = profile 1 then (1 : ℝ) else 0

noncomputable def nfg : NFG.NFGGame (Fin 2) (fun _ => Venue) where
  Outcome := Fin 2 → Venue
  outcome := id
  utility := utility

noncomputable def game : KernelGame (Fin 2) :=
  nfg.toKernelGame

def operaProfile : game.Profile := fun _ => opera

def footballProfile : game.Profile := fun _ => football

noncomputable def potential (profile : game.Profile) : ℝ :=
  game.eu profile 0

theorem operaProfile_isStrictNash :
    game.IsStrictNash operaProfile := by
  intro player alternative hne
  fin_cases player <;> cases alternative <;>
    simp [operaProfile, game, nfg, NFG.NFGGame.toKernelGame, KernelGame.eu,
      expect_pure, utility] at hne ⊢

theorem footballProfile_isStrictNash :
    game.IsStrictNash footballProfile := by
  intro player alternative hne
  fin_cases player <;> cases alternative <;>
    simp [footballProfile, game, nfg, NFG.NFGGame.toKernelGame, KernelGame.eu,
      expect_pure, utility] at hne ⊢

theorem isTeamGame : game.IsTeamGame := by
  intro outcome player other
  simp [game, nfg, NFG.NFGGame.toKernelGame, utility]

theorem exactPotential : game.IsExactPotential potential := by
  intro player profile alternative
  fin_cases player <;>
    cases h0 : profile 0 <;> cases h1 : profile 1 <;>
    cases alternative <;>
    simp [potential, game, nfg, NFG.NFGGame.toKernelGame, KernelGame.eu,
      expect_pure, utility, h0, h1]

theorem opera_potential_max (profile : game.Profile) :
    potential operaProfile ≥ potential profile := by
  cases h0 : profile 0 <;> cases h1 : profile 1 <;>
    simp [potential, operaProfile, game, nfg, NFG.NFGGame.toKernelGame,
      KernelGame.eu, expect_pure, utility, h0, h1]

theorem operaProfile_isNash_from_potential :
    game.IsNash operaProfile :=
  exactPotential.nash_of_maximizer opera_potential_max

end CoordinationKernel

namespace SecondPriceAuction

/-- A concrete two-bidder second-price auction instance for the shared
`GameTheory` Vickrey theorem surface. -/
def values : Fin 2 → ℝ
  | 0 => 10
  | 1 => 7

theorem truthful_isDominant (player : Fin 2) :
    (vickreyGame values).IsDominant player (values player) :=
  vickrey_truthful_isDominant values player

theorem truthful_isNash :
    (vickreyGame values).IsNash values :=
  vickrey_truthful_isNash values

theorem bidder0_value : values 0 = 10 := rfl

theorem bidder1_value : values 1 = 7 := rfl

end SecondPriceAuction

/-! ## Checked Vegas frontier games -/

example
    (profile :
      Vegas.Examples.PrisonersDilemma.checkedProgram.PureFrontierProfile)
    (hdom :
      ∀ player,
        Vegas.Examples.PrisonersDilemma.checkedProgram.PureFrontierDominant
          player (profile player)) :
    Vegas.Examples.PrisonersDilemma.checkedProgram.PureFrontierNash
      profile :=
  Vegas.Examples.PrisonersDilemma.checkedProgram
    |>.pureFrontier_dominant_profile_is_nash profile hdom

example
    (h :
      Vegas.Examples.PrisonersDilemma.checkedProgram.PureFrontierDominanceSolvable) :
    ∃! profile :
      Vegas.Examples.PrisonersDilemma.checkedProgram.PureFrontierProfile,
      Vegas.Examples.PrisonersDilemma.checkedProgram.PureFrontierNash
        profile :=
  Vegas.Examples.PrisonersDilemma.checkedProgram
    |>.pureFrontier_dominanceSolvable_exists_unique_nash h

example
    (player : Vegas.Examples.PrisonersDilemma.Player) :
    ∃ strategy :
      Vegas.Examples.PrisonersDilemma.checkedProgram.PureFrontierStrategy
        player,
      Vegas.Examples.PrisonersDilemma.checkedProgram.pureFrontierWorstCaseEU
          player strategy =
        Vegas.Examples.PrisonersDilemma.checkedProgram.pureFrontierSecurityLevel
          player :=
  Vegas.Examples.PrisonersDilemma.checkedProgram
    |>.pureFrontier_exists_securityStrategy player

example
    (profile :
      Vegas.Examples.matchingPenniesChecked.BehavioralFrontierProfile)
    (hNash :
      Vegas.Examples.matchingPenniesChecked.BehavioralFrontierNash profile) :
    Vegas.Examples.matchingPenniesChecked.BehavioralFrontierεNash 0
      profile :=
  Vegas.Examples.matchingPenniesChecked
    |>.behavioralFrontier_nash_is_epsilonNash hNash le_rfl

example
    (profile :
      Vegas.Examples.matchingPenniesChecked.BehavioralFrontierProfile)
    (hdom :
      ∀ player,
        Vegas.Examples.matchingPenniesChecked.BehavioralFrontierDominant
          player (profile player)) :
    Vegas.Examples.matchingPenniesChecked.BehavioralFrontierNash profile :=
  Vegas.Examples.matchingPenniesChecked
    |>.behavioralFrontier_dominant_profile_is_nash profile hdom

example
    {potential :
      Vegas.Examples.matchingPenniesChecked.BehavioralFrontierProfile → ℝ}
    {profile :
      Vegas.Examples.matchingPenniesChecked.BehavioralFrontierProfile}
    (hpotential :
      Vegas.Examples.matchingPenniesChecked.BehavioralFrontierExactPotential
        potential)
    (hmax : ∀ other, potential profile ≥ potential other) :
    Vegas.Examples.matchingPenniesChecked.BehavioralFrontierNash profile :=
  Vegas.Examples.matchingPenniesChecked
    |>.behavioralFrontier_exactPotential_nash_of_maximizer
      hpotential hmax

end SolutionConcepts
end Examples
end Vegas
