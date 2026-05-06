import Vegas.Examples.Prisoners
import Vegas.Examples.MatchingPennies
import Vegas.Examples.BattleOfTheSexes
import Vegas.Examples.MontyHall
import GameTheory.Concepts.BestResponse
import GameTheory.Concepts.PotentialGame
import GameTheory.Concepts.ZeroSum
import GameTheory.Auctions.Vickrey

/-!
# Solution-concept examples

Small kernel-game examples that exercise the reusable GameTheory solution
concepts used by Vegas: dominance, best response, Nash, strict Nash, zero-sum
games, potential games, and second-price auction truthfulness.
-/

open scoped BigOperators

namespace Vegas
namespace Examples
namespace SolutionConcepts

open GameTheory
open Math.Probability

/-- A deterministic strategic-form game whose outcome records the played profile.

Unlike `KernelGame.ofEU`, this keeps the outcome carrier small enough for
outcome-level predicates such as `IsZeroSum` and `IsTeamGame` to be meaningful
examples.
-/
noncomputable def deterministicProfileGame {ι : Type} (Strategy : ι → Type)
    (utility : (∀ i, Strategy i) → Payoff ι) : KernelGame ι where
  Strategy := Strategy
  Outcome := ∀ i, Strategy i
  utility := utility
  outcomeKernel := fun σ => PMF.pure σ

@[simp] theorem deterministicProfileGame_outcomeKernel {ι : Type} (Strategy : ι → Type)
    (utility : (∀ i, Strategy i) → Payoff ι) (σ : ∀ i, Strategy i) :
    (deterministicProfileGame Strategy utility).outcomeKernel σ = PMF.pure σ := rfl

@[simp] theorem deterministicProfileGame_eu {ι : Type} (Strategy : ι → Type)
    (utility : (∀ i, Strategy i) → Payoff ι) (σ : ∀ i, Strategy i) (i : ι) :
    (deterministicProfileGame Strategy utility).eu σ i = utility σ i := by
  simp [deterministicProfileGame, KernelGame.eu, expect_pure]

/-- A reusable check for zero-one win/loss payoff pairs. -/
theorem winLose_payoffs_sum_one (win : Bool) :
    (if win = true then (1 : Int) else 0) +
      (if win = true then (0 : Int) else 1) = 1 := by
  cases win <;> rfl

namespace PrisonersKernel

inductive Action where
  | cooperate
  | defect
deriving DecidableEq, Fintype, Repr

open Action

/-- Prisoner's Dilemma payoffs with `defect` weakly dominant for both players. -/
def utility (σ : Fin 2 → Action) : Payoff (Fin 2) := fun i =>
  let rowPayoff : ℝ :=
    match σ 0, σ 1 with
    | cooperate, cooperate => 3
    | cooperate, defect => 0
    | defect, cooperate => 5
    | defect, defect => 1
  let colPayoff : ℝ :=
    match σ 0, σ 1 with
    | cooperate, cooperate => 3
    | cooperate, defect => 5
    | defect, cooperate => 0
    | defect, defect => 1
  if i = 0 then rowPayoff else colPayoff

noncomputable def game : KernelGame (Fin 2) :=
  deterministicProfileGame (fun _ => Action) utility

def defectProfile : game.Profile := fun _ => defect

theorem defect_isDominant (who : Fin 2) : game.IsDominant who defect := by
  intro σ s'
  fin_cases who <;> cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases s' <;>
    simp [game, deterministicProfileGame, KernelGame.eu, expect_pure, utility, h0, h1] <;>
      norm_num

theorem defect_isBestResponse (who : Fin 2) (σ : game.Profile) :
    game.IsBestResponse who σ defect :=
  KernelGame.dominant_isBestResponse game who defect σ (defect_isDominant who)

theorem defect_defect_isNash : game.IsNash defectProfile :=
  KernelGame.dominant_is_nash game defectProfile (fun i => defect_isDominant i)

end PrisonersKernel

namespace MatchingPenniesKernel

inductive Coin where
  | heads
  | tails
deriving DecidableEq, Fintype, Repr

open Coin

/-- Player 0 wants a match, player 1 wants a mismatch. -/
def utility (σ : Fin 2 → Coin) : Payoff (Fin 2) := fun i =>
  let row : ℝ := if σ 0 = σ 1 then 1 else -1
  if i = 0 then row else -row

noncomputable def game : KernelGame (Fin 2) :=
  deterministicProfileGame (fun _ => Coin) utility

theorem isZeroSum : game.IsZeroSum := by
  intro ω
  cases h0 : ω 0 <;> cases h1 : ω 1 <;>
    simp [game, deterministicProfileGame, utility, h0, h1]

theorem no_pure_nash (σ : game.Profile) : ¬ game.IsNash σ := by
  intro h
  cases h0 : σ 0 <;> cases h1 : σ 1
  · have hdev := h 1 tails
    simp [game, deterministicProfileGame, KernelGame.eu, expect_pure, utility, h0, h1] at hdev
    norm_num at hdev
  · have hdev := h 0 tails
    simp [game, deterministicProfileGame, KernelGame.eu, expect_pure, utility, h0, h1] at hdev
    norm_num at hdev
  · have hdev := h 0 heads
    simp [game, deterministicProfileGame, KernelGame.eu, expect_pure, utility, h0, h1] at hdev
    norm_num at hdev
  · have hdev := h 1 heads
    simp [game, deterministicProfileGame, KernelGame.eu, expect_pure, utility, h0, h1] at hdev
    norm_num at hdev

theorem player0_eu_neg_player1 (σ : game.Profile) :
    game.eu σ 0 = -game.eu σ 1 :=
  letI : Fintype game.Outcome := by
    change Fintype (Fin 2 → Coin)
    infer_instance
  isZeroSum.eu_neg σ

end MatchingPenniesKernel

namespace CoordinationKernel

inductive Venue where
  | left
  | right
deriving DecidableEq, Fintype, Repr

open Venue

/-- A common-interest coordination game. -/
def utility (σ : Fin 2 → Venue) : Payoff (Fin 2) := fun _ =>
  if σ 0 = σ 1 then (1 : ℝ) else 0

noncomputable def game : KernelGame (Fin 2) :=
  deterministicProfileGame (fun _ => Venue) utility

def leftProfile : game.Profile := fun _ => left

def rightProfile : game.Profile := fun _ => right

noncomputable def potential (σ : game.Profile) : ℝ :=
  game.eu σ 0

theorem left_isStrictNash : game.IsStrictNash leftProfile := by
  intro who s' hne
  fin_cases who <;> cases s' <;>
    simp [leftProfile, game, deterministicProfileGame, KernelGame.eu, expect_pure, utility] at hne ⊢

theorem right_isStrictNash : game.IsStrictNash rightProfile := by
  intro who s' hne
  fin_cases who <;> cases s' <;>
    simp [rightProfile, game, deterministicProfileGame, KernelGame.eu,
      expect_pure, utility] at hne ⊢

theorem isTeamGame : game.IsTeamGame := by
  intro ω i j
  simp [game, deterministicProfileGame, utility]

theorem exactPotential : game.IsExactPotential potential := by
  intro who σ s'
  fin_cases who <;> cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases s' <;>
    simp [potential, game, deterministicProfileGame, KernelGame.eu, expect_pure, utility, h0, h1]

theorem left_potential_max (τ : game.Profile) : potential leftProfile ≥ potential τ := by
  cases h0 : τ 0 <;> cases h1 : τ 1 <;>
    simp [potential, leftProfile, game, deterministicProfileGame, KernelGame.eu, expect_pure,
      utility, h0, h1]

theorem left_isNash_from_potential : game.IsNash leftProfile :=
  exactPotential.nash_of_maximizer left_potential_max

end CoordinationKernel

namespace SecondPriceAuction

/-- A concrete two-bidder second-price auction instance. -/
def values : Fin 2 → ℝ
  | 0 => 10
  | 1 => 7

theorem truthful_isDominant (who : Fin 2) :
    (vickreyGame values).IsDominant who (values who) :=
  vickrey_truthful_isDominant values who

theorem truthful_isNash : (vickreyGame values).IsNash values :=
  vickrey_truthful_isNash values

theorem bidder0_value : values 0 = 10 := rfl

theorem bidder1_value : values 1 = 7 := rfl

end SecondPriceAuction

namespace CheckedProgramFacts

theorem prisoners_row_defect_dominates_checked (col : Bool) :
    evalExpr Prisoners.rowPayoff (Prisoners.payoffEnv false col) ≥
      evalExpr Prisoners.rowPayoff (Prisoners.payoffEnv true col) :=
  Prisoners.row_defect_payoff_ge_cooperate col

theorem prisoners_col_defect_dominates_checked (row : Bool) :
    evalExpr Prisoners.colPayoff (Prisoners.payoffEnv row false) ≥
      evalExpr Prisoners.colPayoff (Prisoners.payoffEnv row true) :=
  Prisoners.col_defect_payoff_ge_cooperate row

theorem matchingPennies_zero_sum_checked (matcher mismatcher : Bool) :
    evalExpr MatchingPennies.matcherPayoff
        (MatchingPennies.payoffEnv matcher mismatcher) +
      evalExpr MatchingPennies.mismatcherPayoff
        (MatchingPennies.payoffEnv matcher mismatcher) = 0 :=
  MatchingPennies.payoffs_zero_sum matcher mismatcher

theorem battleOfTheSexes_total_payoff_checked (operaFan footballFan : Bool) :
    evalExpr BattleOfTheSexes.operaFanPayoff
        (BattleOfTheSexes.payoffEnv operaFan footballFan) +
      evalExpr BattleOfTheSexes.footballFanPayoff
        (BattleOfTheSexes.payoffEnv operaFan footballFan) =
      if operaFan = footballFan then 3 else 0 := by
  cases operaFan <;> cases footballFan <;> rfl

theorem montyHall_host_open_not_first
    (opened first firstHidden car : MontyHall.Door)
    (h : evalGuard (Player := MontyHall.Player) (L := simpleExpr)
        MontyHall.hostOpenGuard opened
          (MontyHall.hostGuardEnv first firstHidden car) = true) :
    opened ≠ first :=
  (MontyHall.hostOpenGuard_iff opened first firstHidden car).1 h |>.1

theorem montyHall_host_open_not_car
    (opened first firstHidden car : MontyHall.Door)
    (h : evalGuard (Player := MontyHall.Player) (L := simpleExpr)
        MontyHall.hostOpenGuard opened
          (MontyHall.hostGuardEnv first firstHidden car) = true) :
    opened ≠ car :=
  (MontyHall.hostOpenGuard_iff opened first firstHidden car).1 h |>.2

theorem montyHall_guest_host_constant_sum
    (first opened car : MontyHall.Door) (switch : Bool) :
    evalExpr MontyHall.guestPayoff
        (MontyHall.payoffEnv first opened car switch) +
      evalExpr MontyHall.hostPayoff
        (MontyHall.payoffEnv first opened car switch) = 1 := by
  let env := MontyHall.payoffEnv first opened car switch
  change (if evalExpr MontyHall.guestWins env = true then (1 : Int) else 0) +
      (if evalExpr MontyHall.guestWins env = true then (0 : Int) else 1) = 1
  exact winLose_payoffs_sum_one (evalExpr MontyHall.guestWins env)

theorem montyHall_switch_stay_complement
    (first opened car : MontyHall.Door) :
    evalExpr MontyHall.guestPayoff
        (MontyHall.payoffEnv first opened car true) +
      evalExpr MontyHall.guestPayoff
        (MontyHall.payoffEnv first opened car false) = 1 := by
  rw [MontyHall.switching_wins_iff_first_guess_wrong,
    MontyHall.staying_wins_iff_first_guess_right]
  split <;> norm_num

theorem montyHall_switching_wins_of_first_wrong
    (first opened car : MontyHall.Door) (h : first ≠ car) :
    evalExpr MontyHall.guestPayoff
        (MontyHall.payoffEnv first opened car true) = 1 := by
  rw [MontyHall.switching_wins_iff_first_guess_wrong]
  simp [h]

theorem montyHall_staying_wins_of_first_right
    (first opened car : MontyHall.Door) (h : first = car) :
    evalExpr MontyHall.guestPayoff
        (MontyHall.payoffEnv first opened car false) = 1 := by
  rw [MontyHall.staying_wins_iff_first_guess_right]
  simp [h]

end CheckedProgramFacts

namespace ProgramFacts

theorem prisoners_horizon : syntaxSteps Prisoners.program = 4 := rfl

theorem matchingPennies_horizon : syntaxSteps MatchingPennies.program = 4 := rfl

theorem battleOfTheSexes_horizon : syntaxSteps BattleOfTheSexes.program = 4 := rfl

theorem montyHall_horizon : syntaxSteps MontyHall.program = 8 := rfl

theorem prisoners_finiteProgram : Nonempty (FiniteProgram Prisoners.program) :=
  ⟨inferInstance⟩

theorem matchingPennies_finiteProgram : Nonempty (FiniteProgram MatchingPennies.program) :=
  ⟨inferInstance⟩

theorem battleOfTheSexes_finiteProgram :
    Nonempty (FiniteProgram BattleOfTheSexes.program) :=
  ⟨inferInstance⟩

theorem montyHall_finiteProgram : Nonempty (FiniteProgram MontyHall.program) :=
  ⟨inferInstance⟩

end ProgramFacts

end SolutionConcepts
end Examples
end Vegas
