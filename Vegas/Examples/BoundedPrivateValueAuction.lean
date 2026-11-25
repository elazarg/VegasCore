module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.BoundedPaymentAuction
public import Vegas.Game.IntendedAuthenticOpening
public import Vegas.Source.PrivateInputsIndependent
public import Vegas.Game.OnePacketPublicInitialSignal
public import GameTheory.Math.Probability.FiniteUniform

@[expose] public section

/-! # A bounded auction with private initial values

Two bidders submit sealed bids in the range zero through six. Alice wins ties,
and the winner pays the other bid. True values remain owner-private initial
cells throughout execution. The allocation and payments use the second-price
rule of W. Vickrey, “Counterspeculation, Auctions, and Competitive Sealed
Tenders,” Journal of Finance 16 (1961).
-/

noncomputable section

namespace Vegas.Examples.BoundedPrivateValueAuction

open SourceProgram GameTheory GameTheory.Math.Probability
open CommitRevealAuction (Player)

abbrev Bid := BoundedPaymentAuction.Bid

def roster : Bool ≃ Player where
  toFun value := if value then .bob else .alice
  invFun | .alice => false | .bob => true
  left_inv value := by cases value <;> rfl
  right_inv value := by cases value <;> rfl

def context : SourceCtx Player simpleExpr :=
  [(4, .privateInput .alice (.range 0 6)), (5, .privateInput .bob (.range 0 6))]

def program : SourceProgram Player simpleExpr context ∅ :=
  .commit 0 .alice (by decide) (BoundedPaymentAuction.acceptGuard .alice 0) <|
  .commit 1 .bob (by decide) (BoundedPaymentAuction.acceptGuard .bob 1) <|
  .reveal 2 .alice 0 (by decide) (.there .here) (by decide) <|
  .reveal 3 .bob 1 (by decide) (.there .here) (by decide) <|
  .ret [(.alice, BoundedPaymentAuction.cashExpr 6 .alice (.var 2 (.there .here)) (.var 3 .here)),
    (.bob, BoundedPaymentAuction.cashExpr 6 .bob (.var 2 (.there .here)) (.var 3 .here))]

def initial (types : Player → Bid) : State simpleExpr context :=
  Env.cons (types .alice) (Env.cons (types .bob) (Env.empty (CellVal simpleExpr)))

def values (state : State simpleExpr context) : Player → Bid
  | .alice => state.get .here
  | .bob => state.get (.there .here)

@[simp] theorem values_initial (types : Player → Bid) : values (initial types) = types := by
  funext who
  cases who <;> rfl

def setup (prior : PMF (Player → Bid)) : Setup (Player := Player) (L := simpleExpr) where
  context := context
  namesNodup := by decide
  initialDistribution := prior.map initial
  obligations := ∅
  program := program
  accounts := rfl
  exitTransfers := fun _ => -6

def uniformPrior : PMF (Player → Bid) := uniformLaw _

theorem finiteBindingTypes : program.FiniteBindingTypes :=
  ⟨inferInstance, inferInstance, trivial⟩

instance (prior : PMF (Player → Bid)) : (setup prior).FiniteInitialSupport where
  support_finite := by
    change (prior.map initial).support.Finite
    rw [PMF.support_map]
    exact (Set.toFinite _).image _

def valuation (types : Player → Bid) (outcome : PublicOutcome program) : Player → ℝ :=
  BoundedPaymentAuction.valuation 6 (fun who => (types who).val)
    ⟨outcome.values, outcome.defaults⟩

def utility (outcome : (Player → Bid) × PublicOutcome program) : Player → ℝ :=
  program.paymentSumUtility (valuation outcome.1) outcome.2

theorem publicPayoffs_eq (outcome : PublicOutcome program) :
    program.publicPayoffs outcome =
      [(.alice, BoundedPaymentAuction.cash 6 (outcome.values.get (.there .here))
          (outcome.values.get .here) .alice),
        (.bob, BoundedPaymentAuction.cash 6 (outcome.values.get (.there .here))
          (outcome.values.get .here) .bob)] := by
  change [(Player.alice, evalExpr _ outcome.values), (Player.bob, evalExpr _ outcome.values)] = _
  rw [BoundedPaymentAuction.eval_cashExpr, BoundedPaymentAuction.eval_cashExpr]
  rfl

theorem utility_eq_economic (outcome : (Player → Bid) × PublicOutcome program) (who : Player) :
    utility outcome who =
      CommitRevealAuction.utility (fun player => (outcome.1 player).val) 6
        (CommitRevealAuction.result
          (BoundedPaymentAuction.integerPublication (outcome.2.values.get (.there .here)))
          (BoundedPaymentAuction.integerPublication (outcome.2.values.get .here))) who := by
  unfold utility
  rw [paymentSumUtility_eq]
  unfold publicTransfers
  rw [publicPayoffs_eq]
  cases who <;>
    cases aliceEq : (outcome.2.values.get (.there .here) : PublicationResult Bid) <;>
    cases bobEq : (outcome.2.values.get .here : PublicationResult Bid) <;>
    simp only [Env.get] at aliceEq bobEq
  all_goals
    simp [valuation, BoundedPaymentAuction.valuation, BoundedPaymentAuction.cash,
      BoundedPaymentAuction.integerPublication, CommitRevealAuction.utility,
      CommitRevealAuction.result, transferAmount, Env.get, Env.cons, aliceEq, bobEq]
  all_goals split_ifs <;> ring

def alicePolicy : BehavioralPolicy Player.alice program :=
  (fun _ view _ => PMF.pure (some (.success
      ((view.observation.cells.get .here).getD (BoundedPaymentAuction.bid 0)))),
    ((fun h => nomatch h),
      (fun _ _ _ => PMF.pure true, ((fun h => nomatch h), PUnit.unit))))

def bobPolicy : BehavioralPolicy Player.bob program :=
  ((fun h => nomatch h),
    (fun _ view _ => PMF.pure (some (.success
      ((view.observation.cells.get (.there (.there .here))).getD (BoundedPaymentAuction.bid 0)))),
      ((fun h => nomatch h), (fun _ _ _ => PMF.pure true, PUnit.unit))))

def truthful : BehavioralProfile program
  | .alice => alicePolicy
  | .bob => bobPolicy

def finalConfig (types : Player → Bid) (alice bob : Bid) :
    Config Player simpleExpr program.terminalCtx :=
  revealSuccessor 3 (.there .here)
    (revealSuccessor 2 (.there .here)
      (commitSuccessor 1 (BoundedPaymentAuction.acceptGuard .bob 1)
        (commitSuccessor 0 (BoundedPaymentAuction.acceptGuard .alice 0)
          (Config.initial (initial types)) (some (.success alice)))
          (some (.success bob))) true) true

theorem truthful_run_initial (types : Player → Bid) :
    program.run truthful (initial types) =
      PMF.pure (finalConfig types (types .alice) (types .bob)) := by
  simp only [SourceProgram.run, program, truthful, alicePolicy, bobPolicy, initial,
    runFrom, commitKernel, revealKernel, afterCommit, afterReveal, PMF.pure_bind,
    Config.initial_defaulted, Finset.notMem_empty, ↓reduceDIte]
  rw [dite_eq_right (by change Player.bob ∉ (∅ : Finset Player); decide), PMF.pure_bind]
  rw [dite_eq_right (by change Player.alice ∉ (∅ : Finset Player); decide), PMF.pure_bind]
  rw [dite_eq_right (by change Player.bob ∉ (∅ : Finset Player); decide), PMF.pure_bind]
  rfl

theorem truthful_source_distribution (prior : PMF (Player → Bid)) :
    (setup prior).run truthful = prior.map
      (fun types => finalConfig types (types .alice) (types .bob)) := by
  change (prior.map initial).bind (program.run truthful) = _
  rw [PMF.bind_map]
  simp_rw [Function.comp_def, truthful_run_initial]
  exact PMF.bind_pure_comp _ _

theorem eventCount : Vegas.eventCount program = 4 := rfl

theorem initial_values (state : State simpleExpr context) : initial (values state) = state := by
  funext name kind cell
  cases cell with
  | here => rfl
  | there cell =>
    cases cell with
    | here => rfl
    | there absent => cases absent

theorem initial_mass (state : State simpleExpr context) :
    (setup uniformPrior).initialDistribution state = (Fintype.card (Player → Bid) : ENNReal)⁻¹ := by
  classical
  change (uniformPrior.map initial) state = _
  rw [PMF.map_apply]
  calc
    _ = if state = initial (values state) then uniformPrior (values state) else 0 := by
      apply tsum_eq_single (values state)
      intro types different
      rw [ite_eq_right]
      intro same
      apply different
      have mapped := congrArg values same
      simpa using mapped.symm
    _ = _ := by rw [initial_values, ite_eq_left rfl]; rfl

def signal (_state : State simpleExpr context) : Unit := ()

theorem independent : (setup uniformPrior).PrivateInputsIndependentGiven signal := by
  intro who first second _
  exact (congrArg₂ (fun x y : ENNReal => x * y)
    (initial_mass (splice who first second)) (initial_mass (splice who second first))).trans
      (congrArg₂ (fun x y : ENNReal => x * y) (initial_mass first) (initial_mass second)).symm

theorem observable : (setup uniformPrior).PublicInitialSignal signal := by intro _ _ _; rfl

theorem wellFormed (prior : PMF (Player → Bid)) : (setup prior).WellFormed where
  initialValues := by
    intro state _ name owner payload cell
    cases cell with
    | there cell => cases cell with
      | there absent => cases absent
  guardsSatisfiable := by
    intro state _
    exact ⟨⟨BoundedPaymentAuction.bid 0, rfl⟩, fun _ _ =>
      ⟨⟨BoundedPaymentAuction.bid 0, rfl⟩, fun _ _ => trivial⟩⟩

end Vegas.Examples.BoundedPrivateValueAuction
