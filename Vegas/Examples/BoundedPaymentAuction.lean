/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Expr.Simple
import Vegas.Game.ProgramPaymentNash
import Vegas.Examples.CommitRevealAuction

/-! # A bounded auction whose transfers are executable instructions

Reports range from zero through six. The program evaluates a finite table of
second-price transfers, including an integer withholding charge. Valuation is
separate from cash. Conditional withholding prevents dominant truthful reporting
for every integer charge, even though transfers are evaluated by the program.
-/

noncomputable section

namespace Vegas.Examples.BoundedPaymentAuction

open SourceProgram GameTheory GameTheory.Math.Probability
open CommitRevealAuction (Player)

abbrev Bid := Val (.range 0 6)

private def bid (index : Fin 7) : Bid :=
  ⟨index.val, by have := index.isLt; constructor <;> omega⟩

private def publications : List (PublicationResult Bid) :=
  .failure :: (List.finRange 7).map (fun index => .success (bid index))

private theorem mem_publications (value : PublicationResult Bid) : value ∈ publications := by
  cases value with
  | failure => exact List.mem_cons_self
  | success value =>
      obtain ⟨value, bounds⟩ := value
      change (0 : Int) ≤ value ∧ value ≤ 6 at bounds
      obtain ⟨lower, upper⟩ := bounds
      let index : Fin 7 := ⟨value.toNat, by omega⟩
      have same : bid index = (⟨value, by constructor <;> omega⟩ : Bid) := by
        apply Subtype.ext
        simp only [bid, index]
        omega
      exact List.mem_cons_of_mem _ (List.mem_map.mpr
        ⟨index, List.mem_finRange _, congrArg PublicationResult.success same⟩)

private def publicLiteral {Γ : CtxSimple} : PublicationResult Bid → Expr Γ (.result (.range 0 6))
  | .failure => .failure
  | .success value => .success (.constRange value)

private theorem eval_publicLiteral {Γ : CtxSimple} (env : PlainEnv Γ)
    (value : PublicationResult Bid) : evalExpr (publicLiteral value) env = value := by
  cases value <;> rfl

private def tableExpr {α : Type} {Γ : CtxSimple} (test : α → Expr Γ .bool)
    (amount : α → Int) : List α → Expr Γ .int
  | [] => .constInt 0
  | key :: rest => .ite (test key) (.constInt (amount key)) (tableExpr test amount rest)

private theorem eval_tableExpr {α : Type} [DecidableEq α] {Γ : CtxSimple}
    (test : α → Expr Γ .bool) (amount : α → Int) (env : PlainEnv Γ)
    (keys : List α) (actual : α)
    (correct : ∀ key ∈ keys, evalExpr (test key) env = decide (key = actual))
    (member : actual ∈ keys) : evalExpr (tableExpr test amount keys) env = amount actual := by
  induction keys with
  | nil => cases member
  | cons key rest ih =>
      by_cases same : key = actual
      · subst key
        simp only [tableExpr, evalExpr, correct actual (by simp), decide_true, ↓reduceIte]
      · have later : actual ∈ rest := (List.mem_cons.mp member).resolve_left (Ne.symm same)
        simp only [tableExpr, evalExpr, correct key (by simp), same, decide_false,
          Bool.false_eq_true, ↓reduceIte]
        exact ih (fun selected selectedMember => correct selected (by simp [selectedMember])) later

/-- Signed receipts in an auction with an external seller; ties favor Alice. -/
def cash (penalty : Int) (alice bob : PublicationResult Bid) : Player → Int
  | .alice => match alice with
    | .failure => -penalty
    | .success a => match bob with
      | .failure => 0
      | .success b => if b.val ≤ a.val then -b.val else 0
  | .bob => match bob with
    | .failure => -penalty
    | .success b => match alice with
      | .failure => 0
      | .success a => if a.val < b.val then -a.val else 0

private def cashExpr {Γ : CtxSimple} (penalty : Int) (who : Player)
    (alice bob : Expr Γ (.result (.range 0 6))) : Expr Γ .int :=
  tableExpr (fun pair => .andBool (.eq (publicLiteral pair.1) alice)
    (.eq (publicLiteral pair.2) bob)) (fun pair => cash penalty pair.1 pair.2 who)
    (publications.product publications)

private theorem eval_cashExpr {Γ : CtxSimple} (penalty : Int) (who : Player)
    (alice bob : Expr Γ (.result (.range 0 6))) (env : PlainEnv Γ) :
    evalExpr (cashExpr penalty who alice bob) env =
      cash penalty (evalExpr alice env) (evalExpr bob env) who := by
  unfold cashExpr
  apply eval_tableExpr (actual := (evalExpr alice env, evalExpr bob env))
  · intro pair _
    simp only [evalExpr, eval_publicLiteral]
    by_cases first : pair.1 = evalExpr alice env <;>
      by_cases second : pair.2 = evalExpr bob env <;> simp_all [Prod.ext_iff]
  · exact List.mem_product.mpr ⟨mem_publications _, mem_publications _⟩

private def acceptGuard {Γ : SourceCtx Player simpleExpr} (who : Player) (name : VarId) :
    SourceGuard simpleExpr Γ who name (.range 0 6) where
  schema := []
  schemaNames := by decide
  subjectFresh := by simp
  code := .constBool true
  reads := fun h => nomatch h

/-- The terminal instructions compute the actual second-price receipts. -/
def program (penalty : Int) : SourceProgram Player simpleExpr [] ∅ :=
  .commit 0 .alice (by decide) (acceptGuard .alice 0) <|
  .commit 1 .bob (by decide) (acceptGuard .bob 1) <|
  .reveal 2 .alice 0 (by decide) (.there .here) (by decide) <|
  .reveal 3 .bob 1 (by decide) (.there .here) (by decide) <|
  .ret [(.alice, cashExpr penalty .alice (.var 2 (.there .here)) (.var 3 .here)),
    (.bob, cashExpr penalty .bob (.var 2 (.there .here)) (.var 3 .here))]

def setup (penalty : Int) : Setup (Player := Player) (L := simpleExpr) where
  context := []
  namesNodup := by decide
  initialLaw := PMF.pure (Env.empty (CellVal simpleExpr))
  obligations := ∅
  program := program penalty
  accounts := rfl

instance (penalty : Int) : (setup penalty).FiniteInitialLaw where
  support_finite := by
    change (PMF.pure _).support.Finite
    simp

theorem finiteBindingTypes (penalty : Int) : (program penalty).FiniteBindingTypes := by
  exact ⟨inferInstance, inferInstance, trivial⟩

/-- Every outcome, including failed and withheld publications, evaluates to
exactly the semantic second-price settlement. -/
theorem publicPayoffs_eq (penalty : Int) (outcome : PublicOutcome (program penalty)) :
    (program penalty).publicPayoffs outcome =
      [(.alice, cash penalty (outcome.get (.there .here)) (outcome.get .here) .alice),
        (.bob, cash penalty (outcome.get (.there .here)) (outcome.get .here) .bob)] := by
  change [(Player.alice, evalExpr _ outcome), (Player.bob, evalExpr _ outcome)] = _
  rw [eval_cashExpr, eval_cashExpr]
  rfl


def result (penalty : Int) (alice bob : PublicationResult Bid) :
    PublicOutcome (program penalty) :=
  Env.cons bob (Env.cons alice (Env.empty simpleExpr.Val))

private def integerPublication : PublicationResult Bid → PublicationResult Int
  | .failure => .failure
  | .success value => .success value.val

/-- Allocation value has no monetary component; the program supplies all cash. -/
def valuation (penalty : Int) (values : Player → ℝ)
    (outcome : PublicOutcome (program penalty)) : Player → ℝ
  | .alice => match (outcome.get (.there .here) : PublicationResult Bid) with
    | .failure => 0
    | .success a => match (outcome.get .here : PublicationResult Bid) with
      | .failure => values .alice
      | .success b => if b.val ≤ a.val then values .alice else 0
  | .bob => match (outcome.get .here : PublicationResult Bid) with
    | .failure => 0
    | .success b => match (outcome.get (.there .here) : PublicationResult Bid) with
      | .failure => values .bob
      | .success a => if a.val < b.val then values .bob else 0

/-- The evaluated instructions agree with the ordinary real-valued economic
settlement on every bounded report and failure outcome. -/
theorem paymentUtility_eq_economic (penalty : Int) (values : Player → ℝ)
    (outcome : PublicOutcome (program penalty)) (who : Player) :
    (program penalty).paymentUtility (valuation penalty values) outcome who =
      CommitRevealAuction.utility values (penalty : ℝ)
        (CommitRevealAuction.result
          (integerPublication (outcome.get (.there .here)))
          (integerPublication (outcome.get .here))) who := by
  rw [paymentUtility_eq]
  unfold publicTransfers
  rw [publicPayoffs_eq]
  cases who <;>
    cases aliceEq : (outcome.get (.there .here) : PublicationResult Bid) <;>
    cases bobEq : (outcome.get .here : PublicationResult Bid) <;>
    simp only [Env.get] at aliceEq bobEq
  all_goals
    simp [valuation, cash, integerPublication, CommitRevealAuction.utility,
      CommitRevealAuction.result, transferAmount, Env.get, Env.cons, aliceEq, bobEq]
  all_goals split_ifs <;> ring

/-- The finite report alphabet supports the existing full-deviation compiler
Nash equivalence with the program's own evaluated monetary instructions. -/
theorem compiled_nash_iff (penalty : Int) (values : Player → ℝ)
    (scheduler : (setup penalty).eventGraph.PublicScheduler) (error : ℝ)
    (profile : BehavioralProfile (program penalty)) :
    IsεNash ((setup penalty).eventGame scheduler)
        (fun outcome who =>
          valuation penalty values ((setup penalty).eventPublicOutcome outcome) who +
            (transferAmount (terminalPayouts (program penalty) outcome) who : ℝ)) error
        (compileEventProfile (program penalty) profile) ↔
      IsεNash (setup penalty).gameForm ((program penalty).paymentUtility (valuation penalty values))
        error profile :=
  (setup penalty).eventGame_payment_approximate_nash_iff (finiteBindingTypes penalty)
    scheduler (valuation penalty values) error profile


/-- Alice reports a bounded value and discloses it. -/
def alicePolicy (penalty : Int) (report : Bid) :
    BehavioralPolicy Player.alice (program penalty) :=
  (fun _ _ => PMF.pure (.success report),
    ((fun h => nomatch h),
      (fun _ _ => PMF.pure true, ((fun h => nomatch h), PUnit.unit))))

/-- Bob reports four and reveals exactly when Alice publishes five. -/
def bobPolicy (penalty : Int) : BehavioralPolicy Player.bob (program penalty) :=
  ((fun h => nomatch h),
    (fun _ _ => PMF.pure (.success (bid 4)),
      ((fun h => nomatch h),
        (fun _ view => PMF.pure (match view.1.cells.get .here with
          | .failure => false
          | .success report => decide (report = bid 5)), PUnit.unit))))

def profile (penalty : Int) (report : Bid) : BehavioralProfile (program penalty)
  | .alice => alicePolicy penalty report
  | .bob => bobPolicy penalty

theorem play_truthful (penalty : Int) :
    (setup penalty).gameForm.play (profile penalty (bid 5)) =
      PMF.pure (result penalty (.success (bid 5)) (.success (bid 4))) := by
  simp only [Setup.gameForm, Setup.publicRun, Setup.run, setup, SourceProgram.run,
    program, profile, alicePolicy, bobPolicy, runWith, commitKernel, revealKernel,
    afterCommit, afterReveal, PMF.pure_bind, PMF.pure_map]
  rfl

theorem play_misreport (penalty : Int) :
    (setup penalty).gameForm.play (profile penalty (bid 6)) =
      PMF.pure (result penalty (.success (bid 6)) .failure) := by
  simp only [Setup.gameForm, Setup.publicRun, Setup.run, setup, SourceProgram.run,
    program, profile, alicePolicy, bobPolicy, runWith, commitKernel, revealKernel,
    afterCommit, afterReveal, PMF.pure_bind, PMF.pure_map]
  rfl

theorem update_profile (penalty : Int) (before after : Bid) :
    Profile.update (sig := (setup penalty).gameForm.sig) (profile penalty before)
        Player.alice (alicePolicy penalty after) = profile penalty after := by
  funext who
  cases who <;> simp [profile, Profile.update]

/-- Executing the transfers retains the same strict conditional-withholding
counterexample: Alice's net utility increases from one to five. -/
theorem profitable_misreport (penalty : Int) (values : Player → ℝ)
    (valueAlice : values .alice = 5) :
    expectedUtility ((program penalty).paymentUtility (valuation penalty values)) Player.alice
        ((setup penalty).gameForm.play (profile penalty (bid 5))) <
      expectedUtility ((program penalty).paymentUtility (valuation penalty values)) Player.alice
        ((setup penalty).gameForm.play (profile penalty (bid 6))) := by
  rw [play_truthful, play_misreport, expectedUtility_pure, expectedUtility_pure,
    paymentUtility_eq_economic, paymentUtility_eq_economic]
  norm_num [CommitRevealAuction.utility, CommitRevealAuction.result,
    result, integerPublication, bid, Env.get, Env.cons, valueAlice]

/-- The actual-payment bounded auction still does not make truthful disclosure
dominant, for any integer withholding charge. All whole policies are legal
comparators in this game form. -/
theorem truthful_not_dominant (penalty : Int) (values : Player → ℝ)
    (valueAlice : values .alice = 5) :
    ¬ IsDominant (setup penalty).gameForm
      (euPreference ((program penalty).paymentUtility (valuation penalty values)))
      Player.alice (alicePolicy penalty (bid 5)) := by
  intro dominant
  have bound := dominant (alicePolicy penalty (bid 6)) (profile penalty (bid 5))
  rw [update_profile, update_profile] at bound
  have real := (euPreference_iff _ _ _ _
    (by rw [play_truthful]; exact payoffIntegrable_pure _ _)
    (by rw [play_misreport]; exact payoffIntegrable_pure _ _)).mp bound
  exact (not_le_of_gt (profitable_misreport penalty values valueAlice)) real

end Vegas.Examples.BoundedPaymentAuction
