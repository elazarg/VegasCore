import Vegas.Strategic.BehavioralPMF

/-!
# Prisoner's Dilemma

A checked Vegas encoding of the two-player Prisoner's Dilemma. The Boolean
commitments use `true` for cooperate and `false` for defect.
-/

namespace Vegas
namespace Examples
namespace Prisoners

inductive Player where
  | row
  | col
deriving DecidableEq, Repr, Fintype

abbrev Ctx := VCtx Player simpleExpr
abbrev Prog (Γ : Ctx) := VegasCore Player simpleExpr Γ

def rowSecret : VarId := 0
def colSecret : VarId := 1
def rowPublic : VarId := 2
def colPublic : VarId := 3

abbrev Γ0 : Ctx := []
abbrev Γ2 : Ctx :=
  [(colSecret, .hidden Player.col .bool),
   (rowSecret, .hidden Player.row .bool)]
abbrev Γ3 : Ctx :=
  [(rowPublic, .pub .bool),
   (colSecret, .hidden Player.col .bool),
   (rowSecret, .hidden Player.row .bool)]
abbrev Γ4 : Ctx :=
  [(colPublic, .pub .bool),
   (rowPublic, .pub .bool),
   (colSecret, .hidden Player.col .bool),
   (rowSecret, .hidden Player.row .bool)]

def hRowSecretΓ2 :
    VHasVar Γ2 rowSecret (.hidden Player.row .bool) :=
  .there .here

def hColSecretΓ3 :
    VHasVar Γ3 colSecret (.hidden Player.col .bool) :=
  .there .here

def hColPublicPayoff :
    HasVar (erasePubVCtx Γ4) colPublic .bool :=
  .here

def hRowPublicPayoff :
    HasVar (erasePubVCtx Γ4) rowPublic .bool :=
  .there .here

def rowChoice : Expr (erasePubVCtx Γ4) .bool :=
  .var rowPublic hRowPublicPayoff

def colChoice : Expr (erasePubVCtx Γ4) .bool :=
  .var colPublic hColPublicPayoff

/-- Row payoff: `(C,C)=2`, `(C,D)=0`, `(D,C)=3`, `(D,D)=1`. -/
def rowPayoff : Expr (erasePubVCtx Γ4) .int :=
  .ite rowChoice
    (.ite colChoice (.constInt 2) (.constInt 0))
    (.ite colChoice (.constInt 3) (.constInt 1))

/-- Column payoff: `(C,C)=2`, `(C,D)=3`, `(D,C)=0`, `(D,D)=1`. -/
def colPayoff : Expr (erasePubVCtx Γ4) .int :=
  .ite rowChoice
    (.ite colChoice (.constInt 2) (.constInt 3))
    (.ite colChoice (.constInt 0) (.constInt 1))

def payoffEnv (row col : Bool) :
    Env simpleExpr.Val (erasePubVCtx Γ4) :=
  Env.cons (x := colPublic) col
    (Env.cons (x := rowPublic) row (Env.empty simpleExpr.Val))

theorem defect_defect_payoff :
    evalExpr rowPayoff (payoffEnv false false) = 1 ∧
      evalExpr colPayoff (payoffEnv false false) = 1 := by
  exact ⟨rfl, rfl⟩

/-- Complete payoff table of the source-level Boolean choices. -/
theorem payoff_table (row col : Bool) :
    (evalExpr rowPayoff (payoffEnv row col),
      evalExpr colPayoff (payoffEnv row col)) =
      match row, col with
      | true, true => (2, 2)
      | true, false => (0, 3)
      | false, true => (3, 0)
      | false, false => (1, 1) := by
  cases row <;> cases col <;> rfl

theorem row_defect_payoff_gt_cooperate (col : Bool) :
    evalExpr rowPayoff (payoffEnv false col) >
      evalExpr rowPayoff (payoffEnv true col) := by
  cases col <;> decide

theorem col_defect_payoff_gt_cooperate (row : Bool) :
    evalExpr colPayoff (payoffEnv row false) >
      evalExpr colPayoff (payoffEnv row true) := by
  cases row <;> decide

theorem row_defect_payoff_ge_cooperate (col : Bool) :
    evalExpr rowPayoff (payoffEnv false col) ≥
      evalExpr rowPayoff (payoffEnv true col) :=
  le_of_lt (row_defect_payoff_gt_cooperate col)

theorem col_defect_payoff_ge_cooperate (row : Bool) :
    evalExpr colPayoff (payoffEnv row false) ≥
      evalExpr colPayoff (payoffEnv row true) :=
  le_of_lt (col_defect_payoff_gt_cooperate row)

abbrev ActionProfile := Player → Bool

def actionPayoff (σ : ActionProfile) : Player → Int
  | Player.row => evalExpr rowPayoff (payoffEnv (σ Player.row) (σ Player.col))
  | Player.col => evalExpr colPayoff (payoffEnv (σ Player.row) (σ Player.col))

def IsActionNash (σ : ActionProfile) : Prop :=
  ∀ who alt, actionPayoff σ who ≥
    actionPayoff (Function.update σ who alt) who

def defectProfile : ActionProfile
  | Player.row => false
  | Player.col => false

theorem defectProfile_actionNash : IsActionNash defectProfile := by
  intro who alt
  cases who <;> cases alt <;> decide

theorem actionNash_eq_defectProfile
    (σ : ActionProfile) (hσ : IsActionNash σ) :
    σ = defectProfile := by
  have hrowFalse : σ Player.row = false := by
    cases hrow : σ Player.row
    · rfl
    · cases hcol : σ Player.col
      · have hdev := hσ Player.row false
        have hbad :
            evalExpr rowPayoff (payoffEnv false false) ≤
              evalExpr rowPayoff (payoffEnv true false) := by
          simpa [actionPayoff, hrow, hcol] using hdev
        exact False.elim
          ((not_le_of_gt (row_defect_payoff_gt_cooperate false)) hbad)
      · have hdev := hσ Player.row false
        have hbad :
            evalExpr rowPayoff (payoffEnv false true) ≤
              evalExpr rowPayoff (payoffEnv true true) := by
          simpa [actionPayoff, hrow, hcol] using hdev
        exact False.elim
          ((not_le_of_gt (row_defect_payoff_gt_cooperate true)) hbad)
  have hcolFalse : σ Player.col = false := by
    cases hcol : σ Player.col
    · rfl
    · have hdev := hσ Player.col false
      have hbad :
          evalExpr colPayoff (payoffEnv false false) ≤
            evalExpr colPayoff (payoffEnv false true) := by
        simpa [actionPayoff, hrowFalse, hcol] using hdev
      exact False.elim
        ((not_le_of_gt (col_defect_payoff_gt_cooperate false)) hbad)
  funext who
  cases who <;> simp [defectProfile, hrowFalse, hcolFalse]

theorem actionNash_iff_defectProfile (σ : ActionProfile) :
    IsActionNash σ ↔ σ = defectProfile := by
  constructor
  · exact actionNash_eq_defectProfile σ
  · intro h
    subst σ
    exact defectProfile_actionNash

noncomputable abbrev program : Prog Γ0 :=
  .commit rowSecret Player.row (b := .bool) (.constBool true)
    (.commit colSecret Player.col (b := .bool) (.constBool true)
      (.reveal rowPublic Player.row rowSecret hRowSecretΓ2
        (.reveal colPublic Player.col colSecret hColSecretΓ3
          (.ret [(Player.row, rowPayoff), (Player.col, colPayoff)]))))

def viewScoped : ViewScoped program := by
  dsimp [program, ViewScoped]
  constructor
  · intro z hz
    simp [simpleExpr, exprDeps] at hz
  · constructor
    · intro z hz
      simp [simpleExpr, exprDeps] at hz
    · trivial

def legal : Legal program := by
  dsimp [program, Legal]
  constructor
  · intro _env
    exact ⟨true, rfl⟩
  · constructor
    · intro _env
      exact ⟨true, rfl⟩
    · trivial

def wf : WF program :=
  ⟨by decide, by decide, viewScoped⟩

def normalized : NormalizedDists program := by
  simp [NormalizedDists]

noncomputable def game : WFProgram Player simpleExpr where
  Γ := Γ0
  prog := program
  env := VEnv.empty simpleExpr
  wctx := WFCtx_nil
  wf := wf
  normalized := normalized
  legal := legal

noncomputable instance instFiniteDomains : FiniteDomains game where
  context := inferInstanceAs (FiniteVCtx Γ0)
  program := inferInstanceAs (FiniteProgram program)

noncomputable def pureGame : GameTheory.KernelGame Player :=
  pureKernelGame game

noncomputable def behavioralGame : GameTheory.KernelGame Player :=
  pmfBehavioralKernelGame game

theorem pureGame_outcomeKernel
    (σ : pureGame.Profile) :
    pureGame.outcomeKernel σ = pureOutcomeKernelAt game σ := rfl

theorem behavioralGame_outcomeKernel
    (σ : behavioralGame.Profile) :
    behavioralGame.outcomeKernel σ = behavioralOutcomeKernelPMFAt game σ := rfl

end Prisoners
end Examples
end Vegas
