import Vegas.StrategicPMF

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
  [(colSecret, ⟨.bool, .hidden Player.col⟩),
   (rowSecret, ⟨.bool, .hidden Player.row⟩)]
abbrev Γ3 : Ctx :=
  [(rowPublic, ⟨.bool, .pub⟩),
   (colSecret, ⟨.bool, .hidden Player.col⟩),
   (rowSecret, ⟨.bool, .hidden Player.row⟩)]
abbrev Γ4 : Ctx :=
  [(colPublic, ⟨.bool, .pub⟩),
   (rowPublic, ⟨.bool, .pub⟩),
   (colSecret, ⟨.bool, .hidden Player.col⟩),
   (rowSecret, ⟨.bool, .hidden Player.row⟩)]

def hRowSecretΓ2 :
    VHasVar Γ2 rowSecret ⟨.bool, .hidden Player.row⟩ :=
  .there .here

def hColSecretΓ3 :
    VHasVar Γ3 colSecret ⟨.bool, .hidden Player.col⟩ :=
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

theorem row_defect_payoff_ge_cooperate (col : Bool) :
    evalExpr rowPayoff (payoffEnv false col) ≥
      evalExpr rowPayoff (payoffEnv true col) := by
  cases col <;> decide

theorem col_defect_payoff_ge_cooperate (row : Bool) :
    evalExpr colPayoff (payoffEnv row false) ≥
      evalExpr colPayoff (payoffEnv row true) := by
  cases row <;> decide

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
