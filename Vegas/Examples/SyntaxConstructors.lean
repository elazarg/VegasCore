import Vegas.StrategicPMF

/-!
# Syntax constructor examples

Small checked programs whose main purpose is to exercise source constructors
that do not appear in the commit/reveal examples.
-/

namespace Vegas
namespace Examples
namespace SyntaxConstructors

inductive Player where
  | sole
deriving DecidableEq, Repr, Fintype

abbrev Ctx := VCtx Player simpleExpr
abbrev Prog (Γ : Ctx) := VegasCore Player simpleExpr Γ

def flag : VarId := 0
def coin : VarId := 1

abbrev Γ0 : Ctx := []
abbrev Γ1 : Ctx := [(flag, ⟨.bool, .pub⟩)]
abbrev Γ2 : Ctx := [(coin, ⟨.bool, .pub⟩), (flag, ⟨.bool, .pub⟩)]

def hCoinPayoff : HasVar (erasePubVCtx Γ2) coin .bool :=
  .here

def hFlagPayoff : HasVar (erasePubVCtx Γ2) flag .bool :=
  .there .here

def flagValue : Expr (erasePubVCtx Γ0) .bool :=
  .constBool true

def fairCoin : DistExpr (erasePubVCtx Γ1) .bool :=
  .weighted [(true, 1 / 2), (false, 1 / 2)]

def coinExpr : Expr (erasePubVCtx Γ2) .bool :=
  .var coin hCoinPayoff

def flagExpr : Expr (erasePubVCtx Γ2) .bool :=
  .var flag hFlagPayoff

/-- Pay `1` exactly when the deterministic flag and sampled coin are both true. -/
def payoff : Expr (erasePubVCtx Γ2) .int :=
  .ite flagExpr (.ite coinExpr (.constInt 1) (.constInt 0)) (.constInt 0)

def payoffEnv (sampled : Bool) : Env simpleExpr.Val (erasePubVCtx Γ2) :=
  Env.cons (x := coin) sampled
    (Env.cons (x := flag) true (Env.empty simpleExpr.Val))

theorem flagValue_eval :
    evalExpr flagValue (Env.empty simpleExpr.Val) = true := rfl

set_option linter.style.nativeDecide false in
theorem fairCoin_totalWeight (env : Env simpleExpr.Val (erasePubVCtx Γ1)) :
    FWeight.totalWeight (evalDistExpr fairCoin env) = 1 := by
  change FWeight.totalWeight (FWeight.ofList [(true, 1 / 2), (false, 1 / 2)]) = 1
  native_decide

theorem payoff_true :
    evalExpr payoff (payoffEnv true) = 1 := rfl

theorem payoff_false :
    evalExpr payoff (payoffEnv false) = 0 := rfl

noncomputable abbrev program : Prog Γ0 :=
  .letExpr flag flagValue
    (.sample coin fairCoin
      (.ret [(Player.sole, payoff)]))

def viewScoped : ViewScoped program := by
  dsimp [program, ViewScoped]
  trivial

def legal : Legal program := by
  dsimp [program, Legal]

def wf : WF program :=
  ⟨by decide, by decide, viewScoped⟩

def normalized : NormalizedDists program := by
  dsimp [program, NormalizedDists]
  constructor
  · intro env
    exact fairCoin_totalWeight (VEnv.eraseSampleEnv env)
  · trivial

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

theorem horizon : syntaxSteps program = 2 := rfl

noncomputable example : FiniteProgram program := inferInstance

noncomputable def behavioralGame : GameTheory.KernelGame Player :=
  pmfBehavioralKernelGame game

theorem behavioralGame_outcomeKernel
    (σ : behavioralGame.Profile) :
    behavioralGame.outcomeKernel σ = behavioralOutcomeKernelPMFAt game σ := rfl

end SyntaxConstructors
end Examples
end Vegas
