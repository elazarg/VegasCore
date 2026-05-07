import Vegas.Strategic.BehavioralPMF

/-!
# Matching Pennies

A checked Vegas encoding of Matching Pennies. The Boolean commitments use
`true` for heads and `false` for tails.
-/

namespace Vegas
namespace Examples
namespace MatchingPennies

inductive Player where
  | matcher
  | mismatcher
deriving DecidableEq, Repr, Fintype

abbrev Ctx := VCtx Player simpleExpr
abbrev Prog (Γ : Ctx) := VegasCore Player simpleExpr Γ

def matcherSecret : VarId := 0
def mismatcherSecret : VarId := 1
def matcherPublic : VarId := 2
def mismatcherPublic : VarId := 3

abbrev Γ0 : Ctx := []
abbrev Γ2 : Ctx :=
  [(mismatcherSecret, .hidden Player.mismatcher .bool),
   (matcherSecret, .hidden Player.matcher .bool)]
abbrev Γ3 : Ctx :=
  [(matcherPublic, .pub .bool),
   (mismatcherSecret, .hidden Player.mismatcher .bool),
   (matcherSecret, .hidden Player.matcher .bool)]
abbrev Γ4 : Ctx :=
  [(mismatcherPublic, .pub .bool),
   (matcherPublic, .pub .bool),
   (mismatcherSecret, .hidden Player.mismatcher .bool),
   (matcherSecret, .hidden Player.matcher .bool)]

def hMatcherSecretΓ2 :
    VHasVar Γ2 matcherSecret (.hidden Player.matcher .bool) :=
  .there .here

def hMismatcherSecretΓ3 :
    VHasVar Γ3 mismatcherSecret (.hidden Player.mismatcher .bool) :=
  .there .here

def hMismatcherPublicPayoff :
    HasVar (erasePubVCtx Γ4) mismatcherPublic .bool :=
  .here

def hMatcherPublicPayoff :
    HasVar (erasePubVCtx Γ4) matcherPublic .bool :=
  .there .here

def matcherChoice : Expr (erasePubVCtx Γ4) .bool :=
  .var matcherPublic hMatcherPublicPayoff

def mismatcherChoice : Expr (erasePubVCtx Γ4) .bool :=
  .var mismatcherPublic hMismatcherPublicPayoff

def choicesMatch : Expr (erasePubVCtx Γ4) .bool :=
  .eq matcherChoice mismatcherChoice

def matcherPayoff : Expr (erasePubVCtx Γ4) .int :=
  .ite choicesMatch (.constInt 1) (.constInt (-1))

def mismatcherPayoff : Expr (erasePubVCtx Γ4) .int :=
  .ite choicesMatch (.constInt (-1)) (.constInt 1)

def payoffEnv (matcher mismatcher : Bool) :
    Env simpleExpr.Val (erasePubVCtx Γ4) :=
  Env.cons (x := mismatcherPublic) mismatcher
    (Env.cons (x := matcherPublic) matcher (Env.empty simpleExpr.Val))

theorem payoffs_zero_sum (matcher mismatcher : Bool) :
    evalExpr matcherPayoff (payoffEnv matcher mismatcher) +
      evalExpr mismatcherPayoff (payoffEnv matcher mismatcher) = 0 := by
  cases matcher <;> cases mismatcher <;>
    rfl

noncomputable abbrev program : Prog Γ0 :=
  .commit matcherSecret Player.matcher (b := .bool) (.constBool true)
    (.commit mismatcherSecret Player.mismatcher (b := .bool) (.constBool true)
      (.reveal matcherPublic Player.matcher matcherSecret hMatcherSecretΓ2
        (.reveal mismatcherPublic Player.mismatcher
          mismatcherSecret hMismatcherSecretΓ3
          (.ret [(Player.matcher, matcherPayoff),
            (Player.mismatcher, mismatcherPayoff)]))))

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

end MatchingPennies
end Examples
end Vegas
