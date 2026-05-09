import Vegas.Strategic.BehavioralPMF

/-!
# Battle of the Sexes

A checked Vegas encoding of Battle of the Sexes. The Boolean commitments use
`true` for opera and `false` for football.
-/

namespace Vegas
namespace Examples
namespace BattleOfTheSexes

inductive Player where
  | operaFan
  | footballFan
deriving DecidableEq, Repr, Fintype

abbrev Ctx := VCtx Player simpleExpr
abbrev Prog (Γ : Ctx) := VegasCore Player simpleExpr Γ

def operaFanSecret : VarId := 0
def footballFanSecret : VarId := 1
def operaFanPublic : VarId := 2
def footballFanPublic : VarId := 3

abbrev Γ0 : Ctx := []
abbrev Γ2 : Ctx :=
  [(footballFanSecret, .hidden Player.footballFan .bool),
   (operaFanSecret, .hidden Player.operaFan .bool)]
abbrev Γ3 : Ctx :=
  [(operaFanPublic, .pub .bool),
   (footballFanSecret, .hidden Player.footballFan .bool),
   (operaFanSecret, .hidden Player.operaFan .bool)]
abbrev Γ4 : Ctx :=
  [(footballFanPublic, .pub .bool),
   (operaFanPublic, .pub .bool),
   (footballFanSecret, .hidden Player.footballFan .bool),
   (operaFanSecret, .hidden Player.operaFan .bool)]

def hOperaFanSecretΓ2 :
    VHasVar Γ2 operaFanSecret (.hidden Player.operaFan .bool) :=
  .there .here

def hFootballFanSecretΓ3 :
    VHasVar Γ3 footballFanSecret (.hidden Player.footballFan .bool) :=
  .there .here

def hFootballFanPublicPayoff :
    HasVar (erasePubVCtx Γ4) footballFanPublic .bool :=
  .here

def hOperaFanPublicPayoff :
    HasVar (erasePubVCtx Γ4) operaFanPublic .bool :=
  .there .here

def operaFanChoice : Expr (erasePubVCtx Γ4) .bool :=
  .var operaFanPublic hOperaFanPublicPayoff

def footballFanChoice : Expr (erasePubVCtx Γ4) .bool :=
  .var footballFanPublic hFootballFanPublicPayoff

def sameVenue : Expr (erasePubVCtx Γ4) .bool :=
  .eq operaFanChoice footballFanChoice

def operaFanPayoff : Expr (erasePubVCtx Γ4) .int :=
  .ite sameVenue
    (.ite operaFanChoice (.constInt 2) (.constInt 1))
    (.constInt 0)

def footballFanPayoff : Expr (erasePubVCtx Γ4) .int :=
  .ite sameVenue
    (.ite operaFanChoice (.constInt 1) (.constInt 2))
    (.constInt 0)

def payoffEnv (operaFan footballFan : Bool) :
    Env simpleExpr.Val (erasePubVCtx Γ4) :=
  Env.cons (x := footballFanPublic) footballFan
    (Env.cons (x := operaFanPublic) operaFan (Env.empty simpleExpr.Val))

theorem opera_opera_payoff :
    evalExpr operaFanPayoff (payoffEnv true true) = 2 ∧
      evalExpr footballFanPayoff (payoffEnv true true) = 1 := by
  exact ⟨rfl, rfl⟩

theorem football_football_payoff :
    evalExpr operaFanPayoff (payoffEnv false false) = 1 ∧
      evalExpr footballFanPayoff (payoffEnv false false) = 2 := by
  exact ⟨rfl, rfl⟩

/-- Complete payoff table of the source-level Boolean choices. -/
theorem payoff_table (operaFan footballFan : Bool) :
    (evalExpr operaFanPayoff (payoffEnv operaFan footballFan),
      evalExpr footballFanPayoff (payoffEnv operaFan footballFan)) =
      match operaFan, footballFan with
      | true, true => (2, 1)
      | true, false => (0, 0)
      | false, true => (0, 0)
      | false, false => (1, 2) := by
  cases operaFan <;> cases footballFan <;> rfl

theorem mismatch_payoff (operaFan footballFan : Bool)
    (h : operaFan ≠ footballFan) :
    evalExpr operaFanPayoff (payoffEnv operaFan footballFan) = 0 ∧
      evalExpr footballFanPayoff (payoffEnv operaFan footballFan) = 0 := by
  cases operaFan <;> cases footballFan <;>
    simp_all [payoffEnv, operaFanPayoff, footballFanPayoff, sameVenue,
      operaFanChoice, footballFanChoice, hOperaFanPublicPayoff,
      hFootballFanPublicPayoff, Env.get, Env.cons, evalExpr]

theorem operaFan_match_opera_gt :
    evalExpr operaFanPayoff (payoffEnv true true) >
      evalExpr operaFanPayoff (payoffEnv false true) := by
  decide

theorem operaFan_match_football_gt :
    evalExpr operaFanPayoff (payoffEnv false false) >
      evalExpr operaFanPayoff (payoffEnv true false) := by
  decide

theorem footballFan_match_opera_gt :
    evalExpr footballFanPayoff (payoffEnv true true) >
      evalExpr footballFanPayoff (payoffEnv true false) := by
  decide

theorem footballFan_match_football_gt :
    evalExpr footballFanPayoff (payoffEnv false false) >
      evalExpr footballFanPayoff (payoffEnv false true) := by
  decide

abbrev ActionProfile := Player → Bool

def actionPayoff (σ : ActionProfile) : Player → Int
  | Player.operaFan =>
      evalExpr operaFanPayoff
        (payoffEnv (σ Player.operaFan) (σ Player.footballFan))
  | Player.footballFan =>
      evalExpr footballFanPayoff
        (payoffEnv (σ Player.operaFan) (σ Player.footballFan))

def IsActionNash (σ : ActionProfile) : Prop :=
  ∀ who alt, actionPayoff σ who ≥
    actionPayoff (Function.update σ who alt) who

def operaProfile : ActionProfile
  | Player.operaFan => true
  | Player.footballFan => true

def footballProfile : ActionProfile
  | Player.operaFan => false
  | Player.footballFan => false

theorem operaProfile_actionNash : IsActionNash operaProfile := by
  intro who alt
  cases who <;> cases alt <;> decide

theorem footballProfile_actionNash : IsActionNash footballProfile := by
  intro who alt
  cases who <;> cases alt <;> decide

theorem actionNash_eq_opera_or_football
    (σ : ActionProfile) (hσ : IsActionNash σ) :
    σ = operaProfile ∨ σ = footballProfile := by
  cases hopera : σ Player.operaFan <;>
    cases hfootball : σ Player.footballFan
  · right
    funext who
    cases who <;> simp [footballProfile, hopera, hfootball]
  · have hdev := hσ Player.operaFan true
    have hbad :
        evalExpr operaFanPayoff (payoffEnv true true) ≤
          evalExpr operaFanPayoff (payoffEnv false true) := by
      simpa [actionPayoff, hopera, hfootball] using hdev
    exact False.elim ((not_le_of_gt operaFan_match_opera_gt) hbad)
  · have hdev := hσ Player.footballFan true
    have hbad :
        evalExpr footballFanPayoff (payoffEnv true true) ≤
          evalExpr footballFanPayoff (payoffEnv true false) := by
      simpa [actionPayoff, hopera, hfootball] using hdev
    exact False.elim ((not_le_of_gt footballFan_match_opera_gt) hbad)
  · left
    funext who
    cases who <;> simp [operaProfile, hopera, hfootball]

theorem actionNash_iff_opera_or_football (σ : ActionProfile) :
    IsActionNash σ ↔ σ = operaProfile ∨ σ = footballProfile := by
  constructor
  · exact actionNash_eq_opera_or_football σ
  · intro h
    rcases h with h | h
    · subst σ
      exact operaProfile_actionNash
    · subst σ
      exact footballProfile_actionNash

noncomputable abbrev program : Prog Γ0 :=
  .commit operaFanSecret Player.operaFan (b := .bool) (.constBool true)
    (.commit footballFanSecret Player.footballFan (b := .bool) (.constBool true)
      (.reveal operaFanPublic Player.operaFan operaFanSecret hOperaFanSecretΓ2
        (.reveal footballFanPublic Player.footballFan
          footballFanSecret hFootballFanSecretΓ3
          (.ret [(Player.operaFan, operaFanPayoff),
            (Player.footballFan, footballFanPayoff)]))))

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

end BattleOfTheSexes
end Examples
end Vegas
