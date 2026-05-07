import Vegas.VegasLang

/-!
# Nullable yield example

An impossible surface yield guard lowers to a feasible core commit because the
internal optional value may be `none`. The public continuation is forced to
handle the revealed option value.
-/

namespace Vegas
namespace Examples
namespace NullableCommit

abbrev Player := Nat

def secret : VarId := 0
def publicVar : VarId := 1

def actor : Player := 0
def victim : Player := 1

abbrev Γ0 : VCtx Player simpleExpr := []

abbrev Γ1 : VCtx Player simpleExpr :=
  [(secret, .hidden 0 (BaseTy.option .bool))]

abbrev Γ2 : VCtx Player simpleExpr :=
  [(publicVar, .pub (BaseTy.option .bool)),
   (secret, .hidden 0 (BaseTy.option .bool))]

def hSecretΓ1 : VHasVar Γ1 secret (.hidden actor (BaseTy.option .bool)) :=
  .here

def hPublicΓ2 : HasVar (erasePubVCtx Γ2) publicVar (BaseTy.option .bool) :=
  .here

/-- A guard that rejects every non-null Boolean action. -/
def impossibleBoolGuard : Expr ((secret, .bool) :: eraseVCtx Γ0) .bool :=
  .constBool false

def publicChoice : Expr (erasePubVCtx Γ2) (BaseTy.option .bool) :=
  .var publicVar hPublicΓ2

/-- The payoff distinguishes the forced-null case from an actual value. -/
def payoff : Expr (erasePubVCtx Γ2) .int :=
  .ite (.isNone publicChoice) (.constInt 1) (.constInt 0)

def payoffEnv (move : Option Bool) : Env Val (erasePubVCtx Γ2) :=
  Env.cons (x := publicVar) move (Env.empty Val)

@[simp] theorem payoffEnv_get_public (move : Option Bool) :
    payoffEnv move publicVar (BaseTy.option .bool) hPublicΓ2 = move := rfl

/-- Incorrect handling: null harms the counterparty, while the nulling player
pays no penalty. -/
def badActorPayoff : Expr (erasePubVCtx Γ2) .int :=
  .constInt 0

def badVictimPayoff : Expr (erasePubVCtx Γ2) .int :=
  .ite (.isNone publicChoice) (.constInt (-10)) (.constInt 0)

/-- Correct handling: null is treated as an abort/punishment for the player who
failed to produce a value. -/
def goodActorPayoff : Expr (erasePubVCtx Γ2) .int :=
  .ite (.isNone publicChoice) (.constInt (-10)) (.constInt 0)

def goodVictimPayoff : Expr (erasePubVCtx Γ2) .int :=
  .constInt 0

def NonCostlyGriefing
    (actorPayoff victimPayoff : Option Bool → Int)
    (abort honest : Option Bool) : Prop :=
  actorPayoff abort ≥ actorPayoff honest ∧
    victimPayoff abort < victimPayoff honest

def BadActorUtility (move : Option Bool) : Int :=
  evalExpr badActorPayoff (payoffEnv move)

def BadVictimUtility (move : Option Bool) : Int :=
  evalExpr badVictimPayoff (payoffEnv move)

def GoodActorUtility (move : Option Bool) : Int :=
  evalExpr goodActorPayoff (payoffEnv move)

def GoodVictimUtility (move : Option Bool) : Int :=
  evalExpr goodVictimPayoff (payoffEnv move)

theorem bad_null_is_noncostly_griefing :
    NonCostlyGriefing BadActorUtility BadVictimUtility
      Option.none (some false) := by
  simp [NonCostlyGriefing, BadActorUtility, BadVictimUtility,
    badActorPayoff, badVictimPayoff, publicChoice,
    evalExpr, Env.get, payoffEnv_get_public]

theorem good_null_is_punished :
    GoodActorUtility Option.none < GoodActorUtility (some false) := by
  simp [GoodActorUtility, goodActorPayoff, publicChoice, evalExpr, Env.get,
    payoffEnv_get_public]

theorem good_null_not_noncostly_griefing :
    ¬ NonCostlyGriefing GoodActorUtility GoodVictimUtility
      Option.none (some false) := by
  intro h
  exact (not_le_of_gt good_null_is_punished) h.1

def langProgram : VegasLang Player Γ0 :=
  VegasLang.yield secret publicVar actor impossibleBoolGuard
    (.ret [(0, payoff)])

def coreProgram : VegasCore Player simpleExpr Γ0 :=
  .commit secret actor (b := BaseTy.option .bool)
    (Expr.nullableCommitGuard impossibleBoolGuard)
    (.reveal publicVar actor secret hSecretΓ1
      (.ret [(0, payoff)]))

def badHandlingProgram : VegasLang Player Γ0 :=
  VegasLang.yield secret publicVar actor impossibleBoolGuard
    (.ret [(actor, badActorPayoff), (victim, badVictimPayoff)])

def goodHandlingProgram : VegasLang Player Γ0 :=
  VegasLang.yield secret publicVar actor impossibleBoolGuard
    (.ret [(actor, goodActorPayoff), (victim, goodVictimPayoff)])

theorem lower_langProgram :
    VegasLang.lower langProgram = coreProgram := rfl

theorem lowered_program_legal :
    Legal (VegasLang.lower langProgram) := by
  dsimp [langProgram, VegasLang.lower, Legal]
  exact ⟨nullableCommitGuard_satisfiable impossibleBoolGuard, trivial⟩

end NullableCommit
end Examples
end Vegas
