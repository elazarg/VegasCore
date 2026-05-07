import Vegas.VegasLang
import Vegas.Examples.MatchingPennies

/-!
# VegasLang examples

This file demonstrates that the surface `VegasLang` syntax can present
simultaneous nullable public `yield`s and lower definitionally to the expected
`VegasCore` commit/reveal sequence. It also includes a non-nullable
Matching Pennies presentation that lowers to the canonical checked core game.
-/

namespace Vegas
namespace Examples
namespace MatchingPennies

abbrev Lang (Γ : Ctx) := VegasLang Player Γ
abbrev LangPhase (Γ Δ : Ctx) := VegasLang.Phase Player Γ Δ

/-- Matching Pennies written with the core-shaped, non-nullable `VegasLang`
constructors. -/
noncomputable abbrev canonicalLangProgram : Lang Γ0 :=
  .commit matcherSecret Player.matcher (b := .bool) (.constBool true)
    (.commit mismatcherSecret Player.mismatcher (b := .bool) (.constBool true)
      (.reveal matcherPublic Player.matcher matcherSecret hMatcherSecretΓ2
        (.reveal mismatcherPublic Player.mismatcher
          mismatcherSecret hMismatcherSecretΓ3
          (.ret [(Player.matcher, matcherPayoff),
            (Player.mismatcher, mismatcherPayoff)]))))

/-- The non-nullable surface presentation lowers definitionally to the
canonical checked core program. -/
theorem lower_canonicalLangProgram :
    VegasLang.lower canonicalLangProgram = program := rfl

/-- Equivalently, the non-nullable surface presentation lowers to the program
stored in `game`. -/
theorem lower_canonicalLangProgram_eq_game_prog :
    VegasLang.lower canonicalLangProgram = game.prog := rfl

abbrev ΓYield : Ctx :=
  [(matcherPublic, ⟨BaseTy.option .bool, .pub⟩),
   (mismatcherPublic, ⟨BaseTy.option .bool, .pub⟩),
   (mismatcherSecret, ⟨BaseTy.option .bool, .hidden Player.mismatcher⟩),
   (matcherSecret, ⟨BaseTy.option .bool, .hidden Player.matcher⟩)]

def hMatcherYieldPublic :
    HasVar (erasePubVCtx ΓYield) matcherPublic (BaseTy.option .bool) :=
  .here

def hMismatcherYieldPublic :
    HasVar (erasePubVCtx ΓYield) mismatcherPublic (BaseTy.option .bool) :=
  .there .here

def matcherYieldChoice : Expr (erasePubVCtx ΓYield) .bool :=
  .getD (.var matcherPublic hMatcherYieldPublic) (.constBool false)

def mismatcherYieldChoice : Expr (erasePubVCtx ΓYield) .bool :=
  .getD (.var mismatcherPublic hMismatcherYieldPublic) (.constBool false)

def yieldChoicesMatch : Expr (erasePubVCtx ΓYield) .bool :=
  .eq matcherYieldChoice mismatcherYieldChoice

def matcherYieldPayoff : Expr (erasePubVCtx ΓYield) .int :=
  .ite yieldChoicesMatch (.constInt 1) (.constInt (-1))

def mismatcherYieldPayoff : Expr (erasePubVCtx ΓYield) .int :=
  .ite yieldChoicesMatch (.constInt (-1)) (.constInt 1)

/-- The two public choices of Matching Pennies as one simultaneous surface
yield phase. Each guard is checked against the pre-phase context, so neither
player can refer to the other's same-phase yielded value. -/
noncomputable abbrev simultaneousYieldPhase : LangPhase Γ0 ΓYield :=
  .yield matcherSecret matcherPublic Player.matcher (b := .bool) (.constBool true)
    (.yield mismatcherSecret mismatcherPublic Player.mismatcher (b := .bool)
      (.constBool true)
      .nil)

theorem simultaneousYieldPhase_distinct :
    simultaneousYieldPhase.DistinctActors := by
  simp [VegasYieldPhase.DistinctActors, VegasYieldPhase.actors]

/-- Matching Pennies written with a single simultaneous nullable yield phase. -/
noncomputable abbrev langProgram : Lang Γ0 :=
  .simultaneous simultaneousYieldPhase simultaneousYieldPhase_distinct
    (.ret [(Player.matcher, matcherYieldPayoff),
      (Player.mismatcher, mismatcherYieldPayoff)])

noncomputable abbrev coreProgram : Prog Γ0 :=
  .commit matcherSecret Player.matcher (b := BaseTy.option .bool)
    (Expr.nullableCommitGuard (.constBool true))
    (.commit mismatcherSecret Player.mismatcher (b := BaseTy.option .bool)
      (Expr.nullableCommitGuard (.constBool true))
      (.reveal mismatcherPublic Player.mismatcher mismatcherSecret .here
        (.reveal matcherPublic Player.matcher matcherSecret
          (.there (.there .here))
          (.ret [(Player.matcher, matcherYieldPayoff),
            (Player.mismatcher, mismatcherYieldPayoff)]))))

/-- The surface presentation lowers definitionally to nullable commits followed
by reveals. -/
theorem lower_langProgram :
    VegasLang.lower langProgram = coreProgram := rfl

end MatchingPennies
end Examples
end Vegas
