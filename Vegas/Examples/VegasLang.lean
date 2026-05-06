import Vegas.VegasLang
import Vegas.Examples.MatchingPennies

/-!
# VegasLang examples

This file demonstrates that the surface `VegasLang` syntax can present an
existing core example with simultaneous commitments and lower definitionally to
the established `VegasCore` program.
-/

namespace Vegas
namespace Examples
namespace MatchingPennies

abbrev Lang (Γ : Ctx) := VegasLang Player simpleExpr Γ
abbrev LangBlock (Γ Δ : Ctx) := VegasLang.Block Player simpleExpr Γ Δ

/-- The two hidden commitments of Matching Pennies as one simultaneous surface
block. The block lowers in presentation order, while the syntax graph sees the
two independent commits in one frontier. -/
noncomputable abbrev simultaneousCommitBlock : LangBlock Γ0 Γ2 :=
  .commit matcherSecret Player.matcher (b := .bool) (.constBool true)
    (.commit mismatcherSecret Player.mismatcher (b := .bool) (.constBool true)
      .nil)

/-- Matching Pennies written with `VegasLang.simultaneous` for the initial
commitments. -/
noncomputable abbrev langProgram : Lang Γ0 :=
  .simultaneous simultaneousCommitBlock
    (.reveal matcherPublic Player.matcher matcherSecret hMatcherSecretΓ2
      (.reveal mismatcherPublic Player.mismatcher
        mismatcherSecret hMismatcherSecretΓ3
        (.ret [(Player.matcher, matcherPayoff),
          (Player.mismatcher, mismatcherPayoff)])))

/-- The surface presentation lowers definitionally to the existing core
program. -/
theorem lower_langProgram :
    VegasLang.lower langProgram = program := rfl

/-- Equivalently, it lowers to the checked example program stored in `game`. -/
theorem lower_langProgram_eq_game_prog :
    VegasLang.lower langProgram = game.prog := rfl

end MatchingPennies
end Examples
end Vegas
