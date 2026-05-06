import Vegas.VegasLang

/-!
# Nullable commit aliases

`VegasLang` is now concrete over `simpleExpr` and contains nullable commit
constructors directly. This module keeps the older `VegasLang.Nullable.commit`
spelling as a small compatibility alias.
-/

namespace Vegas

namespace VegasLang
namespace Nullable

abbrev commit {P : Type} [DecidableEq P] {Γ : VCtx P simpleExpr}
    (x : VarId) (who : P) {b : BaseTy} [CommitPayloadTy b] [DefaultVal b]
    (R : Expr ((x, b) :: eraseVCtx Γ) .bool)
    (k : VegasLang P ((x, .hidden who (BaseTy.option b)) :: Γ)) :
    VegasLang P Γ :=
  VegasLang.commitNullable x who R k

@[simp] theorem lower_commit {P : Type} [DecidableEq P]
    {Γ : VCtx P simpleExpr}
    (x : VarId) (who : P) {b : BaseTy} [CommitPayloadTy b] [DefaultVal b]
    (R : Expr ((x, b) :: eraseVCtx Γ) .bool)
    (k : VegasLang P ((x, .hidden who (BaseTy.option b)) :: Γ)) :
    VegasLang.lower (commit x who R k) =
      VegasCore.commit x who (b := BaseTy.option b)
        (Expr.nullableCommitGuard R) (VegasLang.lower k) := rfl

theorem legal_lower_commit {P : Type} [DecidableEq P]
    {Γ : VCtx P simpleExpr}
    (x : VarId) (who : P) {b : BaseTy} [CommitPayloadTy b] [DefaultVal b]
    (R : Expr ((x, b) :: eraseVCtx Γ) .bool)
    (k : VegasLang P ((x, .hidden who (BaseTy.option b)) :: Γ))
    (hlegal : Legal (VegasLang.lower k)) :
    Legal (VegasLang.lower (commit x who R k)) :=
  VegasLang.legal_lower_commitNullable x who R k hlegal

end Nullable
end VegasLang

namespace VegasLangBlock
namespace Nullable

abbrev commit {P : Type} [DecidableEq P] {Γ Δ : VCtx P simpleExpr}
    (x : VarId) (who : P) {b : BaseTy} [CommitPayloadTy b] [DefaultVal b]
    (R : Expr ((x, b) :: eraseVCtx Γ) .bool)
    (rest : VegasLangBlock P
      ((x, .hidden who (BaseTy.option b)) :: Γ) Δ) :
    VegasLangBlock P Γ Δ :=
  VegasLangBlock.commitNullable x who R rest

@[simp] theorem lowerWith_commit {P : Type} [DecidableEq P]
    {Γ Δ : VCtx P simpleExpr}
    (x : VarId) (who : P) {b : BaseTy} [CommitPayloadTy b] [DefaultVal b]
    (R : Expr ((x, b) :: eraseVCtx Γ) .bool)
    (rest : VegasLangBlock P
      ((x, .hidden who (BaseTy.option b)) :: Γ) Δ)
    (k : VegasCore P simpleExpr Δ) :
    VegasLangBlock.lowerWith (commit x who R rest) k =
      VegasCore.commit x who (b := BaseTy.option b)
        (Expr.nullableCommitGuard R)
        (VegasLangBlock.lowerWith rest k) := rfl

end Nullable
end VegasLangBlock

end Vegas
