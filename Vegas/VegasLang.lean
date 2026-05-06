import Vegas.Core

/-!
# Surface Vegas language

`VegasLang` is a small surface syntax that lowers to `VegasCore`.

The surface keeps all existing core constructors and adds `simultaneous` blocks.
Blocks have a presentation order for lowering, but they are intended to contain
actions that do not causally depend on each other. The existing syntax-graph
compiler then exposes independent lowered nodes in the same frontier.

Quit handlers are deliberately not part of this syntax yet.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A nonterminal sequence of surface actions intended to be presented as one
simultaneous block. The indices record the context transformer implemented by
the block. -/
inductive VegasLangBlock (P : Type) [DecidableEq P] (L : IExpr) :
    VCtx P L → VCtx P L → Type where
  /-- Empty block. -/
  | nil {Γ : VCtx P L} :
      VegasLangBlock P L Γ Γ
  /-- Deterministic public binding inside a block. -/
  | letExpr {Γ Δ : VCtx P L} (x : VarId) {b : L.Ty}
      (e : L.Expr (erasePubVCtx Γ) b)
      (rest : VegasLangBlock P L ((x, .pub b) :: Γ) Δ) :
      VegasLangBlock P L Γ Δ
  /-- Public sample inside a block. -/
  | sample {Γ Δ : VCtx P L} (x : VarId) {b : L.Ty}
      (D : L.DistExpr (erasePubVCtx Γ) b)
      (rest : VegasLangBlock P L ((x, .pub b) :: Γ) Δ) :
      VegasLangBlock P L Γ Δ
  /-- Strategic hidden commitment inside a block. -/
  | commit {Γ Δ : VCtx P L} (x : VarId) (who : P) {b : L.Ty}
      (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool)
      (rest : VegasLangBlock P L ((x, .hidden who b) :: Γ) Δ) :
      VegasLangBlock P L Γ Δ
  /-- Reveal inside a block. -/
  | reveal {Γ Δ : VCtx P L} (y : VarId) (who : P) (x : VarId) {b : L.Ty}
      (hx : VHasVar Γ x (.hidden who b))
      (rest : VegasLangBlock P L ((y, .pub b) :: Γ) Δ) :
      VegasLangBlock P L Γ Δ

/-- Surface Vegas syntax. This mirrors `VegasCore` and adds a simultaneous
block constructor. -/
inductive VegasLang (P : Type) [DecidableEq P] (L : IExpr) :
    VCtx P L → Type where
  /-- Terminate with public payoff expressions. -/
  | ret {Γ : VCtx P L}
      (payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)) :
      VegasLang P L Γ
  /-- Deterministic public binding. This stays in the surface and lowers to
  core `letExpr`; we are not removing `let` from `VegasCore` for now. -/
  | letExpr {Γ : VCtx P L} (x : VarId) {b : L.Ty}
      (e : L.Expr (erasePubVCtx Γ) b)
      (k : VegasLang P L ((x, .pub b) :: Γ)) :
      VegasLang P L Γ
  /-- Public sample. -/
  | sample {Γ : VCtx P L} (x : VarId) {b : L.Ty}
      (D : L.DistExpr (erasePubVCtx Γ) b)
      (k : VegasLang P L ((x, .pub b) :: Γ)) :
      VegasLang P L Γ
  /-- Strategic hidden commitment. -/
  | commit {Γ : VCtx P L} (x : VarId) (who : P) {b : L.Ty}
      (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool)
      (k : VegasLang P L ((x, .hidden who b) :: Γ)) :
      VegasLang P L Γ
  /-- Reveal a hidden commitment as a fresh public alias. -/
  | reveal {Γ : VCtx P L} (y : VarId) (who : P) (x : VarId) {b : L.Ty}
      (hx : VHasVar Γ x (.hidden who b))
      (k : VegasLang P L ((y, .pub b) :: Γ)) :
      VegasLang P L Γ
  /-- Present a block of nonterminal actions as simultaneous surface syntax.
  The lowering keeps a deterministic presentation order; semantic simultaneity
  is recovered by the protocol graph when block actions are causally
  independent. -/
  | simultaneous {Γ Δ : VCtx P L}
      (block : VegasLangBlock P L Γ Δ)
      (k : VegasLang P L Δ) :
      VegasLang P L Γ

namespace VegasLangBlock

/-- Lower a simultaneous block by prefixing its actions onto a core
continuation. -/
def lowerWith :
    {Γ Δ : VCtx P L} →
      VegasLangBlock P L Γ Δ → VegasCore P L Δ → VegasCore P L Γ
  | _, _, .nil, k => k
  | _, _, .letExpr x e rest, k =>
      .letExpr x e (lowerWith rest k)
  | _, _, .sample x D rest, k =>
      .sample x D (lowerWith rest k)
  | _, _, .commit x who R rest, k =>
      .commit x who R (lowerWith rest k)
  | _, _, .reveal y who x hx rest, k =>
      .reveal y who x hx (lowerWith rest k)

@[simp] theorem lowerWith_nil
    {Γ : VCtx P L} (k : VegasCore P L Γ) :
    lowerWith (VegasLangBlock.nil (P := P) (L := L)) k = k := rfl

end VegasLangBlock

namespace VegasLang

/-- Public alias for simultaneous block syntax under the `VegasLang`
namespace. -/
abbrev Block (P : Type) [DecidableEq P] (L : IExpr) :
    VCtx P L → VCtx P L → Type :=
  VegasLangBlock P L

/-- Lower surface Vegas to the maintained core syntax. -/
def lower :
    {Γ : VCtx P L} → VegasLang P L Γ → VegasCore P L Γ
  | _, .ret payoffs => .ret payoffs
  | _, .letExpr x e k => .letExpr x e (lower k)
  | _, .sample x D k => .sample x D (lower k)
  | _, .commit x who R k => .commit x who R (lower k)
  | _, .reveal y who x hx k => .reveal y who x hx (lower k)
  | _, .simultaneous block k => VegasLangBlock.lowerWith block (lower k)

@[simp] theorem lower_ret
    {Γ : VCtx P L}
    (payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)) :
    lower (VegasLang.ret (P := P) (L := L) payoffs) =
      VegasCore.ret payoffs := rfl

@[simp] theorem lower_simultaneous
    {Γ Δ : VCtx P L}
    (block : VegasLangBlock P L Γ Δ)
    (k : VegasLang P L Δ) :
    lower (VegasLang.simultaneous block k) =
      VegasLangBlock.lowerWith block (lower k) := rfl

end VegasLang

end Vegas
