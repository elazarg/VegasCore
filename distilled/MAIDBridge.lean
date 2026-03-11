import distilled.ExprLanguage
import GameTheory.Languages.MAID.Syntax

/-!
# Vegas to MAID backend assumptions

This file records the extra assumptions needed to compile a `Prog` over an
`ExprLanguage` into the finite MAID representation from `GameTheory`.

The protocol language itself stays parametric over `ExprLanguage`. Finiteness
and player enumeration are added only here, where the MAID backend requires:

- finite player set
- finite value domains
- nonempty value domains for non-utility nodes
- canonical encodings of language values as `Fin domainSize`
-/

namespace Distilled

/-- Extra value-domain assumptions needed by the MAID backend.

`FiniteValuation` gives enumeration. `nonemptyVal` is needed because MAID node
domains must have positive size at every non-utility node. -/
structure MAIDValuation (L : ExprLanguage) extends FiniteValuation L where
  nonemptyVal : ∀ τ : L.Ty, Nonempty (L.Val τ)

namespace MAIDValuation

instance instFintypeVal (L : ExprLanguage) (LV : MAIDValuation L) (τ : L.Ty) :
    Fintype (L.Val τ) :=
  LV.toFiniteValuation.fintypeVal τ

instance instNonemptyVal (L : ExprLanguage) (LV : MAIDValuation L) (τ : L.Ty) :
    Nonempty (L.Val τ) :=
  LV.nonemptyVal τ

/-- Positive cardinality of any MAID-compilable value domain. -/
theorem domainSize_pos (L : ExprLanguage) (LV : MAIDValuation L) (τ : L.Ty) :
    0 < LV.toFiniteValuation.domainSize L τ := by
  let _ := instFintypeVal L LV τ
  exact Fintype.card_pos_iff.mpr (instNonemptyVal L LV τ)

/-- A default value, used only as backend compilation scaffolding. -/
noncomputable def defaultVal (L : ExprLanguage) (LV : MAIDValuation L) (τ : L.Ty) :
    L.Val τ :=
  Classical.choice (LV.nonemptyVal τ)

/-- Canonical encoding into the finite node domain used by `MAID.Struct`. -/
noncomputable def encodeVal (L : ExprLanguage) (LV : MAIDValuation L) (τ : L.Ty) :
    L.Val τ ≃ Fin (LV.toFiniteValuation.domainSize L τ) :=
  LV.toFiniteValuation.encodeFin L τ

/-- Decode a MAID node value back into a language value. -/
noncomputable def decodeVal (L : ExprLanguage) (LV : MAIDValuation L) (τ : L.Ty) :
    Fin (LV.toFiniteValuation.domainSize L τ) → L.Val τ :=
  (encodeVal L LV τ).symm

@[simp] theorem decode_encode (L : ExprLanguage) (LV : MAIDValuation L)
    (τ : L.Ty) (v : L.Val τ) :
    decodeVal L LV τ (encodeVal L LV τ v) = v := by
  simp [decodeVal, encodeVal]

@[simp] theorem encode_decode (L : ExprLanguage) (LV : MAIDValuation L)
    (τ : L.Ty) (v : Fin (LV.toFiniteValuation.domainSize L τ)) :
    encodeVal L LV τ (decodeVal L LV τ v) = v := by
  simp [decodeVal, encodeVal]

end MAIDValuation

/-- The full extra backend assumptions needed for compilation to `MAID.Struct`.

This is intentionally backend-specific: the protocol semantics do not need
finite players or finite/nonempty value domains. -/
structure MAIDBackend (Player : Type) [DecidableEq Player] (L : ExprLanguage)
    extends MAIDValuation L where
  fintypePlayer : Fintype Player

namespace MAIDBackend

instance instFintypePlayer {Player : Type} [DecidableEq Player] {L : ExprLanguage}
    (B : MAIDBackend Player L) : Fintype Player :=
  B.fintypePlayer

/-- The MAID node-domain size associated to a language type. -/
noncomputable def domainSize {Player : Type} [DecidableEq Player] {L : ExprLanguage}
    (B : MAIDBackend Player L) (τ : L.Ty) : Nat :=
  B.toMAIDValuation.toFiniteValuation.domainSize L τ

/-- Language values encoded as MAID node values. -/
abbrev NodeVal {Player : Type} [DecidableEq Player] {L : ExprLanguage}
    (B : MAIDBackend Player L) (τ : L.Ty) : Type :=
  Fin (B.domainSize τ)

/-- Canonical value encoding for MAID nodes. -/
noncomputable def encodeVal {Player : Type} [DecidableEq Player] {L : ExprLanguage}
    (B : MAIDBackend Player L) (τ : L.Ty) :
    L.Val τ ≃ NodeVal B τ :=
  B.toMAIDValuation.encodeVal L τ

/-- Positive size of any non-utility node domain produced by the backend. -/
theorem domainSize_pos {Player : Type} [DecidableEq Player] {L : ExprLanguage}
    (B : MAIDBackend Player L) (τ : L.Ty) :
    0 < B.domainSize τ := by
  simpa [MAIDBackend.domainSize] using
    B.toMAIDValuation.domainSize_pos L τ

end MAIDBackend

end Distilled
