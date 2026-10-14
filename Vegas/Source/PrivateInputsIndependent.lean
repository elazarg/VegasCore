/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Setup

/-! # Independent private initial cells

A player's hidden initial cells are its private inputs and its initial
commitments (`Vegas.CellTy.hiddenOwner?`). Splicing two initial
states for a player takes that player's hidden cells from the first and every
other cell from the second (`Vegas.SourceProgram.splice`).

An initial law makes each player's hidden cells independent of the rest when,
for every player, splicing two states both ways preserves the product of their
masses (`Vegas.SourceProgram.Setup.PrivateInputsIndependent`); for a law with
nonnegative masses this says the law factors as a function of the player's
hidden cells times a function of the other cells. It holds for every law over
an empty context. Then exchanging a player's hidden cells for fixed ones
changes the mass of every state sharing those cells by the same ratio
(`Vegas.SourceProgram.Setup.initialLaw_splice_mul`).
-/

namespace Vegas

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- The player whose hidden initial cell a cell of this type is: the owner of a
private input or of a commitment, and nobody for public cells. -/
def CellTy.hiddenOwner? : CellTy Player L → Option Player
  | .privateInput owner _ => some owner
  | .commitment owner _ => some owner
  | .publicData _ | .publication _ => none

namespace SourceProgram

/-- **Splicing for a player.** The state with the player's hidden cells from
`mine` and every other cell from `others`. -/
def splice {Γ : SourceCtx Player L} (who : Player) (mine others : State L Γ) : State L Γ :=
  fun name τ member => if τ.hiddenOwner? = some who then mine name τ member
    else others name τ member

/-- Two states agree on a player's hidden cells. -/
def HiddenAgree {Γ : SourceCtx Player L} (who : Player) (first second : State L Γ) : Prop :=
  ∀ name τ (member : HasVar Γ name τ), τ.hiddenOwner? = some who →
    first name τ member = second name τ member

/-- Splicing in a spliced state's hidden cells takes them from its source. -/
theorem splice_splice_left {Γ : SourceCtx Player L} (who : Player)
    (source first second : State L Γ) :
    splice who (splice who source first) second = splice who source second := by
  funext name τ member
  unfold splice
  split <;> simp_all

/-- Splicing into a spliced state keeps only the other cells of its second
source. -/
theorem splice_splice_right {Γ : SourceCtx Player L} (who : Player)
    (mine first second : State L Γ) :
    splice who mine (splice who first second) = splice who mine second := by
  funext name τ member
  unfold splice
  split <;> simp_all

/-- Splicing the hidden cells a state already has gives the state back. -/
theorem splice_of_hiddenAgree {Γ : SourceCtx Player L} {who : Player}
    {first second : State L Γ} (agree : HiddenAgree who first second) :
    splice who first second = second := by
  funext name τ member
  unfold splice
  split
  · rename_i hidden
    exact agree name τ member hidden
  · rfl

/-- Over an empty context every splice is the second state. -/
theorem splice_nil (who : Player) (mine others : State L []) : splice who mine others = others := by
  funext name τ member
  cases member

namespace Setup

variable [IExpr.ResultTypes L]

/-- **Independent hidden initial cells.** For every player, the initial law
gives two states the same product of masses as their two splices for that
player: the player's hidden initial cells are independent of all the other
cells. -/
def PrivateInputsIndependent (setup : Setup (Player := Player) (L := L)) : Prop :=
  ∀ (who : Player) (first second : State L setup.context),
    setup.initialLaw (splice who first second) * setup.initialLaw (splice who second first) =
      setup.initialLaw first * setup.initialLaw second

/-- An initial law over an empty context has independent hidden cells. -/
theorem privateInputsIndependent_of_nil (setup : Setup (Player := Player) (L := L))
    (empty : setup.context = []) : setup.PrivateInputsIndependent := by
  intro who first second
  obtain ⟨context, namesNodup, initialLaw, obligations, program, accounts⟩ := setup
  dsimp only at empty first second ⊢
  subst empty
  rw [splice_nil, splice_nil, mul_comm]

/-- **The prior ratio of a hidden exchange is common.** With independent hidden
cells, exchanging a player's hidden cells for those of `source` multiplies the
mass of two states sharing their hidden cells by the same ratio. -/
theorem initialLaw_splice_mul (setup : Setup (Player := Player) (L := L))
    (independent : setup.PrivateInputsIndependent) (who : Player)
    (source : State L setup.context) {first second : State L setup.context}
    (agree : HiddenAgree who second first) :
    setup.initialLaw (splice who source first) * setup.initialLaw second =
      setup.initialLaw (splice who source second) * setup.initialLaw first := by
  have product := independent who (splice who source first) second
  rw [splice_splice_left, splice_splice_right, splice_of_hiddenAgree agree] at product
  exact product.symm

end Setup

end SourceProgram

end Vegas
