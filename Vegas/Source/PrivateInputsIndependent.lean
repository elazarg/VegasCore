/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

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
hidden cells times a function of the other cells. Then exchanging a player's
hidden cells for fixed ones
changes the mass of every state sharing those cells by the same ratio
(`Vegas.SourceProgram.Setup.initialLaw_splice_mul`), and splices of supported
states are supported (`Vegas.SourceProgram.Setup.splice_mem_support`).

The condition is a device of the argument that compares two late deliveries of
an owner with the same late-delivery key by exchanging the owner's hidden
values: the exchange must change the prior by a common factor. It is not known
to be necessary for the comparison, and an initial law correlating different
players' private values, such as a joint prior over private valuations, does
not satisfy it.

Private cells can instead be independent conditional on a public signal
(`Vegas.SourceProgram.Setup.PrivateInputsIndependentGiven`). The cross-product
identity and supported-splice closure then apply within each signal fiber.
The common-ratio identity additionally requires private splicing to preserve
that signal; hidden-cell agreement alone does not fix a public signal.
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

variable {Public : Type*}

/-- The private-splice cross-product identity within each signal fiber.
For conditional independence, the signal must also be unchanged by private
splicing, as required explicitly by the common-ratio theorem below.
No identity across different signal values is required. -/
def PrivateInputsIndependentGiven (setup : Setup (Player := Player) (L := L))
    (signal : State L setup.context → Public) : Prop :=
  ∀ (who : Player) (first second : State L setup.context), signal first = signal second →
    setup.initialLaw (splice who first second) * setup.initialLaw (splice who second first) =
      setup.initialLaw first * setup.initialLaw second

/-- Within a signal fiber, replacing equal hidden cells changes prior masses
by a common ratio when private splicing preserves the signal. -/
theorem initialLaw_splice_mul (setup : Setup (Player := Player) (L := L))
    (signal : State L setup.context → Public)
    (independent : setup.PrivateInputsIndependentGiven signal)
    (preserves : ∀ (who : Player) (mine others : State L setup.context),
      signal (splice who mine others) = signal others)
    (who : Player) (source : State L setup.context) {first second : State L setup.context}
    (agree : HiddenAgree who second first) (sameSignal : signal first = signal second) :
    setup.initialLaw (splice who source first) * setup.initialLaw second =
      setup.initialLaw (splice who source second) * setup.initialLaw first := by
  have product := independent who (splice who source first) second
    ((preserves who source first).trans sameSignal)
  rw [splice_splice_left, splice_splice_right, splice_of_hiddenAgree agree] at product
  exact product.symm

/-- Splicing supported draws within one signal fiber preserves support. -/
theorem splice_mem_support (setup : Setup (Player := Player) (L := L))
    (signal : State L setup.context → Public)
    (independent : setup.PrivateInputsIndependentGiven signal) (who : Player)
    {first second : State L setup.context} (firstMember : first ∈ setup.initialLaw.support)
    (secondMember : second ∈ setup.initialLaw.support) (sameSignal : signal first = signal second) :
    splice who first second ∈ setup.initialLaw.support := by
  rw [PMF.mem_support_iff] at firstMember secondMember ⊢
  have product := independent who first second sameSignal
  have nonzero : setup.initialLaw first * setup.initialLaw second ≠ 0 :=
    mul_ne_zero firstMember secondMember
  rw [← product] at nonzero
  exact left_ne_zero_of_mul nonzero

end Setup

end SourceProgram

end Vegas
