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
an empty context, and for every law under which only one player's hidden
cells vary
(`Vegas.SourceProgram.Setup.privateInputsIndependent_of_single_owner`). Then
exchanging a player's hidden cells for fixed ones
changes the mass of every state sharing those cells by the same ratio
(`Vegas.SourceProgram.Setup.initialLaw_splice_mul`), and splices of supported
states are supported (`Vegas.SourceProgram.Setup.splice_mem_support`).

The condition is a device of the argument that compares two late deliveries of
an owner with the same late-delivery key by exchanging the owner's hidden
values: the exchange must change the prior by a common factor. It is not known
to be necessary for the comparison, and an initial law correlating different
players' private values, such as a joint prior over private valuations, does
not satisfy it.
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

open Classical in
/-- **One player's hidden cells vary.** An initial law whose supported states
agree with `base` at every cell not hidden by `owner` has independent hidden
cells: the law is the mass of the owner's hidden cells times the indicator that
the other cells are `base`'s. -/
theorem privateInputsIndependent_of_single_owner (setup : Setup (Player := Player) (L := L))
    (owner : Player) (base : State L setup.context)
    (constant : ∀ state ∈ setup.initialLaw.support, ∀ name τ
      (member : HasVar setup.context name τ), τ.hiddenOwner? ≠ some owner →
        state name τ member = base name τ member) :
    setup.PrivateInputsIndependent := by
  let Off := fun state : State L setup.context => ∀ name τ
    (member : HasVar setup.context name τ), τ.hiddenOwner? ≠ some owner →
      state name τ member = base name τ member
  have factor : ∀ state, setup.initialLaw state =
      setup.initialLaw (splice owner state base) * (if Off state then 1 else 0) := by
    intro state
    by_cases off : Off state
    · simp only [off, ↓reduceIte, mul_one]
      congr 1
      funext name τ member
      unfold splice
      split
      · rfl
      · rename_i hidden
        exact off name τ member hidden
    · simp only [off, ↓reduceIte, mul_zero]
      by_contra nonzero
      exact off (constant state ((PMF.mem_support_iff _ _).mpr nonzero))
  intro who first second
  rw [factor (splice who first second), factor (splice who second first), factor first,
    factor second]
  by_cases same : who = owner
  · subst same
    rw [splice_splice_left, splice_splice_left]
    have offSplice : ∀ mine others : State L setup.context,
        Off (splice who mine others) ↔ Off others := by
      intro mine others
      constructor
      · intro off name τ member hidden
        have := off name τ member hidden
        unfold splice at this
        simpa only [hidden, ↓reduceIte] using this
      · intro off name τ member hidden
        unfold splice
        simp only [hidden, ↓reduceIte]
        exact off name τ member hidden
    simp only [offSplice]
    ring
  · have ownerSplice : ∀ mine others : State L setup.context,
        splice owner (splice who mine others) base = splice owner others base := by
      intro mine others
      funext name τ member
      unfold splice
      split
      · rename_i hidden
        have notMine : ¬ τ.hiddenOwner? = some who :=
          fun other => same (Option.some.inj (other.symm.trans hidden))
        simp only [notMine, ↓reduceIte]
      · rfl
    rw [ownerSplice, ownerSplice]
    have offIff : (Off (splice who first second) ∧ Off (splice who second first)) ↔
        (Off first ∧ Off second) := by
      constructor
      · rintro ⟨offFirst, offSecond⟩
        constructor
        · intro name τ member hidden
          by_cases mine : τ.hiddenOwner? = some who
          · have := offFirst name τ member hidden
            unfold splice at this
            simpa only [mine, ↓reduceIte] using this
          · have := offSecond name τ member hidden
            unfold splice at this
            simpa only [mine, ↓reduceIte] using this
        · intro name τ member hidden
          by_cases mine : τ.hiddenOwner? = some who
          · have := offSecond name τ member hidden
            unfold splice at this
            simpa only [mine, ↓reduceIte] using this
          · have := offFirst name τ member hidden
            unfold splice at this
            simpa only [mine, ↓reduceIte] using this
      · rintro ⟨offFirst, offSecond⟩
        constructor
        · intro name τ member hidden
          unfold splice
          split
          · exact offFirst name τ member hidden
          · exact offSecond name τ member hidden
        · intro name τ member hidden
          unfold splice
          split
          · exact offSecond name τ member hidden
          · exact offFirst name τ member hidden
    by_cases offFirst : Off first <;> by_cases offSecond : Off second <;>
      by_cases offOne : Off (splice who first second) <;>
      by_cases offTwo : Off (splice who second first) <;>
      simp only [offFirst, offSecond, offOne, offTwo, ↓reduceIte, mul_one, mul_zero, zero_mul,
        and_true, and_false, iff_true, iff_false, not_true_eq_false] at offIff ⊢
    ring

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

/-- With independent hidden cells, splicing two supported initial states for a
player gives a supported initial state. -/
theorem splice_mem_support (setup : Setup (Player := Player) (L := L))
    (independent : setup.PrivateInputsIndependent) (who : Player)
    {first second : State L setup.context} (firstMember : first ∈ setup.initialLaw.support)
    (secondMember : second ∈ setup.initialLaw.support) :
    splice who first second ∈ setup.initialLaw.support := by
  rw [PMF.mem_support_iff] at firstMember secondMember ⊢
  have product := independent who first second
  have positive : setup.initialLaw first * setup.initialLaw second ≠ 0 :=
    mul_ne_zero firstMember secondMember
  rw [← product] at positive
  exact left_ne_zero_of_mul positive

end Setup

end SourceProgram

end Vegas
