/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryInformation

/-! # Truthful proposal labels over semantic recovery moves -/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} {L : IExpr}

/-- A truthful proposal may accompany the semantic withheld successor. Its
value is read from the actual pre-state, never supplied by this label. -/
structure ProposalRecoveryMove (Player : Type) (L : IExpr) where
  semantic : CommitRecoveryMove Player L
  proposed : Bool

namespace ProposalRecoveryMove

/-- Only a semantic withheld reveal needs an additional proposal label. -/
def Valid (move : ProposalRecoveryMove Player L) : Prop :=
  move.proposed = true → ∃ owner name, move.semantic.action = .reveal owner name false

def ordinary (move : CommitRecoveryMove Player L) : ProposalRecoveryMove Player L :=
  ⟨move, false⟩

@[simp] theorem ordinary_valid (move : CommitRecoveryMove Player L) :
    (ordinary move).Valid := by
  intro impossible
  cases impossible

/-- Both ordinary truthful disclosure and failed delivery expose a proposal. -/
def discloses (move : ProposalRecoveryMove Player L) : Bool :=
  OwnAction.disclosure (some move.semantic.action) || move.proposed

@[simp] theorem ordinary_semantic (move : CommitRecoveryMove Player L) :
    (ordinary move).semantic = move := rfl

end ProposalRecoveryMove

end Vegas.SourceProgram
