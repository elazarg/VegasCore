/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Honest

/-! # Sequences of revelations of initialized commitments

`RevealOnly` is a property of existing source syntax. It introduces no executor,
admission mode, or restriction on disclosure choices. Owners may recur, and the
initial state may contain arbitrarily correlated private data. Validity of the
initial bindings is a separate setup premise.

The existing open-obligation index accounts for every reveal. From an empty
guard registry, every disclosure simply publishes the bound result or failure;
no guard condition has to be supplied by an analysis of this class.
-/

noncomputable section

namespace Vegas.State

variable {Player : Type} {L : IExpr} {Γ : SourceCtx Player L}

/-- Every commitment cell contains an actual value. This is an initial-state
premise for the reveal service, not a restriction on disclosure or payoffs. -/
def BindingsOpenable (state : State L Γ) : Prop :=
  ∀ {name owner payload} (ref : HasVar Γ name (.commitment owner payload)),
    ∃ value, state.get ref = .success value

end Vegas.State

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A fixed sequence of reveals followed by settlement, with no new bindings
or chance instructions. Disclosure and withholding are both still legal. -/
def RevealOnly : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    SourceProgram Player L Γ O → Prop
  | _, _, .ret _ => True
  | _, _, .reveal _ _ _ _ _ _ next => RevealOnly next
  | _, _, .sample .. | _, _, .commit .. => False

end Vegas.SourceProgram
