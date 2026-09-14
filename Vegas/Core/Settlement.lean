/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Core.SourceLikelihood

/-! # Source-defined payout bounds for quitting

The programmer supplies a valuation of the written payout. A uniform quitting
bound compares legal complete source executions, including every continuation
and every choice of the other players. This is stronger than an ex-ante expected
payoff comparison. It involves no runtime states, observations, or policies.
-/

namespace Vegas.VegasCore

variable {P : Type} [DecidableEq P] {L : IExpr} {Γ : VCtx P L}

/-- All legal source executions give each player at least its bound, and any
legal execution recording that player's designated quitting value gives at
most that bound. The value is a chosen interpretation of an existing source
action; this certificate does not add quitting syntax to the language. -/
structure QuitPayoutBound (prog : VegasCore P L Γ) (initial : VEnv L Γ)
    {ty : L.Ty} (quit : L.Val ty) (valuation : Payout P → P → ℝ)
    (bound : P → ℝ) : Prop where
  lower : ∀ final : VEnv L (sourceTerminalCtx prog),
    SmallStep.Star ⟨Γ, initial, prog⟩
      ⟨sourceTerminalCtx prog, final, .ret (sourceTerminalPayoffs prog)⟩ →
    ∀ who, bound who ≤ valuation (evalPayoffs (sourceTerminalPayoffs prog) final) who
  quit_upper : ∀ final : VEnv L (sourceTerminalCtx prog),
    SmallStep.Star ⟨Γ, initial, prog⟩
      ⟨sourceTerminalCtx prog, final, .ret (sourceTerminalPayoffs prog)⟩ →
    ∀ who, prog.Chooses who quit final →
      valuation (evalPayoffs (sourceTerminalPayoffs prog) final) who ≤ bound who

end Vegas.VegasCore
