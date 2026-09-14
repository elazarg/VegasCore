/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Core.SourceLikelihood

/-! # Source-defined payout bounds for quitting

The programmer supplies a valuation of the written payout. A quitting cap
bounds every legal settlement recording the player's designated default. The
corresponding floor can quantify over all legal executions or only the support
of unilateral deviations against fixed opponents. Both conditions are pointwise,
stronger than ex-ante expected payoff comparisons, and entirely source-defined.
-/

namespace Vegas.VegasCore

variable {P : Type} [DecidableEq P] {L : IExpr} {Γ : VCtx P L}

/-- An upper bound on every legal source settlement recording this player's
designated quitting value. The settlement witness may use arbitrary opponents. -/
def QuitPayoutCap (prog : VegasCore P L Γ) (initial : VEnv L Γ)
    {ty : L.Ty} (quit : L.Val ty) (valuation : Payout P → P → ℝ)
    (bound : P → ℝ) : Prop :=
  ∀ final : VEnv L (sourceTerminalCtx prog),
    SmallStep.Star ⟨Γ, initial, prog⟩
      ⟨sourceTerminalCtx prog, final, .ret (sourceTerminalPayoffs prog)⟩ →
    ∀ who, prog.Chooses who quit final →
      valuation (evalPayoffs (sourceTerminalPayoffs prog) final) who ≤ bound who

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
  quit_upper : prog.QuitPayoutCap initial quit valuation bound

/-- The source floor need hold only against the fixed opponents under analysis.
It is pointwise on every unilateral deviation's support, not merely an expected
payoff bound or a condition on equilibrium play. Quitting settlements still
require the global cap because their source witnesses need not retain opponents. -/
structure QuitPayoutBoundAgainst (prog : VegasCore P L Γ) (initial : VEnv L Γ)
    {ty : L.Ty} (quit : L.Val ty) (valuation : Payout P → P → ℝ)
    (bound : P → ℝ) (profile : SourceBehavioralProfile prog) : Prop where
  lower : ∀ who (alternative : SourceBehavioralPolicy prog who)
    (final : VEnv L (sourceTerminalCtx prog)),
    final ∈ (denoteSource prog (GameTheory.Profile.update (sig := sourceGameSignature prog)
      profile who alternative) initial).support →
      bound who ≤ valuation (evalPayoffs (sourceTerminalPayoffs prog) final) who
  quit_upper : prog.QuitPayoutCap initial quit valuation bound

/-- A global source floor supplies the fixed-opponent condition at any profile. -/
theorem QuitPayoutBound.against {prog : VegasCore P L Γ} {initial : VEnv L Γ}
    {ty : L.Ty} {quit : L.Val ty} {valuation : Payout P → P → ℝ} {bound : P → ℝ}
    (hbound : prog.QuitPayoutBound initial quit valuation bound)
    (profile : SourceBehavioralProfile prog) :
    prog.QuitPayoutBoundAgainst initial quit valuation bound profile where
  lower who alternative final hfinal :=
    hbound.lower final (denoteSource_support_star prog
      (GameTheory.Profile.update (sig := sourceGameSignature prog) profile who alternative)
      initial final hfinal) who
  quit_upper := hbound.quit_upper

end Vegas.VegasCore
