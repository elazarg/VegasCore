/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SealedRounds
import Vegas.Compile.SourceOutcomeExecution

/-! # Programmed payout utilities for sealed round games -/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- Utility obtained by valuing the payout written by the source program. -/
def sourcePayoutUtility (valuation : Payout Player → Player → ℝ)
    (outcome : VEnv L (sourceTerminalCtx source.core.prog)) (who : Player) : ℝ :=
  valuation (evalPayoffs (sourceTerminalPayoffs source.core.prog) outcome) who

/-- Utility obtained from the publicly reconstructible native payout. The
explicit fallback is used only when public payout evaluation returns `none`. -/
def nativePayoutUtility {nullValue : L.Val ty} {window : Nat}
    {compilation : SealedCompilation source ty}
    (model : RoundModel compilation nullValue window)
    (valuation : Payout Player → Player → ℝ) (missing : Player → ℝ)
    (next : model.game.sig.Outcome) (who : Player) : ℝ :=
  (compilation.publicPayout? next.native.application.visible.events).elim
    (missing who) (fun payout => valuation payout who)

namespace RoundModel

variable {compilation : SealedCompilation source ty} {nullValue : L.Val ty} {window : Nat}

/-- Public payout valuation automatically agrees with the written source
payout on every normal decoded execution. -/
theorem normalUtilityAgreement_sourcePayout (model : RoundModel compilation nullValue window)
    (valuation : Payout Player → Player → ℝ) (missing : Player → ℝ) :
    model.NormalUtilityAgreement
      (sourcePayoutUtility (source := source) valuation)
      (nativePayoutUtility model valuation missing) := by
  intro cfg next hterminal hinvariant _hcomplete _htimeouts hdecode who
  rw [nativePayoutUtility, compilation.publicPayout?_eq_graph_of_decode
    nullValue window next.native.application hinvariant cfg.1 hdecode]
  have hpayout := evalPayoffs?_eq_decodedSourceOutcome source.core.prog source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
      cfg hterminal
  change (evalPayoffs? (compile source.core).payoffs cfg.1.store).elim
      (missing who) (fun payout => valuation payout who) = _
  rw [show evalPayoffs? (compile source.core).payoffs cfg.1.store = _ from by
    simpa [compile] using hpayout]
  rw [observeSourceOutcome_of_terminal source.core cfg hterminal]
  rfl

end RoundModel

end Vegas.SealedCompilation
