/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Payoff
import Vegas.Compile.SourceChoice
import Vegas.Compile.SourceOutcomeExecution
import Vegas.Core.Settlement

/-! # Source payout interpretations and graph quitting bounds

Compiled payout expressions depend only on public graph fields. Written-source
execution and recorded-choice correspondence transport the programmer's uniform
quitting condition to the graph, independently of any message implementation.
-/

noncomputable section

namespace Vegas.WFProgram

open EventGraph ToEventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

def graphPayoutUtility (source : WFProgram Player L)
    (valuation : Payout Player → Player → ℝ) (missing : Player → ℝ) :
    (compile source.core).graph.PublicUtility :=
  Graph.PublicUtility.ofPayoffs _ (compile source.core).payoffs
    (fun payoff hpayoff ref href => ((compile source.core).payoffsWF payoff hpayoff ref href).1)
    valuation missing

/-- Public graph payout valuation agrees with the independently decoded
written-source terminal outcome. -/
theorem graphPayoutUtility_terminal (source : WFProgram Player L)
    (valuation : Payout Player → Player → ℝ) (missing : Player → ℝ)
    (cfg : ReachableConfig (compile source.core).graph)
    (hterminal : Terminal (compile source.core).graph cfg.1) (who : Player) :
    (source.graphPayoutUtility valuation missing).eval cfg.1.store who =
      valuation (evalPayoffs (sourceTerminalPayoffs source.core.prog)
        (decodeSourceOutcome source.core.prog source.core.fresh
          (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
          cfg hterminal)) who := by
  change (evalPayoffs? (compile source.core).payoffs cfg.1.store).elim (missing who) _ = _
  exact congrArg (fun payout : Option (Payout Player) =>
    payout.elim (missing who) (fun result => valuation result who))
    (evalPayoffs?_eq_decodedSourceOutcome source.core.prog source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
      cfg hterminal)

/-- The source-only quitting condition certifies the backend's graph-only
condition. No native utility comparison is an assumption. -/
theorem graphQuitBound_of_source (source : WFProgram Player L) {ty : L.Ty}
    (nullValue : L.Val ty) (valuation : Payout Player → Player → ℝ)
    (missing bound : Player → ℝ)
    (hbound : source.core.prog.QuitPayoutBound source.core.env nullValue valuation bound) :
    (source.graphPayoutUtility valuation missing).QuitBound nullValue bound where
  lower cfg hterminal who := by
    rw [source.graphPayoutUtility_terminal valuation missing cfg hterminal who]
    exact hbound.lower _ (decodeSourceOutcome_reachable source.core cfg hterminal) who
  quitting cfg hterminal who producer guard hcommit hvalue := by
    rw [source.graphPayoutUtility_terminal valuation missing cfg hterminal who]
    exact hbound.quit_upper _ (decodeSourceOutcome_reachable source.core cfg hterminal) who
      (source.source_chooses_of_commit_store cfg hterminal producer who guard hcommit
        nullValue hvalue)

end Vegas.WFProgram
