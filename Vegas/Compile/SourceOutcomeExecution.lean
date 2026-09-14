/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SourceAdequacy
import Vegas.Compile.SourceOutcome

/-! # Operational legality of decoded source outcomes -/

noncomputable section

namespace Vegas.ToEventGraph

open EventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

private theorem sourceConfig_eq (left right : SourceConfig P L)
    (hctx : left.ctx = right.ctx) (henv : HEq left.env right.env)
    (hcont : HEq left.cont right.cont) : left = right := by
  cases left
  cases right
  simp_all

private theorem ret_heq {Γ Δ : VCtx P L}
    {left : List (P × L.Expr (erasePubVCtx Γ) L.int)}
    {right : List (P × L.Expr (erasePubVCtx Δ) L.int)}
    (hctx : Γ = Δ) (hpayoffs : HEq left right) :
    HEq (VegasCore.ret left : VegasCore P L Γ)
      (VegasCore.ret right : VegasCore P L Δ) := by
  subst Δ
  have heq : left = right := eq_of_heq hpayoffs
  subst right
  rfl

/-- Decoding a terminal reachable compiled state produces a legal execution
of the original written source program. -/
theorem decodeSourceOutcome_reachable (source : GraphProgram P L)
    (cfg : ReachableConfig (compile source).graph)
    (hterminal : Terminal (compile source).graph cfg.1) :
    SmallStep.Star
      { ctx := source.Γ, env := source.env, cont := source.prog }
      { ctx := sourceTerminalCtx source.prog,
        env := decodeSourceOutcome source.prog source.fresh
          (BuildState.fromInitial (initialState source.Γ source.env source.wctx))
          cfg hterminal,
        cont := .ret (sourceTerminalPayoffs source.prog) } := by
  obtain ⟨terminalEnv, hstar, _hpayout, hagrees⟩ :=
    compile_sourceStar source cfg.1 cfg.2 hterminal
  have henv := (compile source).decodeTerminalSource_eq cfg hterminal terminalEnv hagrees
  have hctx := compileCore_terminalCtx_eq_sourceTerminalCtx source.prog source.fresh
    (BuildState.fromInitial (initialState source.Γ source.env source.wctx))
  have hpayoffs : HEq (compile source).sourcePayoffs
      (sourceTerminalPayoffs source.prog) := by
    simpa [compile] using compileCore_sourcePayoffs_heq source.prog source.fresh
      (BuildState.fromInitial (initialState source.Γ source.env source.wctx))
  have hfinal :
      ({ ctx := sourceTerminalCtx source.prog,
         env := decodeSourceOutcome source.prog source.fresh
           (BuildState.fromInitial (initialState source.Γ source.env source.wctx))
           cfg hterminal,
         cont := .ret (sourceTerminalPayoffs source.prog) } : SourceConfig P L) =
      { ctx := (compile source).terminalCtx, env := terminalEnv,
        cont := .ret (compile source).sourcePayoffs } := by
    apply sourceConfig_eq
    · exact hctx.symm
    · simpa [decodeSourceOutcome, compile] using henv
    · exact ret_heq hctx.symm hpayoffs.symm
  rw [hfinal]
  exact hstar

end Vegas.ToEventGraph
