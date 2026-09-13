/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SourceOutcome

/-! # Reading source outcomes from compiled states

Only terminal graph configurations decode to source outcomes. Nonterminal
states return `none`; this observation never supplies a fictitious completed
source execution. Decoding includes sealed fields for analysis, without making
them part of any player's operational observation.
-/

noncomputable section

namespace Vegas.ToEventGraph

open EventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Partial source-outcome decoding for an actual compiled graph state. -/
def observeSourceOutcome (program : GraphProgram P L)
    (state : ReachableConfig (compile program).graph) :
    Option (VEnv L (sourceTerminalCtx program.prog)) := by
  classical
  exact if hterminal : Terminal (compile program).graph state.1 then
    some (decodeSourceOutcome program.prog program.fresh
      (BuildState.fromInitial (initialState program.Γ program.env program.wctx)) state hterminal)
  else none

theorem observeSourceOutcome_of_terminal (program : GraphProgram P L)
    (state : ReachableConfig (compile program).graph)
    (hterminal : Terminal (compile program).graph state.1) :
    observeSourceOutcome program state =
      some (decodeSourceOutcome program.prog program.fresh
        (BuildState.fromInitial (initialState program.Γ program.env program.wctx))
        state hterminal) := by
  rw [observeSourceOutcome, dif_pos hterminal]

theorem observeSourceOutcome_eq_none_iff (program : GraphProgram P L)
    (state : ReachableConfig (compile program).graph) :
    observeSourceOutcome program state = none ↔ ¬ Terminal (compile program).graph state.1 := by
  classical
  simp [observeSourceOutcome]

end Vegas.ToEventGraph
