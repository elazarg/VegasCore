/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitPhaseAutomatic

/-! # The actual typed attempt of an entirely excluded commitment block -/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Every slot is an automatic source action when the complete owner roster
is excluded. The attempt neither adds an exclusion nor records an owned move. -/
def automaticAttempt {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (entry : Config Player L Γ) (excluded : Finset Player)
    (all : block.owners ⊆ excluded) :
    block.Attempt entry excluded (block.automatic entry) excluded := by
  induction block with
  | nil => exact .nil entry excluded
  | commit name owner fresh guard rest ih =>
      exact .excluded (all (Finset.mem_insert_self _ _))
        (ih (automaticCommit name owner _ entry)
          (fun who member => all (Finset.mem_insert_of_mem member)))

end Vegas.SourceProgram.CommitPrefix
