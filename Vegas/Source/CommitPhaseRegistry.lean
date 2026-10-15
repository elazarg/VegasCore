/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitPhase
import Vegas.Source.RegistryFailureExtension

/-! # Static guard registration along typed commitment blocks -/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The compiler retains a guard for every syntactic commitment slot, including
the slots that recovery subsequently services automatically. -/
def guardRegistry : {Γ Δ : SourceCtx Player L} → {O P : Finset VarId} →
    CommitPrefix Γ O Δ P → Registry Γ → Registry Δ
  | _, _, _, _, .nil, registry => registry
  | _, _, _, _, .commit name owner _fresh guard rest, registry =>
      let obligation : Obligation _ :=
        { owner := owner, subject := name, payload := _, source := .here,
          guard := guard.weaken }
      rest.guardRegistry (obligation :: registry.weaken)

end Vegas.SourceProgram.CommitPrefix
