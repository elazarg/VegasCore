/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitPhase
import Vegas.Source.FailureRevelations

/-! # Immutable failure meanings through arbitrary typed commitment attempts -/

namespace Vegas.SourceProgram.CommitPrefix

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- Fresh source commitment names preserve the context's distinct-name invariant. -/
theorem names_nodup (block : CommitPrefix Γ O Δ P) :
    (Γ.map Prod.fst).Nodup → (Δ.map Prod.fst).Nodup := by
  induction block with
  | nil => exact id
  | commit name owner fresh guard rest ih =>
      intro unique
      apply ih
      exact List.nodup_cons.mpr ⟨fresh, unique⟩

omit [IExpr.ResultTypes L] in
/-- Active choices and automatic excluded slots preserve failure propagation
through revelations, including a failed accepted binding with no public miss. -/
theorem Attempt.preservesFailures {block : CommitPrefix Γ O Δ P}
    {entry : Config Player L Γ} {excluded : Finset Player}
    {finished : Config Player L Δ} {afterExcluded : Finset Player}
    (attempt : block.Attempt entry excluded finished afterExcluded) :
    Revelations.PreservesFailures entry.revelations entry.state →
      Revelations.PreservesFailures finished.revelations finished.state := by
  induction attempt with
  | nil => exact id
  | @active Γ O Δ P name owner payload fresh guard rest config excluded finished afterExcluded
      active choice missed missingFailure later ih =>
      intro valid
      exact ih (valid.weaken (name := name) (cell := .commitment owner payload) choice)
  | @excluded Γ O Δ P name owner payload fresh guard rest config excluded finished afterExcluded
      inactive later ih =>
      intro valid
      exact ih (valid.weaken (name := name) (cell := .commitment owner payload)
        PublicationResult.failure)

end Vegas.SourceProgram.CommitPrefix
