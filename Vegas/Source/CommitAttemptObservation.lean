/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryBlockEmbedding
import Vegas.Source.ObservationRecall

/-! # Recovering surviving owners' entry views from actual commitment attempts -/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [IExpr.ResultTypes L] in
/-- An already excluded foreign binding adds no own action, so the existing
back projection still recovers a surviving owner's entire prior decision view. -/
theorem back_automaticCommit_view {Γ : SourceCtx Player L} {payload : L.Ty}
    (who owner : Player) (different : owner ≠ who) (name : VarId)
    (config : Config Player L Γ) :
    ((automaticCommit name owner payload config).view who).back (decide (owner = who)) =
      config.view who := by
  simp only [different, decide_false, Config.view, automaticCommit, back_sourceObserve,
    Bool.false_eq_true, ↓reduceIte]

namespace CommitPrefix

/-- The existing source view projection recovers the full entry observation of
a surviving owner from an actual attempt, even when foreign owners were excluded
or became excluded. Original failed typed results are ordinary recorded actions. -/
theorem Attempt.entryView {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    {block : CommitPrefix Γ O Δ P} {entry : Config Player L Γ} {excluded : Finset Player}
    {finished : Config Player L Δ} {after : Finset Player}
    (attempt : block.Attempt entry excluded finished after)
    (suffix : SourceProgram Player L Δ P) (who : Player) (survives : who ∉ after) :
    ProtocolView.entryView who (block.prepend suffix)
        (ProtocolState.observe who (block.prepend suffix)
          (block.liftPoint suffix (ProtocolState.entry suffix finished))) =
      entry.view who := by
  induction attempt with
  | nil config excluded => exact ProtocolView.entryView_observe_entry who suffix config
  | @active Γ Δ O P name owner payload fresh guard rest config excluded finished after
      active choice missed missingFailure later ih =>
      change (ProtocolView.entryView who (rest.prepend suffix)
        (ProtocolState.observe who (rest.prepend suffix)
          (rest.liftPoint suffix (ProtocolState.entry suffix finished)))).back
            (decide (owner = who)) = config.view who
      rw [ih suffix survives]
      exact back_commit_view who name guard config choice
  | @excluded Γ Δ O P name owner payload fresh guard rest config excluded finished after
      inactive later ih =>
      have different : owner ≠ who := by
        intro same
        exact survives (same ▸ later.excluded_subset inactive)
      change (ProtocolView.entryView who (rest.prepend suffix)
        (ProtocolState.observe who (rest.prepend suffix)
          (rest.liftPoint suffix (ProtocolState.entry suffix finished)))).back
            (decide (owner = who)) = config.view who
      rw [ih suffix survives]
      exact back_automaticCommit_view who owner different name config

end CommitPrefix

end Vegas.SourceProgram
