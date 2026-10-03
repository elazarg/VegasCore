/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceReachedDecoding

/-! # The next source prefix is unavailable before its ready event completes

The current ready event has no stored output. The actual source decoder reads
that field before constructing its successor, so its next-prefix result is
`none`. Waiting therefore needs no artificial unfinished readout label.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {profile : BehavioralProfile setup.program}

/-- The real next-prefix decoder cannot supply the current event's unwritten
typed cell, including when its eventual result may be failure. -/
theorem SourceResidual.next_decode_none {rank : Nat} {config : (graph setup).Config}
    (residual : SourceResidual setup profile rank config)
    (event : (graph setup).EventId) (atRank : event.val = rank)
    (ready : config.cut.Ready event) :
    sourceServicePrefix? setup (rank + 1) config = none := by
  obtain ⟨Γ, names, program, residualProfile, source, refs, embedding, refsBefore, aligned,
    _admitted, _effective, _supports, lift, _recover, _recovered, _commutes, _steps,
    _injective, transport, _checkpoint⟩ := residual
  have absent (index : Fin (eventCount program))
      (ranked : (embedding.event index).val = rank) :
      (embedding.ref index).get? config.store = none := by
    have same : embedding.event index = event := Fin.ext (ranked.trans atRank.symm)
    have outputNone : config.outputs (embedding.event index) = none := by
      cases stored : config.outputs (embedding.event index) with
      | none => rfl
      | some value =>
          have finished := (config.output_available (embedding.event index)).mp (by simp [stored])
          exact (ready.1 (same ▸ finished)).elim
    unfold OutputEmbedding.ref EventGraph.FieldRef.get?
    change cast (congrArg (fun kind => Option kind.Value) (embedding.layout_eq index))
      (config.outputs (embedding.event index)) = none
    rw [outputNone]
    have castNone {first second : EventGraph.EventField Player L} (equal : first = second) :
        cast (congrArg (fun kind => Option kind.Value) equal)
          (none : Option first.Value) = none := by
      cases equal
      rfl
    exact castNone (embedding.layout_eq index)
  unfold sourceServicePrefix?
  rw [transport]
  cases program with
  | ret payoffs => rfl
  | sample name fresh law next =>
      have missing := absent ⟨0, by simp [eventCount]⟩ (by
        simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩)
      simp only [decodeSourcePrefix?, decodeState?, ContextRefs.cons]
      rw [missing]
      rfl
  | commit name owner fresh guard next =>
      have missing := absent ⟨0, by simp [eventCount]⟩ (by
        simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩)
      simp only [decodeSourcePrefix?, decodeState?, ContextRefs.cons]
      rw [missing]
      rfl
  | reveal published owner name fresh binding unresolved next =>
      have missing := absent ⟨0, by simp [eventCount]⟩ (by
        simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩)
      simp only [decodeSourcePrefix?, decodeState?, ContextRefs.cons]
      rw [missing]
      rfl

end Vegas
