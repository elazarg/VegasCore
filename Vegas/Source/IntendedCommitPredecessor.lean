/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.IntendedForPlayer

/-! # Own admissibility reflected through a completed commitment -/

noncomputable section

namespace Vegas.SourceProgram.Config

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {owner who : Player}
  {payload : L.Ty}

omit [IExpr.ResultTypes L] in
/-- A commitment cannot repair any earlier violation of this player's source
invariant. This statement keeps the complete original typed action history. -/
theorem IntendedFor.commit_before (fresh : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ owner name payload) (entry : Config Player L Γ)
    (result : PublicationResult (L.Val payload))
    (after : (commitSuccessor name guard entry result).IntendedFor who (insert name O)) :
    entry.IntendedFor who O where
  unique := (List.nodup_cons.mp after.unique).2
  accounted := by
    intro author value read cell
    have previous := after.accounted (.there cell)
    have different : read ≠ name := fun same => fresh (same ▸ cell.mem_map_fst)
    simpa only [commitSuccessor, Revelations.weaken_there, Revelation.isRevealed_weaken,
      Finset.mem_insert, different, false_or] using previous
  bound cell := after.bound (.there cell)
  publishes := by
    intro read value cell opened
    have before : ((commitSuccessor name guard entry result).revelations
        (.there cell)).isRevealed = true := by
      simpa only [commitSuccessor, Revelations.weaken_there, Revelation.isRevealed_weaken]
        using opened
    have kept := after.publishes (.there cell) before
    simpa only [commitSuccessor, Revelations.weaken_there, Revelation.result_weaken,
      Env.cons_get_there] using kept
  predicted := by
    intro obligation member own value bound
    have kept := after.predicted obligation.weaken
      (List.mem_cons_of_mem _ (List.mem_map_of_mem member)) own value bound
    exact (SourceGuard.predicts_weaken _ _ _ _).symm.trans kept

omit [IExpr.ResultTypes L] in
/-- A completed own binding in a debt-free configuration is an accepted typed
value, with its guard judged at the original pre-binding observation. -/
theorem IntendedFor.commit_result (guard : SourceGuard L Γ who name payload)
    (entry : Config Player L Γ) (result : PublicationResult (L.Val payload))
    (after : (commitSuccessor name guard entry result).IntendedFor who (insert name O)) :
    ∃ value, result = .success value ∧
      guard.predicts (sourceObserve who entry.state) value = true := by
  obtain ⟨value, equal⟩ := after.bound .here
  change result = .success value at equal
  refine ⟨value, equal, ?_⟩
  have predicted := after.predicted
    ⟨who, name, payload, .here, guard.weaken⟩ (List.mem_cons_self) rfl value equal
  exact (SourceGuard.predicts_weaken _ _ _ _).symm.trans predicted

end Vegas.SourceProgram.Config
