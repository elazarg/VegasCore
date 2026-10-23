/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseArchivedRecall
import Vegas.Compile.EventGraphPolicyLaw
import Vegas.EventGraph.SequentialLaw

/-! # Original source action words recovered from retired native attempts -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L} {O : Finset VarId}
  (whole : SourceProgram Player L Γ O) (mode : ExecutionMode)

/-- Decoding the recovered physical records appends exactly the actual newly
completed own word, retaining all older retired attempts before that suffix. -/
theorem decodeArchivedHistory_checkpoint_extension
    (retired : List (RetiredCommitAttempt ((toEventGraph whole).withMode mode)))
    (entry current : ((toEventGraph whole).withMode mode).Config) (offset : Nat)
    (before : ∀ record ∈ retired, record.attempt.phase ≤ offset)
    (saved : entry.cut.IsPrefix offset) (retained : entry.history.IsPrefix current.history)
    (who : Player) :
    decodeHistory whole ((PhaseRuntimeState.archivedHistory retired current.history).map
      ((toEventGraph whole).fromModeCompletion mode)) who =
      decodeHistory whole ((PhaseRuntimeState.archivedHistory retired entry.history).map
        ((toEventGraph whole).fromModeCompletion mode)) who ++
      (decodeHistory whole (current.history.map
        ((toEventGraph whole).fromModeCompletion mode)) who).drop
          (decodeHistory whole (entry.history.map
            ((toEventGraph whole).fromModeCompletion mode)) who).length := by
  have recovered := PhaseRuntimeState.archivedHistory_checkpoint_extension retired entry current
    offset before saved retained
  obtain ⟨later, complete⟩ := retained
  have append (first second : List (toEventGraph whole).Completion) :
      decodeHistory whole (first ++ second) who =
        decodeHistory whole first who ++ decodeHistory whole second who := by
    simp only [decodeHistory, ownCompletions, List.filter_append, decodeCompletions_append]
  rw [recovered, ← complete, List.drop_left, List.map_append, append, List.map_append, append]
  simp only [List.drop_left]

/-- Equality of the original owned native records retains the exact decoded
source word, including its original result values and disclosure bits. -/
theorem decodeHistory_fromMode_congr
    (first second : List ((toEventGraph whole).withMode mode).Completion) (who : Player)
    (same : ((toEventGraph whole).withMode mode).ownCompletions who first =
      ((toEventGraph whole).withMode mode).ownCompletions who second) :
    decodeHistory whole (first.map ((toEventGraph whole).fromModeCompletion mode)) who =
      decodeHistory whole (second.map ((toEventGraph whole).fromModeCompletion mode)) who := by
  have own (past : List ((toEventGraph whole).withMode mode).Completion) :
      decodeHistory whole (past.map ((toEventGraph whole).fromModeCompletion mode)) who =
        decodeCompletions whole
          ((((toEventGraph whole).withMode mode).ownCompletions who past).map
            ((toEventGraph whole).fromModeCompletion mode)) := by
    simp only [decodeHistory, ownCompletions, List.filter_map]
    rfl
  rw [own first, own second, same]

end Vegas
