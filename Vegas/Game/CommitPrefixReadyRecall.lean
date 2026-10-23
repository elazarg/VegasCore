/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.CommitPrefixFillRecall
import Vegas.Game.CommitAttemptOwnRecall

/-! # Exact source own history at a ready commitment after hidden foreign holes -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeO) (mode : ExecutionMode)

/-- The source completion's own history is exactly the actual native one at
a ready owned commitment. All new-action and interval conditions follow from
readiness; only the already aligned saved checkpoint history is reused. -/
theorem fillCommitPrefix_history_of_ready
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (offset : Nat)
    (rank : ∀ index, (embedding.event index).val = offset + index.val)
    (entryNative native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (entry : SourceProgram.Config Player L Γ) (valid : native.BindingInvariant) {inputs}
    (reachable : native.config.Reachable inputs)
    (retained : entryNative.config.history.IsPrefix native.config.history)
    (saved : entryNative.config.cut.IsPrefix offset) (who : Player)
    (history : entry.history who = decodeHistory whole (entryNative.config.history.map
      ((toEventGraph whole).fromModeCompletion mode)) who)
    (actions : ∀ index action, decodeEventAction whole (embedding.event index) action =
      decodeEventAction (block.prepend suffix) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    (selected : Fin (eventCount (block.prepend suffix))) (atEnd : selected.val = block.length)
    (ready : native.config.cut.Ready (embedding.event selected))
    (acting : ((toEventGraph whole).withMode mode).actor? (embedding.event selected) = some who) :
    (fillCommitPrefix whole block suffix embedding native.config.store entry).history who =
      decodeHistory whole (native.config.history.map
        ((toEventGraph whole).fromModeCompletion mode)) who := by
  let graph := (toEventGraph whole).withMode mode
  have relaxed := (toEventGraph whole).withMode_revealRelaxedOrdered
    (toEventGraph_barrierOrdered whole) mode
  have own (event : graph.EventId) (actor : graph.actor? event = some who) :
      event ∈ native.config.cut.completed ↔ event.val < (embedding.event selected).val :=
    relaxed.ready_visible_iff native.config.cut ready acting
      (EventCode.output_visible_of_actor (graph.nodes event) who actor)
      (IndependentReveals.not_of_actor_eq (by rw [actor, acting]))
      (IndependentReveals.not_of_actor_eq (by rw [actor, acting]))
  have completedOwn : ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
      graph.actor? (embedding.event index) = some who →
        embedding.event index ∈ native.config.cut.completed := by
    intro index inside actor
    apply (own _ actor).mpr
    rw [rank, rank, atEnd]
    omega
  have boundedOwn : ∀ event ∈ native.config.cut.completed, graph.actor? event = some who →
      event.val < offset + block.length := by
    intro event completed actor
    have before := (own event actor).mp completed
    rw [rank, atEnd] at before
    exact before
  rw [fillCommitPrefix_history whole mode block suffix embedding native entry valid who
    completedOwn actions, history]
  have ownRecall := commitAttemptCompletions_ownRecall whole mode block suffix embedding offset
    rank entryNative native valid reachable retained saved who completedOwn boundedOwn
  have decoded := congrArg (fun past => decodeCompletions whole
    (past.map ((toEventGraph whole).fromModeCompletion mode))) ownRecall
  have fromMode (past : List graph.Completion) :
      decodeHistory whole (past.map ((toEventGraph whole).fromModeCompletion mode)) who =
        decodeCompletions whole ((graph.ownCompletions who past).map
          ((toEventGraph whole).fromModeCompletion mode)) := by
    simp only [decodeHistory, ownCompletions, List.filter_map]
    rfl
  rw [← fromMode, ← fromMode] at decoded
  have projected : ((commitAttemptCompletions whole mode block suffix embedding native).map
      ((toEventGraph whole).toModeCompletion mode)).map
        ((toEventGraph whole).fromModeCompletion mode) =
      commitAttemptCompletions whole mode block suffix embedding native := by
    simp only [List.map_map, Function.comp_def, fromModeCompletion_toModeCompletion]
    exact List.map_id _
  rw [List.map_append, projected] at decoded
  have append (first second : List (toEventGraph whole).Completion) :
      decodeHistory whole (first ++ second) who =
        decodeHistory whole first who ++ decodeHistory whole second who := by
    simp only [decodeHistory, ownCompletions, List.filter_append, decodeCompletions_append]
  rw [append] at decoded
  exact decoded.symm

end Vegas
