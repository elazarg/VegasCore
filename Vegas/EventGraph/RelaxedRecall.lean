/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Recall
import Vegas.EventGraph.RevealRelaxation

/-! # Original own-action ordering under relaxed reveal dependencies -/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Relaxing independent foreign revelations preserves every owner's original
chronological rank order, including all dependent action values. -/
theorem RevealRelaxedOrdered.ownEventIds_pairwise
    {inputs : graph.Inputs} {config : graph.Config}
    (relaxed : graph.RevealRelaxedOrdered) (reachable : Config.Reachable inputs config)
    (who : Player) :
    (graph.ownEventIds who config.history).Pairwise fun left right =>
      left.val < right.val := by
  induction reachable with
  | initial => simp [ownEventIds, ownCompletions, Config.initial]
  | step priorReachable event ready action next supported ih =>
      rename_i prior
      rw [Config.step_history prior event ready action next supported]
      rw [ownEventIds, ownCompletions, List.filter_append]
      simp only [List.filter_cons, List.filter_nil]
      split
      · rename_i owned
        simp only [List.map_append, List.map_cons, List.map_nil]
        change (graph.ownEventIds who prior.history ++ [event]).Pairwise _
        rw [List.pairwise_append]
        refine ⟨ih, by simp, ?_⟩
        intro earlier earlierMem later laterMem
        have : later = event := by simpa using laterMem
        subst later
        have completionMem : ∃ completion ∈ graph.ownCompletions who prior.history,
            completion.event = earlier := by
          simpa [ownEventIds] using earlierMem
        obtain ⟨completion, completionOwn, rfl⟩ := completionMem
        have filtered := List.mem_filter.mp completionOwn
        have earlierCompleted : completion.event ∈ prior.cut.completed := by
          apply (prior.history_exact completion.event).mp
          exact List.mem_map.mpr ⟨completion, filtered.1, rfl⟩
        have earlierOwned : graph.actor? completion.event = some who :=
          of_decide_eq_true filtered.2
        by_contra notEarlier
        have different : event ≠ completion.event := by
          intro same
          subst event
          exact ready.1 earlierCompleted
        have later : event.val < completion.event.val := by
          exact Nat.lt_of_le_of_ne (Nat.le_of_not_gt notEarlier)
            (fun equal => different (Fin.ext equal))
        have predecessor : event ∈ graph.order.predecessors completion.event :=
          relaxed completion.event event
            ((mem_barrierOrder graph.outputLayout event completion.event).mpr
              ⟨later, EventCode.barrierRelated_of_visible (graph.nodes completion.event) who
                earlierOwned _
                (graph.nodes event)
                  (EventCode.output_visible_of_actor (graph.nodes event) who
                    (of_decide_eq_true owned))⟩)
            (IndependentReveals.not_of_actor_eq (by
              rw [of_decide_eq_true owned, earlierOwned]))
        exact ready.1 (prior.cut.predecessor_closed earlierCompleted predecessor)
      · simp only [List.map_append, List.map_nil]
        change (graph.ownEventIds who prior.history ++ []).Pairwise _
        simpa using ih

end Vegas.EventGraph
