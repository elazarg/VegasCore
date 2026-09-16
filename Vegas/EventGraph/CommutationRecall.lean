/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Commutation
import Vegas.EventGraph.Information

/-! # Fixed-action commutation with original-action recall

The local two-step diamond remains valid when the store projection is paired
with every player's chronological list of original dependent actions.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L} {schema : graph.LogicalSchema}

/-- Store contents together with every player's retained original actions. -/
def storeRecall (graph : Vegas.EventGraph Player L) (config : graph.Config) :=
  (config.store, fun who => graph.ownCompletions who config.history)

/-- Distinct simultaneously ready strategic events cannot have the same actor
when same-owner source order is part of the information discipline. -/
theorem InformationDiscipline.ready_actor_ne
    (discipline : graph.InformationDiscipline schema) {config : graph.Config}
    {left right : graph.EventId} (leftReady : config.cut.Ready left)
    (rightReady : config.cut.Ready right) (different : left ≠ right)
    {leftOwner rightOwner : Player}
    (leftActor : graph.actor? left = some leftOwner)
    (rightActor : graph.actor? right = some rightOwner) :
    leftOwner ≠ rightOwner := by
  intro sameOwner
  subst rightOwner
  rcases lt_or_gt_of_ne (fun equal => different (Fin.ext equal)) with earlier | earlier
  · exact leftReady.1 (rightReady.2
      (discipline.same_owner_ordered earlier leftActor rightActor))
  · exact rightReady.1 (leftReady.2
      (discipline.same_owner_ordered earlier rightActor leftActor))

/-- Swapping two simultaneously ready fixed completions preserves every
player's filtered original-action history. -/
theorem ownCompletions_complete_comm
    (discipline : graph.InformationDiscipline schema) (config : graph.Config)
    {left right : graph.EventId} (leftReady : config.cut.Ready left)
    (rightReady : config.cut.Ready right) (different : left ≠ right)
    (leftAction : graph.Action left) (rightAction : graph.Action right) :
    (fun who => graph.ownCompletions who
      (config.history ++ [⟨left, leftAction⟩, ⟨right, rightAction⟩])) =
    (fun who => graph.ownCompletions who
      (config.history ++ [⟨right, rightAction⟩, ⟨left, leftAction⟩])) := by
  funext who
  simp only [ownCompletions, List.filter_append, List.filter_cons, List.filter_nil]
  by_cases leftOwned : graph.actor? left = some who
  · have rightNotOwned : graph.actor? right ≠ some who := by
      intro rightOwned
      exact (discipline.ready_actor_ne leftReady rightReady different
        leftOwned rightOwned) rfl
    simp [leftOwned, rightNotOwned]
  · by_cases rightOwned : graph.actor? right = some who
    · simp [leftOwned, rightOwned]
    · simp [leftOwned, rightOwned]

omit [DecidableEq Player] in
private theorem stepThen_history {config : graph.Config} {first second : graph.EventId}
    (firstReady : config.cut.Ready first) (secondReady : config.cut.Ready second)
    (different : first ≠ second) (firstAction : graph.Action first)
    (secondAction : graph.Action second) (result : graph.Config)
    (member : result ∈ (stepThen config first second firstReady secondReady different
      firstAction secondAction).support) :
    result.history = config.history ++
      [⟨first, firstAction⟩, ⟨second, secondAction⟩] := by
  unfold stepThen at member
  rw [FinDist.support_bindOnSupport] at member
  simp only [Set.mem_iUnion] at member
  obtain ⟨afterFirst, firstMember, secondMember⟩ := member
  calc
    result.history = afterFirst.history ++ [⟨second, secondAction⟩] :=
      Config.step_history afterFirst second _ secondAction result secondMember
    _ = (config.history ++ [⟨first, firstAction⟩]) ++ [⟨second, secondAction⟩] := by
      rw [Config.step_history config first firstReady firstAction afterFirst firstMember]
    _ = config.history ++ [⟨first, firstAction⟩, ⟨second, secondAction⟩] := by simp

private theorem stepThen_map_storeRecall
    (config : graph.Config) (first second : graph.EventId)
    (firstReady : config.cut.Ready first) (secondReady : config.cut.Ready second)
    (different : first ≠ second) (firstAction : graph.Action first)
    (secondAction : graph.Action second) :
    (stepThen config first second firstReady secondReady different
      firstAction secondAction).map (storeRecall graph) =
    ((stepThen config first second firstReady secondReady different
      firstAction secondAction).map Config.store).map fun store =>
        (store, fun who => graph.ownCompletions who
          (config.history ++ [⟨first, firstAction⟩, ⟨second, secondAction⟩])) := by
  rw [FinDist.map_comp]
  apply FinDist.map_congr_of_eq_on_support
  intro result member
  simp only [storeRecall]
  rw [stepThen_history firstReady secondReady different firstAction secondAction result member]
  rfl

/-- Fixed actions at distinct simultaneously ready events commute after
projecting to both the typed store and all players' original-action recall. -/
theorem stepThen_map_storeRecall_comm
    (discipline : graph.InformationDiscipline schema) (config : graph.Config)
    (left right : graph.EventId)
    (leftReady : config.cut.Ready left) (rightReady : config.cut.Ready right)
    (different : left ≠ right)
    (leftAction : graph.Action left) (rightAction : graph.Action right) :
    (stepThen config left right leftReady rightReady different
      leftAction rightAction).map (storeRecall graph) =
    (stepThen config right left rightReady leftReady different.symm
      rightAction leftAction).map (storeRecall graph) := by
  rw [stepThen_map_storeRecall, stepThen_map_storeRecall]
  have recallEq := ownCompletions_complete_comm discipline config leftReady rightReady
    different leftAction rightAction
  rw [stepThen_map_store_comm config left right leftReady rightReady different
    leftAction rightAction, recallEq]

end Vegas.EventGraph
