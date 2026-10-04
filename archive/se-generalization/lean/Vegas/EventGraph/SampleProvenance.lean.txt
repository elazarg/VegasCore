/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Execution

/-! # Persistent outputs of constant public chance laws

A completed constant-law sample retains a value in the original draw's
support through every later graph step. The law comes from the actual
evaluator, independently of strategic responses or scheduler timing.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

theorem Config.Reachable.constant_sample_output
    {inputs : graph.Inputs} {config : graph.Config}
    (reachable : config.Reachable inputs)
    (event : graph.EventId) (payload : L.Ty)
    (law : PublicDist graph.layout payload)
    (outputEq : graph.outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .sample payload law)
    (draw : PMF (L.Val payload))
    (evaluates : ∀ store, law.eval? store = some draw)
    (completed : event ∈ config.cut.completed) :
    ∃ value ∈ draw.support,
      (⟨.inr event, outputEq⟩ : FieldRef graph.layout (.publicData payload)).get?
        config.store = some value := by
  induction reachable with
  | initial =>
      change event ∈ (∅ : Finset graph.EventId) at completed
      simp at completed
  | @step before prior added ready action after supported ih =>
      have nextCut := Config.step_cut before added ready action after supported
      rw [nextCut, EventOrder.Cut.mem_complete] at completed
      rcases completed with rfl | completedBefore
      · have actionEq : cast (congrArg EventField.Action outputEq.symm) PUnit.unit = action := by
          have unitEq : cast (congrArg EventField.Action outputEq) action = PUnit.unit :=
            Subsingleton.elim _ _
          rw [← unitEq]
          simp
        have step := before.step_eq_map_of_code event ready outputEq
          (.sample payload law) codeEq PUnit.unit draw (evaluates before.store)
        rw [actionEq] at step
        rw [step, PMF.support_map] at supported
        obtain ⟨value, chosen, rfl⟩ := supported
        refine ⟨value, chosen, ?_⟩
        change cast (congrArg (fun kind => Option kind.Value) outputEq)
          ((before.complete event ready action
            (cast (congrArg EventField.Value outputEq.symm) value)).outputs event) = some value
        rw [Config.complete_output_same]
        have roundtrip {left right : EventField Player L} (same : left = right)
            (result : right.Value) :
            cast (congrArg (fun kind => Option kind.Value) same)
              (some (cast (congrArg EventField.Value same.symm) result)) = some result := by
          cases same
          rfl
        exact roundtrip outputEq value
      · obtain ⟨value, chosen, stored⟩ := ih completedBefore
        refine ⟨value, chosen, ?_⟩
        exact (⟨.inr event, outputEq⟩ : FieldRef graph.layout (.publicData payload)).get?_preserved
          before.store after.store
          (fun field result present => before.step_store_of_some after added ready action
            supported field result present) value stored

end Vegas.EventGraph
