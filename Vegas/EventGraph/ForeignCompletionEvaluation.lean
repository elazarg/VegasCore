/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.ForeignCompletionSequence
import Vegas.EventGraph.Commutation

/-! # Pending foreign completions preserve the original sampled value -/

noncomputable section
namespace Vegas.EventGraph
open GameTheory.Math.Probability
variable {Player : Type}
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Advancing pending foreign intentions preserves the retained event's exact
evaluator, including all of its private and public read fields. -/
theorem ForeignCompletionSequence.eval_eq
    {who : Player} {first last : graph.Config}
    (sequence : ForeignCompletionSequence who first last)
    (event : graph.EventId) (ready : first.cut.Ready event)
    (actor : graph.actor? event = some who) (action : graph.Action event) :
    last.cut.Ready event ∧
      (graph.nodes event).eval? action last.store =
        (graph.nodes event).eval? action first.store := by
  induction sequence with
  | refl => exact ⟨ready, rfl⟩
  | snoc previous other otherReady owner otherActor foreign otherAction value supported ih =>
      obtain ⟨retainedReady, same⟩ := ih
      have different : event ≠ other := by
        intro equal
        subst other
        have owners := Option.some.inj (otherActor.symm.trans actor)
        exact foreign owners
      exact ⟨retainedReady.after_complete otherReady different,
        (eval?_after_complete otherReady retainedReady otherAction value action).trans same⟩

/-- The same deterministic owned event evaluation fixes the same written value
in two genuine supported graph steps, even if their other pending outputs and
completion histories differ. -/
theorem Config.owned_step_output_eq_of_eval_eq
    (first last firstNext lastNext : graph.Config)
    (event : graph.EventId) (firstReady : first.cut.Ready event)
    (lastReady : last.cut.Ready event) (who : Player)
    (actor : graph.actor? event = some who) (action : graph.Action event)
    (evaluations : (graph.nodes event).eval? action last.store =
      (graph.nodes event).eval? action first.store)
    (firstStep : firstNext ∈ (first.step event firstReady action).support)
    (lastStep : lastNext ∈ (last.step event lastReady action).support) :
    firstNext.outputs event = lastNext.outputs event := by
  obtain ⟨value, evaluates⟩ := (graph.nodes event).eval?_eq_pure_of_actor who actor action
    first.store (fun _ read => first.read_available firstReady read)
  have firstLaw := first.step_eq_map_of_eval event firstReady action (PMF.pure value) evaluates
  have lastLaw := last.step_eq_map_of_eval event lastReady action (PMF.pure value)
    (evaluations.trans evaluates)
  rw [PMF.pure_map] at firstLaw lastLaw
  rw [firstLaw, PMF.mem_support_pure_iff] at firstStep
  rw [lastLaw, PMF.mem_support_pure_iff] at lastStep
  subst firstNext
  subst lastNext
  simp only [Config.complete_output_same]

end Vegas.EventGraph
