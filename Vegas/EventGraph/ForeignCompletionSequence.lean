/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.NormalizedPolicy

/-! # Normalized policy stability through semantic foreign completions -/

noncomputable section
namespace Vegas.EventGraph
open GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A proof-only sequence of supported semantic completions by other owners.
The relation adds no execution state and does not choose an evaluation law. -/
inductive ForeignCompletionSequence (who : Player) : graph.Config → graph.Config → Prop
  | refl (config : graph.Config) : ForeignCompletionSequence who config config
  | snoc {first before : graph.Config}
      (previous : ForeignCompletionSequence who first before)
      (other : graph.EventId) (ready : before.cut.Ready other)
      (owner : Player) (actor : graph.actor? other = some owner) (foreign : owner ≠ who)
      (action : graph.Action other) (value : (graph.outputLayout other).Value)
      (supported : before.complete other ready action value ∈
        (before.step other ready action).support) :
      ForeignCompletionSequence who first (before.complete other ready action value)

omit [DecidableEq Player] in
/-- Semantic pending completions preserve genuine reachability. -/
theorem ForeignCompletionSequence.reachable {who : Player} {first last : graph.Config}
    (sequence : ForeignCompletionSequence who first last) {inputs : graph.Inputs}
    (reachable : first.Reachable inputs) : last.Reachable inputs := by
  induction sequence with
  | refl => exact reachable
  | snoc previous other ready owner actor foreign action value supported ih =>
      exact Config.Reachable.step ih other ready action _ supported

/-- The exact normalized decision law at a retained ready event is unchanged
through every pending foreign completion. This uses the graph's barrier
information discipline rather than assuming the desired kernel equality. -/
theorem ForeignCompletionSequence.normalizePolicy_eq
    {who : Player} {first last : graph.Config}
    (sequence : ForeignCompletionSequence who first last)
    (ordered : graph.BarrierOrdered) (policy : graph.BehavioralPolicy who)
    (event : graph.EventId) (ready : first.cut.Ready event)
    (actor : graph.actor? event = some who) :
    last.cut.Ready event ∧
      graph.normalizePolicy who policy event actor (graph.playerObserve who last) =
        graph.normalizePolicy who policy event actor (graph.playerObserve who first) := by
  induction sequence with
  | refl => exact ⟨ready, rfl⟩
  | snoc previous other otherReady owner otherActor foreign action value supported ih =>
      obtain ⟨retainedReady, same⟩ := ih
      have advanced := ordered.normalizePolicy_complete_foreign policy _ event other
        retainedReady otherReady actor owner otherActor foreign action value
      exact ⟨advanced.1, advanced.2.trans same⟩

end Vegas.EventGraph
