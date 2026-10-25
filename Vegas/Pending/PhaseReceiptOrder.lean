/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseExclusionRecord

/-! # Owned receipt order inside actual commitment phases -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace ExclusionEvidence

/-- An active owner's ready binding has received every earlier owned binding in
the phase. A missing predecessor would already have excluded that owner. -/
theorem ready_binding_receipts {low : Nat} {inherited : Finset Player}
    {state : RecoveryState graph} (valid : ExclusionEvidence low inherited state)
    (ordered : graph.RevealRelaxedOrdered) (event : graph.EventId)
    (ready : state.native.config.cut.Ready event) (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (active : owner ∉ state.excluded) :
    owner ∉ inherited ∧ ∀ prior : graph.EventId, low ≤ prior.val → prior.val < event.val →
      ∀ priorPayload : L.Ty, graph.outputLayout prior = .binding owner priorPayload →
        state.native.accepted (.inr prior) ≠ none := by
  refine ⟨fun inheritedOwner => active ((valid.excluded owner).mpr (Or.inl inheritedOwner)), ?_⟩
  intro prior lower earlier priorPayload priorBinding absent
  have dependency : prior ∈ graph.order.predecessors event :=
    ordered.keeps (barrierOrder_same_owner graph.outputLayout earlier (by
      rw [priorBinding, binding]
      rfl)) (Or.inl (by simp only [priorBinding, EventField.IsPublication, not_false_eq_true]))
  have completed := ready.2 dependency
  have missed : state.native.publicView.missedBinding prior = true :=
    (State.publicView_missedBinding state.native prior owner priorPayload priorBinding).mpr
      ⟨completed, absent⟩
  exact active ((valid.excluded owner).mpr (Or.inr ⟨prior, lower,
    EventGraph.actor?_of_outputLayout_binding graph priorBinding, Or.inl missed⟩))

end ExclusionEvidence

end Vegas.EventGraphRuntime
