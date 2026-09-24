/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphEvaluation
import Vegas.Source.CommitmentEvidence
import Vegas.EventGraph.CommitmentEvidence

/-! # Source names and graph binding evidence

The compiler's typed context references interpret binding facts at a source
prefix. Store agreement is the existing source-to-graph relation. Evidence
does not introduce handles or add fields to publication results.
-/

namespace Vegas.SourceProgram.EventLowering.ContextRefs

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {Γ : SourceCtx Player L}

def commitmentEvidence (refs : ContextRefs graph.layout Γ)
    {owner : Player} {name : VarId} {payload : L.Ty}
    (source : HasVar Γ name (.commitment owner payload)) (value : L.Val payload) :
    EventGraph.CommitmentEvidence graph := ⟨owner, payload, refs.get source, value⟩

theorem commitmentEvidence_holds_iff (refs : ContextRefs graph.layout Γ)
    (state : State L Γ) (store : EventGraph.Store graph.layout) (agree : refs.Agrees state store)
    {owner : Player} {name : VarId} {payload : L.Ty}
    (source : HasVar Γ name (.commitment owner payload)) (value : L.Val payload) :
    (refs.commitmentEvidence source value).Holds store ↔ state.get source = .success value := by
  change (refs.get source).get? store = some (.success value) ↔ _
  rw [agree source]
  exact Option.some_inj

theorem sourceEvidence_of_graph (refs : ContextRefs graph.layout Γ)
    (state : State L Γ) (store : EventGraph.Store graph.layout) (agree : refs.Agrees state store)
    {owner : Player} {name : VarId} {payload : L.Ty}
    (source : HasVar Γ name (.commitment owner payload)) (value : L.Val payload)
    (valid : (refs.commitmentEvidence source value).Holds store) :
    (⟨owner, name, payload, value⟩ : CommitmentEvidence Player L).Holds state :=
  ⟨source, (refs.commitmentEvidence_holds_iff state store agree source value).mp valid⟩

theorem graphEvidence_of_source (refs : ContextRefs graph.layout Γ)
    (state : State L Γ) (store : EventGraph.Store graph.layout) (agree : refs.Agrees state store)
    (fact : CommitmentEvidence Player L) (valid : fact.Holds state) :
    ∃ source : HasVar Γ fact.name (.commitment fact.owner fact.payload),
      (refs.commitmentEvidence source fact.value).Holds store := by
  obtain ⟨source, bound⟩ := valid
  exact ⟨source, (refs.commitmentEvidence_holds_iff state store agree source fact.value).mpr bound⟩

end Vegas.SourceProgram.EventLowering.ContextRefs
