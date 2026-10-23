/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingRestoration
import Vegas.Pending.ReactiveBindingShadowInvariant

/-! # Recorded private results of submitted bindings

The repair implementation records each original typed binding result when its
opaque packet is submitted. Recording another prepared candidate changes no
completion record; recording a different event preserves earlier records. These
facts support provenance of outstanding owner bindings under the count menu.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace BindingShadow

/-- The private memory retains the original action and value of a binding. -/
def RecordsBinding (memory : BindingShadow graph) (event : graph.EventId)
    {owner : Player} {payload : L.Ty}
    (outputEq : graph.outputLayout event = .binding owner payload)
    (result : PublicationResult (L.Val payload)) : Prop :=
  memory.actions event = some (cast (congrArg EventField.Action outputEq.symm) result) ∧
    memory.values (.inr event) = some (cast (congrArg EventField.Value outputEq.symm) result)

omit [DecidableEq Player] in
/-- Remembering a candidate does not change any recorded completion. -/
theorem RecordsBinding.rememberCandidate {memory : BindingShadow graph} {event : graph.EventId}
    {owner : Player} {payload : L.Ty}
    {outputEq : graph.outputLayout event = .binding owner payload}
    {result : PublicationResult (L.Val payload)} (recorded : memory.RecordsBinding event
      outputEq result) (slot : CandidateSlot graph) (candidate : CommitmentCandidate (Raw L)) :
    (memory.rememberCandidate slot candidate).RecordsBinding event outputEq result := recorded

omit [DecidableEq Player] in
/-- A newly recorded event preserves every distinct event's private record. -/
theorem RecordsBinding.rememberCompletion_of_ne
    {memory : BindingShadow graph} {event : graph.EventId} {owner : Player} {payload : L.Ty}
    {outputEq : graph.outputLayout event = .binding owner payload}
    {result : PublicationResult (L.Val payload)}
    (recorded : memory.RecordsBinding event outputEq result)
    (other : graph.EventId) (different : event ≠ other)
    (action : graph.Action other) (value : (graph.outputLayout other).Value) :
    (memory.rememberCompletion other action value).RecordsBinding event outputEq result := by
  simp only [RecordsBinding, rememberCompletion, Function.update_of_ne different,
    Function.update_of_ne (show Sum.inr event ≠ (Sum.inr other : graph.Field) from
      fun same => different (Sum.inr.inj same))]
  exact recorded

end BindingShadow

end Vegas.EventGraphRuntime
