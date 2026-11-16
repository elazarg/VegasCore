module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.BindingChain
public import Vegas.EventGraph.BindingPrefixObservation
public import Vegas.Game.SourceServiceReachedDecoding

@[expose] public section

/-! # Source prefixes filled from submitted binding records

An existing action-table run constructs a genuine source residual at its exact
rank. Its records can come from a sampled honest table and earlier actual focal
bindings; only the cropped prefix enters a current source observation.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}

/-- A submitted cropped table has a genuine source residual and checkpoint. -/
theorem SourceResidual.actionTable_prefix
    {profile : BehavioralProfile setup.program} {start : Nat}
    {origin : setup.informationGraph.Config}
    (residual : SourceResidual setup profile start origin)
    {inputs : setup.informationGraph.Inputs} (reachable : origin.Reachable inputs)
    (clear : origin.defaulted = ∅)
    (table : (event : setup.informationGraph.EventId) → setup.informationGraph.Action event)
    (count : Nat) (bounded : start + count ≤ setup.informationGraph.order.eventCount)
    (submitted : ∀ event : setup.informationGraph.EventId,
      start ≤ event.val → event.val < start + count →
      (setup.informationGraph.outputLayout event).Submitted (table event))
    (bindings : ∀ event : setup.informationGraph.EventId,
      start ≤ event.val → event.val < start + count →
      ∃ owner payload, setup.informationGraph.outputLayout event = .binding owner payload) :
    ∃ filled,
      setup.informationGraph.runPlan (setup.informationGraph.policyPlan
        (actionTableProfile table) setup.informationGraph.canonicalScheduler) count origin =
          PMF.pure filled ∧
      filled.Reachable inputs ∧ filled.cut.IsPrefix (start + count) ∧
      filled.defaulted = ∅ ∧ filled.NoBindingDefaults ∧
      Nonempty (SourceResidual setup profile (start + count) filled) ∧
      (∀ event : setup.informationGraph.EventId, start ≤ event.val →
        event.val < start + count → ∃ value : (setup.informationGraph.outputLayout event).Value,
          completionOf filled event = some (EventGraph.completion setup.informationGraph event
            (some (table event)) value) ∧ filled.outputs event = some value) ∧
      ∀ smaller, smaller ≤ count → ∃ prefixConfig,
        setup.informationGraph.runPlan (setup.informationGraph.policyPlan
            (actionTableProfile table) setup.informationGraph.canonicalScheduler) smaller origin =
              PMF.pure prefixConfig ∧
          prefixConfig.RestrictionOf (fun event => event.val < start + smaller) filled := by
  obtain ⟨filled, law, ordered, path, finalClear, finalClean, frame, restrictions⟩ :=
    exists_submitted_actionTable_prefix table count start origin residual.checkpoint.ordered
      clear bounded submitted bindings
  obtain ⟨rank, ⟨next⟩⟩ := residual.path path
  have rankEq : rank = start + count := next.checkpoint.ordered.unique ordered
  subst rank
  exact ⟨filled, law, Config.Step.path_reachable path reachable, ordered, finalClear, finalClean,
    ⟨next⟩, frame, restrictions⟩

/-- Consistent donor records construct a genuine source prefix, rather than
postulating a checkpoint for an intermediate native cut. The donors can be
selected from one sampled honest table and the actual focal binding records. -/
theorem SourceResidual.actionTable_prefix_records
    {profile : BehavioralProfile setup.program} {start : Nat}
    {origin : setup.informationGraph.Config}
    (residual : SourceResidual setup profile start origin)
    {inputs : setup.informationGraph.Inputs} (reachable : origin.Reachable inputs)
    (clear : origin.defaulted = ∅)
    (table : (event : setup.informationGraph.EventId) → setup.informationGraph.Action event)
    (records : setup.informationGraph.EventId → Option setup.informationGraph.Completion)
    (outputs : (event : setup.informationGraph.EventId) →
      Option (setup.informationGraph.outputLayout event).Value)
    (count : Nat) (bounded : start + count ≤ setup.informationGraph.order.eventCount)
    (typed : ∀ event : setup.informationGraph.EventId,
      start ≤ event.val → event.val < start + count →
      ∃ owner payload, ∃ binding : setup.informationGraph.outputLayout event =
          .binding owner payload,
        ∃ result : PublicationResult (L.Val payload),
          table event = cast (congrArg EventField.Action binding.symm) (some result) ∧
          records event = some (EventGraph.completion setup.informationGraph event
            (some (cast (congrArg EventField.Action binding.symm) (some result)))
            (cast (congrArg EventField.Value binding.symm) result)) ∧
          outputs event = some (cast (congrArg EventField.Value binding.symm) result)) :
    ∃ filled,
      setup.informationGraph.runPlan (setup.informationGraph.policyPlan
        (actionTableProfile table) setup.informationGraph.canonicalScheduler) count origin =
          PMF.pure filled ∧
      filled.Reachable inputs ∧ filled.cut.IsPrefix (start + count) ∧
      filled.defaulted = ∅ ∧ filled.NoBindingDefaults ∧
      Nonempty (SourceResidual setup profile (start + count) filled) ∧
      (∀ event : setup.informationGraph.EventId, start ≤ event.val →
        event.val < start + count → completionOf filled event = records event ∧
          filled.outputs event = outputs event) ∧
      ∀ smaller, smaller ≤ count → ∃ prefixConfig,
        setup.informationGraph.runPlan (setup.informationGraph.policyPlan
            (actionTableProfile table) setup.informationGraph.canonicalScheduler) smaller origin =
              PMF.pure prefixConfig ∧
          prefixConfig.RestrictionOf (fun event => event.val < start + smaller) filled := by
  have submitted (event : setup.informationGraph.EventId) (lower : start ≤ event.val)
      (upper : event.val < start + count) :
      (setup.informationGraph.outputLayout event).Submitted (table event) := by
    obtain ⟨owner, payload, binding, result, actionEq, _⟩ := typed event lower upper
    rw [actionEq]
    exact EventField.submitted_cast binding.symm (some result) rfl
  have bindings (event : setup.informationGraph.EventId) (lower : start ≤ event.val)
      (upper : event.val < start + count) :
      ∃ owner payload, setup.informationGraph.outputLayout event = .binding owner payload := by
    obtain ⟨owner, payload, binding, _⟩ := typed event lower upper
    exact ⟨owner, payload, binding⟩
  obtain ⟨filled, law, filledReach, ordered, finalClear, finalClean, next, frame, restrictions⟩ :=
    residual.actionTable_prefix reachable clear table count bounded submitted bindings
  refine ⟨filled, law, filledReach, ordered, finalClear, finalClean, next, ?_, restrictions⟩
  intro event lower upper
  obtain ⟨owner, payload, binding, result, actionEq, recordEq, outputEq⟩ := typed event lower upper
  have matched := binding_frame_of_typed_action filled filledReach table event owner payload
    binding result actionEq (frame event lower upper)
  exact ⟨matched.1.trans recordEq.symm, matched.2.trans outputEq.symm⟩

end Vegas
