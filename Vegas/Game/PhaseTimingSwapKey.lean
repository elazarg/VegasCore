/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingBindingKey
import Vegas.Game.PhaseRepairTimingKey
import Vegas.Pending.PhaseOpeningMenuSymmetry

/-! # Actual operational timing information under hidden initial-value changes -/

noncomputable section

namespace Vegas

open EventGraph EventGraphRuntime Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Hidden swaps preserve all actual operational fields, including the fresh
slot mask, while allowing the original private inputs to change. -/
theorem phaseOperationalView_swap (swap : HiddenSwap graph) (view : (app).PlayerView) :
    phaseOperationalView runtime leaks (swap.phaseView view) =
      phaseOperationalView runtime leaks view := by
  change (⟨view.application.2, view.messages, view.receipts, fun slot =>
    match swapCandidate (swap.raw (view.application.1.who, slot))
      (view.application.1.candidates slot) with
    | .fresh => true
    | _ => false⟩ : PhaseOperationalView graph) = _
  congr 1
  funext slot
  cases view.application.1.candidates slot <;> rfl

private theorem timing_key_of_delivered (swap : HiddenSwap graph) (owner : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (delivered : phaseDeliveredValue runtime leaks owner (swap.phaseView view) =
      phaseDeliveredValue runtime leaks owner view) :
    phaseTimingKey runtime leaks owner (some (past.map swap.phaseEntry, swap.phaseView view)) =
      phaseTimingKey runtime leaks owner (some (past, view)) := by
  have recalled : (past.map swap.phaseEntry).map (fun entry =>
      (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)) =
        past.map (fun entry =>
          (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro entry _member
    exact congrArg (fun operational => (operational, entry.emitted))
      (phaseOperationalView_swap runtime leaks swap entry.beforeView)
  simp only [phaseTimingKey, phaseOperationalView_swap, delivered, recalled]

/-- The complete binding timing key is unchanged across a hidden swap of the
whole actual history, including arbitrary original private input fields. -/
theorem phaseTimingKey_swap_at_binding (swap : HiddenSwap graph)
    (ordered : graph.RevealRelaxedOrdered) (execution : (app).Execution)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩) :
    phaseTimingKey runtime leaks owner (some ((swap.phaseExecution execution).recall owner,
        (swap.phaseExecution execution).observe app owner)) =
      phaseTimingKey runtime leaks owner
        (some (execution.recall owner, execution.observe app owner)) := by
  rw [swap.observe_phaseExecution]
  apply timing_key_of_delivered runtime leaks swap
  rw [← swap.observe_phaseExecution,
    phaseDeliveredValue_eq_none_of_binding runtime leaks ordered _ owner event payload binding
      (show (swap.phaseExecution execution).application.SeedRequest owner
        ⟨(swap.phaseExecution execution).application.attempt, event⟩ from request),
    phaseDeliveredValue_eq_none_of_binding runtime leaks ordered _ owner event payload binding
      request]

/-- A guarded opening retains its complete timing key even when earlier
private input fields change. Its delivered field is the same actual binding. -/
theorem phaseTimingKey_swap_at_opening (swap : HiddenSwap graph)
    (ordered : graph.RevealRelaxedOrdered) (execution : (app).Execution)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (fixed : RevealFixed swap execution.application.current.native event) :
    phaseTimingKey runtime leaks owner (some ((swap.phaseExecution execution).recall owner,
        (swap.phaseExecution execution).observe app owner)) =
      phaseTimingKey runtime leaks owner
        (some (execution.recall owner, execution.observe app owner)) := by
  have field : swap.values.value binding.field = id :=
    (show swap.values.value binding.field = id ∧ _ from
      by simpa only [RevealFixed, node] using fixed).1
  have storeAt : swap.values.store execution.application.current.native.config.store
      binding.field =
      execution.application.current.native.config.store binding.field := by
    simp only [ValueSwap.store, field, Option.map_id, id_eq]
  have stored : binding.get?
      (swap.phaseExecution execution).application.current.native.config.store =
      binding.get? execution.application.current.native.config.store := by
    change binding.get? (execution.application.current.native.swap swap).config.store = _
    rw [State.swap_config, Config.swap_store, binding.get?_congr _ _ storeAt]
  rw [swap.observe_phaseExecution]
  apply timing_key_of_delivered runtime leaks swap
  rw [← swap.observe_phaseExecution,
    phaseDeliveredValue_of_opening runtime leaks ordered _ owner event payload binding checks
      outputEq codeEq node (show (swap.phaseExecution execution).application.SeedRequest owner
        ⟨(swap.phaseExecution execution).application.attempt, event⟩ from request),
    phaseDeliveredValue_of_opening runtime leaks ordered _ owner event payload binding checks
      outputEq codeEq node request, stored]

end Vegas
