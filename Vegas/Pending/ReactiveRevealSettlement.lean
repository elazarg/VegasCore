/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveRevealBlock
import Vegas.Pending.ReactiveMonitoring

/-! # Monitored revelation settlement in the existing service

After reserved inclusion, the same watcher, tick, and expiry suffix settles
either source choice. Published replay copies may remain pending. The watcher
has no fresh information on these paths and performs its actual silent response;
the equations retain that private recall and the complete network state.

Timely acceptance of an opening and the elapsed deadline on withholding are
separate operational premises, supplied by the source/calendar induction.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Clock ticks and expiry do not change a settled event or its message effects.
The expiry command is still executed and retained in environment recall. -/
theorem settled_reveal_expiry (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (event : graph.EventId) (settled : ¬execution.application.config.cut.Ready event)
    (ticks : Nat) :
    ∃ next, runtime.runInteractionPlan leaks players network
        (List.replicate ticks .tick ++ [.expire event]) execution = PMF.pure next ∧
      next.application =
        { execution.application with clock := execution.application.clock + ticks } ∧
      next.network = execution.network ∧ next.receipts = execution.receipts ∧
      next.recall = execution.recall := by
  let app := runtime.reactiveApplication leaks
  obtain ⟨ticked, ticksLaw, application, messages, receipts, recall⟩ :=
    runtime.interaction_ticks_pure leaks players network ticks execution
  have notReady : ¬ticked.application.config.cut.Ready event := by
    rw [application]
    exact settled
  have expiry : app.environment ticked.application (.expire event) =
      PMF.pure ticked.application :=
    runtime.environmentStep_expire_of_not_ready ticked.application event notReady
  let next : app.Execution := { ticked with
    environmentRecall := ticked.environmentRecall ++
      [⟨ticked.observeEnvironment app, .application (.expire event)⟩] }
  have step : runtime.interactionStep leaks players network (.expire event) ticked =
      PMF.pure next := by
    simp only [interactionStep, interactionInstruction, PMF.pure_bind,
      ReactiveApplication.dispatch, ReactiveApplication.Command.actor?]
    change (ticked.environmentStep app (.application (.expire event))).bind PMF.pure = _
    rw [PMF.bind_pure]
    change ((app.environment ticked.application (.expire event)).map
      (fun state => { ticked with application := state })).map (fun result : app.Execution =>
        { result with environmentRecall := ticked.environmentRecall ++
          [(⟨ticked.observeEnvironment app, .application (.expire event)⟩ :
            app.EnvironmentEntry)] }) = _
    rw [expiry, PMF.pure_map, PMF.pure_map]
  refine ⟨next, ?_, application, messages, receipts, recall⟩
  rw [runtime.runInteractionPlan_append, ticksLaw, PMF.pure_bind,
    runInteractionPlan, step, PMF.pure_bind]
  rfl

/-- The complete monitored tail after successful opening is quiet. No sampling
restriction is required when all pending and retained evidence is published. -/
theorem monitored_settled_reveal (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy) (watcher : Player)
    (policy : players watcher = (runtime.reactiveApplication leaks).reportFirstUnpublished)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (pending : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id)
    (leaked : ∀ message ∈ execution.network.leaked watcher,
      message.id ∈ execution.network.ledger.map Message.id)
    (inputs : ∀ input ∈ execution.network.inputs, input.broadcaster = watcher →
      input.envelope.id ∈ execution.network.ledger.map Message.id)
    (event : graph.EventId) (settled : ¬execution.application.config.cut.Ready event)
    (ticks : Nat) :
    ∃ next, runtime.runInteractionPlan leaks players (runtime.reportNetwork leaks watcher)
        ([.player watcher, .wire] ++ List.replicate ticks .tick ++ [.expire event])
        execution = PMF.pure next ∧
      next.application =
        { execution.application with clock := execution.application.clock + ticks } ∧
      next.network = execution.network ∧ next.receipts = execution.receipts ∧
      next.recall =
        (execution.respond (runtime.reactiveApplication leaks) watcher ⟨none⟩).recall := by
  obtain ⟨watched, monitor, application, messages, receipts, recall, _length⟩ :=
    (runtime.reactiveApplication leaks).reportInclusion_quiescent players watcher policy
      execution pending leaked inputs
  have notReady : ¬watched.application.config.cut.Ready event := by
    rw [application]
    exact settled
  obtain ⟨next, suffix, after, networkEq, receiptEq, recallEq⟩ :=
    runtime.settled_reveal_expiry leaks players (runtime.reportNetwork leaks watcher)
      watched event notReady ticks
  refine ⟨next, ?_, ?_, networkEq.trans messages, receiptEq.trans receipts,
    recallEq.trans recall⟩
  · rw [List.append_assoc, runtime.runInteractionPlan_append, runtime.run_report_plan,
      monitor, PMF.pure_bind]
    exact suffix
  · simpa only [application] using after

/-- The same monitored tail after withholding performs the actual failure
completion once the current deadline is due. The reporter adds no publication,
receipt, or private knowledge on this source-representable path. -/
theorem monitored_silent_reveal (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy) (watcher : Player)
    (policy : players watcher = (runtime.reactiveApplication leaks).reportFirstUnpublished)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (pending : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id)
    (leaked : ∀ message ∈ execution.network.leaked watcher,
      message.id ∈ execution.network.ledger.map Message.id)
    (inputs : ∀ input ∈ execution.network.inputs, input.broadcaster = watcher →
      input.envelope.id ∈ execution.network.ledger.map Message.id)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (ready : execution.application.config.cut.Ready event)
    (entered ticks : Nat) (activated : execution.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ execution.application.clock + ticks - entered) :
    ∃ next, runtime.runInteractionPlan leaks players (runtime.reportNetwork leaks watcher)
        ([.player watcher, .wire] ++ List.replicate ticks .tick ++ [.expire event])
        execution = PMF.pure next ∧
      next.application =
        ({ execution.application with clock := execution.application.clock + ticks } :
          State graph).complete event ready
            (cast (congrArg EventField.Action outputEq.symm) false)
            (cast (congrArg EventField.Value outputEq.symm) PublicationResult.failure) ∧
      next.network = execution.network ∧ next.receipts = execution.receipts ∧
      next.recall =
        (execution.respond (runtime.reactiveApplication leaks) watcher ⟨none⟩).recall := by
  obtain ⟨watched, monitor, application, messages, receipts, recall, _length⟩ :=
    (runtime.reactiveApplication leaks).reportInclusion_quiescent players watcher policy
      execution pending leaked inputs
  have watchedReady : watched.application.config.cut.Ready event := by
    rw [application]
    exact ready
  have watchedActivation : watched.application.activatedAt event = some entered := by
    rw [application]
    exact activated
  have watchedDue : runtime.deadline event ≤ watched.application.clock + ticks - entered := by
    rw [application]
    exact due
  obtain ⟨next, suffix, after, networkEq, receiptEq, recallEq⟩ :=
    runtime.canonical_silent_expiry leaks players (runtime.reportNetwork leaks watcher)
      watched owner event payload binding checks outputEq codeEq node watchedReady
      entered ticks watchedActivation watchedDue
  refine ⟨next, ?_, ?_, networkEq.trans messages, receiptEq.trans receipts,
    recallEq.trans recall⟩
  · rw [List.append_assoc, runtime.runInteractionPlan_append, runtime.run_report_plan,
      monitor, PMF.pure_bind]
    exact suffix
  · simpa only [application] using after

end Vegas.EventGraphRuntime
