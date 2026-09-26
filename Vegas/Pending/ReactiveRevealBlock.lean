/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveDisclosure
import Vegas.Pending.ReactiveServiceEvaluation
import Vegas.Pending.ReactiveServiceSelection
import Interaction.ReactiveQuiescent

/-! # Canonical revelation blocks in the existing reactive service

A source revelation chooses a certified opening or silence. Reserved inclusion
then consumes the sole opening packet; silence leaves expiry to resolve the
event. The equations concern actual executions and retain network and recall
effects. They do not restrict the raw response menu or assume player optimality.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The two source choices, using matching owned evidence on the opening branch.
Withholding emits no packet and is completed by the existing expiry command. -/
def canonicalRevealResponse (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L) (disclose : Bool) :
    (runtime.reactiveApplication leaks).Action :=
  ⟨if disclose then some (.submit (disclosureSubmission (.opening event candidate raw)))
    else none⟩

theorem canonicalRevealResponse_application (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L) (disclose : Bool) :
    (execution.respond (runtime.reactiveApplication leaks) owner
      (runtime.canonicalRevealResponse leaks event candidate raw disclose)).application =
        execution.application := by
  cases disclose <;> rfl

/-- Empty-pool silence produces the actual service wait, including its command
recall. Neither player nor network policy is consulted at this instruction. -/
theorem canonical_silent_inclusion (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (execution : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (empty : execution.network.pending = []) :
    let app := runtime.reactiveApplication leaks
    let submitted := execution.respond app owner
      (runtime.canonicalRevealResponse leaks event candidate raw false)
    runtime.interactionStep leaks players network (.includeLatest event owner) submitted =
      submitted.environmentStep app .wait := by
  dsimp only
  have pending : (execution.respond (runtime.reactiveApplication leaks) owner
      (runtime.canonicalRevealResponse leaks event candidate raw false)).network.pending = [] :=
    empty
  simp only [interactionStep, interactionInstruction, reactiveLatest,
    ReactiveApplication.Execution.observeEnvironment, MessageNetwork.publicView, pending,
    List.reverse_nil, List.find?_nil, FinDist.pure_bind, ReactiveApplication.dispatch,
    ReactiveApplication.Command.actor?]
  exact FinDist.bind_pure _

/-- A fresh canonical opening is selected by immediate reserved inclusion,
including in the presence of earlier traffic. -/
theorem canonical_opening_inclusion (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (execution : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (fresh : (owner, execution.network.nextSerial owner) ∉
      execution.network.ledger.map Message.id) :
    let app := runtime.reactiveApplication leaks
    let submitted := execution.respond app owner
      (runtime.canonicalRevealResponse leaks event candidate raw true)
    runtime.interactionStep leaks players network (.includeLatest event owner) submitted =
      submitted.environmentStep app (.include (owner, execution.network.nextSerial owner)) := by
  let app := runtime.reactiveApplication leaks
  let submitted := execution.respond app owner
    (runtime.canonicalRevealResponse leaks event candidate raw true)
  change runtime.interactionStep leaks players network (.includeLatest event owner) submitted =
    submitted.environmentStep app (.include (owner, execution.network.nextSerial owner))
  let packet := app.packet execution.application owner (execution.network.known owner)
    (disclosureSubmission (.opening event candidate raw))
  have selected : runtime.reactiveLatest leaks event owner (submitted.observeEnvironment app) =
      .include (owner, execution.network.nextSerial owner) := by
    exact runtime.reactiveLatest_last leaks owner event _ execution.network.pending
      ⟨(owner, execution.network.nextSerial owner), packet⟩ rfl rfl rfl fresh
  unfold interactionStep
  rw [interactionInstruction, selected, FinDist.pure_bind]
  simp only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?]
  exact FinDist.bind_pure _

/-- The successful opening branch restores an empty pending pool and adds only
the accepted receipt. The full execution law retains its actual public ledger
and private response recall, rather than replacing them by a source state. -/
theorem canonical_opening_checkpoint (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (execution : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L) (after : State graph)
    (empty : execution.network.pending = [])
    (fresh : (owner, execution.network.nextSerial owner) ∉
      execution.network.ledger.map Message.id)
    (accepted : runtime.handle execution.application
      ⟨(owner, execution.network.nextSerial owner), .opening event candidate raw⟩ = some after) :
    let app := runtime.reactiveApplication leaks
    let submitted := execution.respond app owner
      (runtime.canonicalRevealResponse leaks event candidate raw true)
    ∃ next, runtime.interactionStep leaks players network (.includeLatest event owner)
        submitted = FinDist.pure next ∧
      next.application = after ∧ next.network.pending = [] ∧
      next.receipts = execution.receipts ++
        [((owner, execution.network.nextSerial owner), true)] ∧
      next.recall = submitted.recall := by
  let app := runtime.reactiveApplication leaks
  let submitted := execution.respond app owner
    (runtime.canonicalRevealResponse leaks event candidate raw true)
  let packet := app.packet execution.application owner (execution.network.known owner)
    (disclosureSubmission (.opening event candidate raw))
  let envelope : Message Player app.Payload :=
    ⟨(owner, execution.network.nextSerial owner), packet⟩
  have pending : submitted.network.pending = [envelope] := by
    change execution.network.pending ++ [_] = _
    rw [empty, List.nil_append]
    rfl
  have found : submitted.network.lookup envelope.id = some envelope := by
    simp only [MessageNetwork.lookup, pending, List.find?_cons, decide_true]
  have handled : app.handle submitted.application envelope = some after := accepted
  let next : app.Execution := { submitted.includePending app envelope.id with
    environmentRecall := submitted.environmentRecall ++
      [⟨submitted.observeEnvironment app, .include envelope.id⟩] }
  refine ⟨next, ?_, ?_, ?_, ?_, ?_⟩
  · rw [runtime.canonical_opening_inclusion leaks players network execution owner event
      candidate raw fresh]
    simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure]
    rfl
  · change (submitted.includePending app envelope.id).application = after
    simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, handled, Option.getD_some]
  · change (submitted.includePending app envelope.id).network.pending = []
    simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, pending, MessagePool.removeFirst, ↓reduceIte]
  · change (submitted.includePending app envelope.id).receipts = _
    simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, handled, Option.isSome_some]
    rfl
  · change (submitted.includePending app envelope.id).recall = submitted.recall
    simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found]

/-- Any fixed number of clock ticks has a deterministic full execution law.
No player is activated, and all packet, receipt and private recall data persist. -/
theorem interaction_ticks_pure (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (ticks : Nat)
    (execution : (runtime.reactiveApplication leaks).Execution) :
    ∃ next, runtime.runInteractionPlan leaks players network (List.replicate ticks .tick)
        execution = FinDist.pure next ∧
      next.application =
        { execution.application with clock := execution.application.clock + ticks } ∧
      next.network = execution.network ∧ next.receipts = execution.receipts ∧
      next.recall = execution.recall := by
  induction ticks generalizing execution with
  | zero =>
      refine ⟨execution, rfl, ?_, rfl, rfl, rfl⟩
      simp only [Nat.add_zero]
      cases execution.application
      rfl
  | succ ticks ih =>
      let app := runtime.reactiveApplication leaks
      let first : app.Execution := { execution with
        application := { execution.application with clock := execution.application.clock + 1 }
        environmentRecall := execution.environmentRecall ++
          [⟨execution.observeEnvironment app, .application .advanceClock⟩] }
      have step : runtime.interactionStep leaks players network .tick execution =
          FinDist.pure first := by
        have clockLaw : app.environment execution.application .advanceClock =
            FinDist.pure { execution.application with clock := execution.application.clock + 1 } :=
          rfl
        simp only [interactionStep, interactionInstruction, FinDist.pure_bind,
          ReactiveApplication.dispatch, ReactiveApplication.Command.actor?]
        change (execution.environmentStep app (.application .advanceClock)).bind FinDist.pure = _
        rw [FinDist.bind_pure]
        change ((app.environment execution.application .advanceClock).map
          (fun state => { execution with application := state })).map (fun next : app.Execution =>
            { next with environmentRecall := execution.environmentRecall ++
              [(⟨execution.observeEnvironment app, .application .advanceClock⟩ :
                app.EnvironmentEntry)] }) = _
        rw [clockLaw, FinDist.map_pure, FinDist.map_pure]
      obtain ⟨next, law, application, messages, receipts, recall⟩ := ih first
      refine ⟨next, ?_, ?_, messages, receipts, recall⟩
      · rw [List.replicate_succ, runInteractionPlan, step, FinDist.pure_bind]
        exact law
      · rw [application]
        change { execution.application with clock := execution.application.clock + 1 + ticks } = _
        exact congrArg (fun clock => { execution.application with clock := clock })
          (show execution.application.clock + 1 + ticks =
            execution.application.clock + (ticks + 1) by omega)

/-- Once the declared deadline is due, the silent source branch becomes the
actual failure completion. The clock premise is explicit and independent of
how early previous events completed. -/
theorem canonical_silent_expiry (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (execution : (runtime.reactiveApplication leaks).Execution)
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
    ∃ next, runtime.runInteractionPlan leaks players network
        (List.replicate ticks .tick ++ [.expire event]) execution = FinDist.pure next ∧
      next.application =
        ({ execution.application with clock := execution.application.clock + ticks } :
          State graph).complete event ready
            (cast (congrArg EventField.Action outputEq.symm) false)
            (cast (congrArg EventField.Value outputEq.symm) PublicationResult.failure) ∧
      next.network = execution.network ∧ next.receipts = execution.receipts ∧
      next.recall = execution.recall := by
  let app := runtime.reactiveApplication leaks
  obtain ⟨ticked, ticksLaw, application, messages, receipts, recall⟩ :=
    runtime.interaction_ticks_pure leaks players network ticks execution
  have tickedReady : ticked.application.config.cut.Ready event := by
    rw [application]
    exact ready
  have tickedActivation : ticked.application.activatedAt event = some entered := by
    rw [application]
    exact activated
  have tickedDue : runtime.deadline event ≤ ticked.application.clock - entered := by
    rw [application]
    exact due
  let after := ticked.application.complete event tickedReady
    (cast (congrArg EventField.Action outputEq.symm) false)
    (cast (congrArg EventField.Value outputEq.symm) PublicationResult.failure)
  have expiry : app.environment ticked.application (.expire event) = FinDist.pure after :=
    runtime.environmentStep_expire_resolve_eq ticked.application event tickedReady entered
      tickedActivation tickedDue owner payload binding checks outputEq codeEq node
  let next : app.Execution := { ticked with
    application := after
    environmentRecall := ticked.environmentRecall ++
      [⟨ticked.observeEnvironment app, .application (.expire event)⟩] }
  have step : runtime.interactionStep leaks players network (.expire event) ticked =
      FinDist.pure next := by
    simp only [interactionStep, interactionInstruction, FinDist.pure_bind,
      ReactiveApplication.dispatch, ReactiveApplication.Command.actor?]
    change (ticked.environmentStep app (.application (.expire event))).bind FinDist.pure = _
    rw [FinDist.bind_pure]
    change ((app.environment ticked.application (.expire event)).map
      (fun state => { ticked with application := state })).map (fun result : app.Execution =>
        { result with environmentRecall := ticked.environmentRecall ++
          [(⟨ticked.observeEnvironment app, .application (.expire event)⟩ :
            app.EnvironmentEntry)] }) = _
    rw [expiry, FinDist.map_pure, FinDist.map_pure]
  refine ⟨next, ?_, ?_, messages, receipts, recall⟩
  · rw [runtime.runInteractionPlan_append, ticksLaw, FinDist.pure_bind,
      runInteractionPlan, step, FinDist.pure_bind]
    rfl
  · change after = _
    unfold after
    simp only [application]

end Vegas.EventGraphRuntime
