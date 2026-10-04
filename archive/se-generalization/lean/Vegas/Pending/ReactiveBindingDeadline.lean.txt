/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingOmission
import Vegas.Pending.ReactiveRevealBlock
import Interaction.ReactivePolicyInvariant

/-! # Missing the protected binding response

After the designated binding opportunity, reserved inclusion skips published
replays. If no accepted handle was installed, the existing clock and expiry
instructions create public omission evidence. The result is independent of
all subsequent player and network policies. Earlier waiting opportunities are
not classified by this result.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

theorem binding_deadline_omission
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (scheduler : runtime.NetworkPolicy leaks)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (ready : execution.application.config.cut.Ready event)
    (absent : execution.application.accepted (.inr event) = none)
    (entered ticks : Nat)
    (activated : execution.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ execution.application.clock + ticks - entered) :
    ∃ next, runtime.runInteractionPlan leaks players scheduler
        (List.replicate ticks .tick ++ [.expire event]) execution = PMF.pure next ∧
      next.application.publicView.missedBinding event = true := by
  let app := runtime.reactiveApplication leaks
  obtain ⟨ticked, tickLaw, application, _, _, _⟩ :=
    runtime.interaction_ticks_pure leaks players scheduler ticks execution
  have tickReady : ticked.application.config.cut.Ready event := by
    rw [application]
    exact ready
  have tickActivated : ticked.application.activatedAt event = some entered := by
    rw [application]
    exact activated
  have tickDue : runtime.deadline event ≤ ticked.application.clock - entered := by
    rw [application]
    exact due
  let failed : PublicationResult (L.Val payload) := .failure
  let after := (ticked.application.complete event tickReady
    (cast (congrArg EventField.Action outputEq.symm) failed)
    (cast (congrArg EventField.Value outputEq.symm) failed)).markMissed event
  have expiry : app.environment ticked.application (.expire event) = PMF.pure after :=
    runtime.environmentStep_expire_bind_eq ticked.application event tickReady entered tickActivated
      tickDue who payload outputEq codeEq node
  let next : app.Execution := { ticked with
    application := after
    environmentRecall := ticked.environmentRecall ++
      [⟨ticked.observeEnvironment app, .application (.expire event)⟩] }
  have step : runtime.interactionStep leaks players scheduler (.expire event) ticked =
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
  refine ⟨next, ?_, ?_⟩
  · rw [runtime.runInteractionPlan_append, tickLaw, PMF.pure_bind,
      runInteractionPlan, step, PMF.pure_bind]
    rfl
  · change (ticked.application.complete event tickReady _ _).publicView.missedBinding event = true
    apply ticked.application.missedBinding_complete event tickReady _ _ who payload outputEq
    rw [application]
    exact absent

/-- No unpublished response at the required slot means the reserved selection
waits. Expiry then supplies actual public evidence, rather than an inference
from a partial monitor's failure to observe a transmission. -/
theorem protected_binding_omission
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (scheduler : runtime.NetworkPolicy leaks)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (ready : execution.application.config.cut.Ready event)
    (absent : execution.application.accepted (.inr event) = none)
    (published : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id)
    (entered ticks : Nat)
    (activated : execution.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ execution.application.clock + ticks - entered) :
    ∃ next, runtime.runInteractionPlan leaks players scheduler
        (.includeLatest event who :: List.replicate ticks .tick ++ [.expire event]) execution =
          PMF.pure next ∧
      next.application.publicView.missedBinding event = true := by
  let app := runtime.reactiveApplication leaks
  let waited : app.Execution := { execution with
    environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .wait⟩] }
  have waitLaw : runtime.interactionStep leaks players scheduler
      (.includeLatest event who) execution = PMF.pure waited := by
    rw [runtime.interaction_includeLatest_of_pending_published leaks players scheduler execution
      who event published]
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
    rfl
  obtain ⟨next, suffix, omitted⟩ := runtime.binding_deadline_omission leaks
    players scheduler waited who event payload outputEq codeEq node
      ready absent entered ticks activated due
  refine ⟨next, ?_, omitted⟩
  rw [List.cons_append, runInteractionPlan, waitLaw, PMF.pure_bind]
  exact suffix

/-- Collection evidence from the protected block survives arbitrary later
native responses and scheduling, including further deviations. -/
theorem protected_binding_omission_persists
    (event : graph.EventId) (who : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding who payload)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (count : Nat) (before after : (runtime.reactiveApplication leaks).Execution)
    (omitted : before.application.publicView.missedBinding event = true)
    (reached : after ∈ ((runtime.reactiveApplication leaks).runRounds scheduler players count
      before).support) : after.application.publicView.missedBinding event = true :=
  (ReactiveApplication.Invariant.policyInvariant (runtime.reactiveApplication leaks)
    (runtime.reactiveMissedBindingInvariant leaks event who payload binding)
      players).runRounds scheduler count before after omitted reached

end Vegas.EventGraphRuntime
