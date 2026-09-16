/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventPotential
import Vegas.Pending.EventBindingAcceptance

/-! # Continuation preservation by prescribed binding blocks -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Once the action has been sampled, private staging and public commitment
submission leave the continuation law unchanged. -/
theorem bindingBlockContinuation_continuation (runtime : EventGraphRuntime graph)
    (profile : graph.BehavioralProfile) (owner : Player) (event : graph.EventId)
    (payload : L.Ty) (outputEq : graph.outputLayout event = .binding owner payload)
    (execution : runtime.application.PolicyExecution) (action : graph.Action event)
    (actor : graph.actor? event = some owner)
    (empty : execution.native.application.remembered event = none) :
    (runtime.bindingBlockContinuation owner event payload outputEq execution action).bind
        (fun next => next.native.application.continuationLaw profile) =
      (runtime.application.playerStep owner execution
        (.privateCommand (.remember event action))).bind
          (fun next => next.native.application.continuationLaw profile) := by
  obtain ⟨command, stage⟩ :=
    runtime.bindingStageCommand_is_private event payload outputEq action
  rw [runtime.bindingBlockContinuation_eq_pure owner event payload outputEq execution
    action command stage, FinDist.pure_bind,
    runtime.application.playerStep_private_eq, FinDist.pure_bind]
  let first := runtime.application.afterPrivate execution owner (.remember event action)
  have remembered : first.native.application.remembered event = some action :=
    runtime.afterPrivate_remembered_same execution owner event action actor empty
  change (privateStep first.native.application owner command).continuationLaw profile =
    first.native.application.continuationLaw profile
  unfold bindingStageCommand at stage
  generalize cast (congrArg EventField.Action outputEq) action = result at stage
  cases result with
  | failure =>
      simp only [MessageInterface.PlayerCommand.privateCommand.injEq] at stage
      subst command
      simp only [privateStep, dif_pos actor, remembered]
  | success value =>
      simp only [MessageInterface.PlayerCommand.privateCommand.injEq] at stage
      subst command
      rfl

/-- The actual three-call binding policy block preserves the future semantic
law in expectation, including its private action draw and opaque submission.
This is before inclusion, so it needs no candidate or delivery assumption. -/
theorem runServicePlan_compiled_bind_continuation (runtime : EventGraphRuntime graph)
    (ordered : graph.BarrierOrdered) (profile : graph.BehavioralProfile)
    (owner : Player) (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (execution : runtime.application.PolicyExecution)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (viewNode : nodeView graph event = .bind owner payload outputEq codeEq)
    (playersOwner : players owner = runtime.compilePlayerPolicy owner (profile owner))
    (grant : execution.native.application.serviceGrant = some event)
    (ready : execution.native.application.config.cut.Ready event)
    (actor : graph.actor? event = some owner)
    (stage : stagingCount (execution.principalHistory owner) event = 0)
    (notSubmitted : submittedAt (execution.principalHistory owner) event = false)
    (emptyCache : execution.native.application.remembered event = none) :
    (runtime.runServicePlan players wire (List.replicate 3 (.player owner)) execution).bind
        (fun next => next.native.application.continuationLaw profile) =
      execution.native.application.continuationLaw profile := by
  rw [runtime.runServicePlan_compiled_bind_block owner (profile owner) players wire execution
    event owner payload outputEq codeEq viewNode playersOwner grant ready actor stage
    notSubmitted emptyCache, FinDist.bind_bind]
  calc
    _ = (graph.normalizePolicy owner (profile owner) event actor
        (graph.playerObserve owner execution.native.application.config)).bind
          (fun action => (runtime.application.playerStep owner execution
            (.privateCommand (.remember event action))).bind
              (fun next => next.native.application.continuationLaw profile)) := by
      apply FinDist.bind_congr
      intro action _
      exact runtime.bindingBlockContinuation_continuation profile owner event payload
        outputEq execution action actor emptyCache
    _ = _ := runtime.playerStep_remember_continuation ordered profile execution
      event ready owner actor emptyCache

end Vegas.EventGraphRuntime
