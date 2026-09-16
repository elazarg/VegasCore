/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventPotential
import Vegas.Pending.EventResolutionBlock

/-! # Continuation potential across prescribed resolution staging -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Once the first resolution choice has been remembered, the remaining
private staging call and public submission leave its semantic continuation
law unchanged. -/
theorem resolutionBlockContinuation_continuationLaw
    (runtime : EventGraphRuntime graph) (profile : graph.BehavioralProfile)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (DeferredCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (execution : runtime.application.PolicyExecution)
    (action : graph.Action event)
    (actor : graph.actor? event = some owner)
    (emptyCache : execution.native.application.remembered event = none) :
    (runtime.resolutionBlockContinuation owner event payload binding checks outputEq
        execution action).bind
        (fun next => next.native.application.continuationLaw profile) =
      (runtime.application.playerStep owner execution
        (.privateCommand (.remember event action))).bind
          (fun next => next.native.application.continuationLaw profile) := by
  let first := runtime.application.afterPrivate execution owner (.remember event action)
  have firstRemembered : first.native.application.remembered event = some action :=
    runtime.afterPrivate_remembered_same execution owner event action actor emptyCache
  have secondNative : (runtime.application.afterPrivate first owner
      (.remember event action)).native.application = first.native.application := by
    change privateStep first.native.application owner (.remember event action) =
      first.native.application
    simp [privateStep, actor, firstRemembered]
  let second := runtime.application.afterPrivate first owner (.remember event action)
  obtain ⟨packet, submission, _addressed⟩ :=
    runtime.resolutionSubmission_address owner event payload binding checks outputEq action
      (MessageApplication.State.observe runtime.application second.native owner)
  unfold resolutionBlockContinuation
  rw [runtime.application.playerStep_private_eq execution owner (.remember event action),
    FinDist.pure_bind]
  change ((runtime.application.playerStep owner first
      (.privateCommand (.remember event action))).bind fun second =>
        runtime.application.playerStep owner second
          (runtime.resolutionSubmission owner event payload binding checks outputEq action
            (MessageApplication.State.observe runtime.application second.native owner))).bind
      (fun next => next.native.application.continuationLaw profile) = _
  rw [runtime.application.playerStep_private_eq first owner (.remember event action),
    FinDist.pure_bind]
  change (runtime.application.playerStep owner second
      (runtime.resolutionSubmission owner event payload binding checks outputEq action
        (MessageApplication.State.observe runtime.application second.native owner))).bind
      (fun next => next.native.application.continuationLaw profile) = _
  rw [submission, runtime.application.playerStep_submit_eq, FinDist.pure_bind]
  simp only [FinDist.pure_bind]
  change (runtime.application.afterSubmit second owner packet).native.application.continuationLaw
      profile = first.native.application.continuationLaw profile
  change second.native.application.continuationLaw profile = _
  rw [secondNative]

/-- The actual compiled three-call resolution block preserves the memoized
canonical continuation potential in expectation. Inclusion is deliberately
not part of this staging-only law. -/
theorem runServicePlan_compiled_resolve_continuationLaw
    (runtime : EventGraphRuntime graph) (ordered : graph.BarrierOrdered)
    (profile : graph.BehavioralProfile)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (execution : runtime.application.PolicyExecution)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (DeferredCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (viewNode : nodeView graph event =
      .resolve owner payload binding checks outputEq codeEq)
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
  rw [runtime.runServicePlan_compiled_resolve_block owner (profile owner) players wire
    execution event owner payload binding checks outputEq codeEq viewNode playersOwner grant
    ready actor stage notSubmitted emptyCache]
  rw [FinDist.bind_bind]
  apply Eq.trans (FinDist.bind_congr fun action _ =>
    runtime.resolutionBlockContinuation_continuationLaw profile owner event payload binding
      checks outputEq execution action actor emptyCache)
  exact runtime.playerStep_remember_continuation ordered profile execution event ready owner
    actor emptyCache

end Vegas.EventGraphRuntime
