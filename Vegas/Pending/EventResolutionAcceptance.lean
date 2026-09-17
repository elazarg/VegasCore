/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventResolutionBlock
import Vegas.Pending.EventDisclosure
import Vegas.Pending.EventInclusion

/-! # Prescribed resolution acceptance -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Reserved inclusion immediately after the resolution block realizes the
exact graph resolution step through the native message service. -/
theorem resolutionBlockContinuation_includeLatest_law
    (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (viewNode : nodeView graph event =
      .resolve owner payload binding checks outputEq codeEq)
    (execution : runtime.application.PolicyExecution) (action : graph.Action event)
    (ready : execution.native.application.config.cut.Ready event)
    (timely : execution.native.application.WithinDeadline runtime event)
    (invariant : execution.native.application.BindingInvariant)
    (actor : graph.actor? event = some owner)
    (emptyCache : execution.native.application.remembered event = none)
    (serialFresh : execution.native.pool.lookup
      (owner, execution.native.pool.nextSerial owner) = none) :
    ((runtime.resolutionBlockContinuation owner event payload binding checks outputEq
        execution action).bind
        (runtime.serviceStep players wire (.includeLatest event owner))).map
        (fun next => next.native.application.config) =
      execution.native.application.config.step event ready action := by
  let first := runtime.application.afterPrivate execution owner (.remember event action)
  let second := runtime.application.afterPrivate first owner (.remember event action)
  have firstRemembered : first.native.application.remembered event = some action :=
    runtime.afterPrivate_remembered_same execution owner event action actor emptyCache
  have secondRemembered : second.native.application.remembered event = some action := by
    change (privateStep first.native.application owner
      (.remember event action)).remembered event = some action
    simp [privateStep, actor, firstRemembered]
  have secondReady : second.native.application.config.cut.Ready event := by
    simpa [second, first] using ready
  have secondTimely : second.native.application.WithinDeadline runtime event := by
    have firstFacts := privateStep_facts execution.native.application owner
      (.remember event action)
    have secondFacts := privateStep_facts first.native.application owner
      (.remember event action)
    have firstClock : first.native.application.clock =
        execution.native.application.clock := by
      change (privateStep execution.native.application owner
        (.remember event action)).clock = _
      exact firstFacts.2.1
    have firstActivated : first.native.application.activatedAt =
        execution.native.application.activatedAt := by
      change (privateStep execution.native.application owner
        (.remember event action)).activatedAt = _
      exact firstFacts.2.2
    have secondClock : second.native.application.clock =
        first.native.application.clock := by
      change (privateStep first.native.application owner
        (.remember event action)).clock = _
      exact secondFacts.2.1
    have secondActivated : second.native.application.activatedAt =
        first.native.application.activatedAt := by
      change (privateStep first.native.application owner
        (.remember event action)).activatedAt = _
      exact secondFacts.2.2
    unfold State.WithinDeadline at timely ⊢
    rw [secondClock, secondActivated, firstClock, firstActivated]
    exact timely
  have firstInvariant : first.native.application.BindingInvariant := by
    exact privateStep_bindingInvariant execution.native.application invariant owner
      (.remember event action)
  have secondInvariant : second.native.application.BindingInvariant := by
    exact privateStep_bindingInvariant first.native.application firstInvariant owner
      (.remember event action)
  obtain ⟨result, packet, resolved, submission, handled⟩ :=
    runtime.handle_resolutionSubmission_eq second.native event owner payload binding checks
      outputEq codeEq viewNode secondReady secondTimely action secondRemembered
      secondInvariant (execution.native.pool.nextSerial owner)
  have block : runtime.resolutionBlockContinuation owner event payload binding checks outputEq
      execution action = FinDist.pure (runtime.application.afterSubmit second owner packet) := by
    simp only [resolutionBlockContinuation, runtime.application.playerStep_private_eq,
      FinDist.pure_bind]
    rw [submission, runtime.application.playerStep_submit_eq]
  have inclusion := runtime.serviceStep_includeLatest_afterSubmit_native players wire
    second event owner packet
    (second.native.application.complete event secondReady action
      (cast (congrArg EventField.Value outputEq.symm) result))
    (by
      have address := runtime.resolutionSubmission_address owner event payload binding checks
        outputEq action (MessageApplication.State.observe runtime.application second.native owner)
      obtain ⟨selected, selectedEq, addressed⟩ := address
      rw [submission] at selectedEq
      simp only [MessageInterface.PlayerCommand.submit.injEq] at selectedEq
      subst selected
      exact addressed)
    serialFresh handled
  have projected := congrArg (fun law => law.map
    (fun native : runtime.application.State => native.application.config)) inclusion
  simp only [FinDist.map_comp, Function.comp_def, FinDist.map_pure] at projected
  rw [block, FinDist.pure_bind, projected]
  have resolvedInitial : EventCode.resolveOutput? binding checks
      (cast (congrArg EventField.Action outputEq) action)
      execution.native.application.config.store = some result := by
    simpa [second, first] using resolved
  have graphLaw := execution.native.application.config.step_eq_map_of_code event ready
    outputEq (.resolve owner payload binding checks) codeEq
    (cast (congrArg EventField.Action outputEq) action) (FinDist.pure result)
  rw [EventCode.resolve_eval?, resolvedInitial] at graphLaw
  specialize graphLaw (by rfl)
  simp only [cast_cast, cast_eq, FinDist.map_pure] at graphLaw
  have firstConfig : first.native.application.config =
      execution.native.application.config := by simp [first]
  have secondConfig : second.native.application.config =
      execution.native.application.config := by simpa [second] using firstConfig
  change FinDist.pure (second.native.application.config.complete event secondReady action
      (cast (congrArg EventField.Value outputEq.symm) result)) = _
  have complete_congr {left right : graph.Config} (same : left = right)
      (leftReady : left.cut.Ready event) (rightReady : right.cut.Ready event)
      (value : (graph.outputLayout event).Value) :
      left.complete event leftReady action value =
        right.complete event rightReady action value := by
    subst right
    rfl
  have completionEq : second.native.application.config.complete event secondReady action
      (cast (congrArg EventField.Value outputEq.symm) result) =
      execution.native.application.config.complete event ready action
        (cast (congrArg EventField.Value outputEq.symm) result) := by
    exact complete_congr secondConfig secondReady ready _
  rw [completionEq]
  exact graphLaw.symm

/-- The compiled three owner calls followed immediately by reserved inclusion
are exactly one normalized policy draw followed by the graph resolution step. -/
theorem runServicePlan_compiled_resolve_includeLatest
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (execution : runtime.application.PolicyExecution)
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (viewNode : nodeView graph event =
      .resolve owner payload binding checks outputEq codeEq)
    (playersOwner : players owner = runtime.compilePlayerPolicy owner policy)
    (grant : execution.native.application.serviceGrant = some event)
    (ready : execution.native.application.config.cut.Ready event)
    (timely : execution.native.application.WithinDeadline runtime event)
    (invariant : execution.native.application.BindingInvariant)
    (actor : graph.actor? event = some owner)
    (stage : stagingCount (execution.principalHistory owner) event = 0)
    (notSubmitted : submittedAt (execution.principalHistory owner) event = false)
    (emptyCache : execution.native.application.remembered event = none)
    (serialFresh : execution.native.pool.lookup
      (owner, execution.native.pool.nextSerial owner) = none) :
    (runtime.runServicePlan players wire
        (List.replicate 3 (.player owner) ++ [.includeLatest event owner]) execution).map
        (fun next => next.native.application.config) =
      (graph.normalizePolicy owner policy event actor
        (graph.playerObserve owner execution.native.application.config)).bind
          (execution.native.application.config.step event ready) := by
  rw [runtime.runServicePlan_append players wire]
  rw [runtime.runServicePlan_compiled_resolve_block owner policy players wire execution
    event owner payload binding checks outputEq codeEq viewNode playersOwner grant ready actor
    stage notSubmitted emptyCache]
  rw [FinDist.bind_bind, FinDist.map_bind]
  apply FinDist.bind_congr
  intro action _
  simpa only [runServicePlan, FinDist.bind_pure] using
    runtime.resolutionBlockContinuation_includeLatest_law players wire owner event payload
      binding checks outputEq codeEq viewNode execution action ready timely invariant actor
      emptyCache serialFresh

end Vegas.EventGraphRuntime
