/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventPolicyBlock
import Vegas.Pending.EventInvariant
import Vegas.Pending.EventInclusion

/-! # Prescribed binding preparation and acceptance

The binding block stages the selected typed graph action at its canonical
handle. Freshness is explicit: arbitrary player policies may reuse or prepare
that handle differently, and are not covered by the prescribed-block law.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

private theorem remember_candidates (state : State graph) (who : Player)
    (event : graph.EventId) (action : graph.Action event) :
    (privateStep state who (.remember event action)).candidates = state.candidates := by
  by_cases owned : graph.actor? event = some who
  · rw [privateStep, dif_pos owned]
    cases state.remembered event <;> rfl
  · rw [privateStep, dif_neg owned]

/-- Private staging at a fresh canonical handle implements exactly the
selected typed binding action, including failure without preparation. -/
theorem bindingStageCommand_result (runtime : EventGraphRuntime graph)
    (state : State graph) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (action : graph.Action event) (command : PrivateCommand graph)
    (stage : runtime.bindingStageCommand event payload outputEq action =
      .privateCommand command)
    (fresh : state.candidates.lookup (owner, eventSlot event) = .fresh) :
    (privateStep state owner command).bindingResult (owner, eventSlot event) payload =
      cast (congrArg EventField.Action outputEq) action := by
  unfold bindingStageCommand at stage
  generalize resultEq : cast (congrArg EventField.Action outputEq) action = result at *
  cases result with
  | failure =>
      simp only [MessageInterface.PlayerCommand.privateCommand.injEq] at stage
      subst command
      simp only [State.bindingResult, remember_candidates, fresh]
  | success value =>
      simp only [MessageInterface.PlayerCommand.privateCommand.injEq] at stage
      subst command
      simp only [eventSlot] at fresh
      simp [privateStep, State.bindingResult, eventSlot,
        CommitmentCandidates.lookup_prepare_self, fresh, Raw.as?]

/-- The selected-action continuation is deterministic and retains the full
native execution record. -/
theorem bindingBlockContinuation_eq_pure (runtime : EventGraphRuntime graph)
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    {owner : Player} (outputEq : graph.outputLayout event = .binding owner payload)
    (execution : runtime.application.PolicyExecution) (action : graph.Action event)
    (command : PrivateCommand graph)
    (stage : runtime.bindingStageCommand event payload outputEq action =
      .privateCommand command) :
    runtime.bindingBlockContinuation who event payload outputEq execution action =
      FinDist.pure (runtime.application.afterSubmit
        (runtime.application.afterPrivate
          (runtime.application.afterPrivate execution who (.remember event action)) who command)
        who (.commitment event (who, eventSlot event))) := by
  simp only [bindingBlockContinuation, stage, runtime.application.playerStep_private_eq,
    FinDist.pure_bind, runtime.application.playerStep_submit_eq]

/-- Before inclusion, every selected binding action exposes exactly the same
public submission. The joint environment history and observation retain the
full pending pool and receipts, but not the selected value or failure. -/
theorem bindingBlockContinuation_environment_law (runtime : EventGraphRuntime graph)
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    {owner : Player} (outputEq : graph.outputLayout event = .binding owner payload)
    (execution : runtime.application.PolicyExecution) (action : graph.Action event) :
    (runtime.bindingBlockContinuation who event payload outputEq execution action).map
        (fun next => (next.environmentHistory,
          MessageApplication.State.environmentView runtime.application next.native)) =
      FinDist.pure (execution.environmentHistory,
        MessageApplication.State.environmentView runtime.application
        (runtime.application.afterSubmit execution who
          (.commitment event (who, eventSlot event))).native) := by
  obtain ⟨command, stage⟩ :=
    runtime.bindingStageCommand_is_private event payload outputEq action
  rw [runtime.bindingBlockContinuation_eq_pure who event payload outputEq execution
    action command stage, FinDist.map_pure]
  change FinDist.pure (execution.environmentHistory, MessageInterface.EnvironmentObservation.mk
    (execution.native.pool.submit who (.commitment event (who, eventSlot event))).2
    (privateStep (privateStep execution.native.application who (.remember event action))
      who command).publicView execution.native.receipts) = _
  rw [privateStep_publicView, privateStep_publicView]
  rfl

/-- Other players' joint history and observation likewise retain exactly the
fixed opaque pending packet and their own unchanged private information. -/
theorem bindingBlockContinuation_observer_law (runtime : EventGraphRuntime graph)
    (who observer : Player) (different : observer ≠ who)
    (event : graph.EventId) (payload : L.Ty)
    {owner : Player} (outputEq : graph.outputLayout event = .binding owner payload)
    (execution : runtime.application.PolicyExecution) (action : graph.Action event) :
    (runtime.bindingBlockContinuation who event payload outputEq execution action).map
        (fun next => (next.principalHistory observer,
          MessageApplication.State.observe runtime.application next.native observer)) =
      FinDist.pure (execution.principalHistory observer,
        MessageApplication.State.observe runtime.application
        (runtime.application.afterSubmit execution who
          (.commitment event (who, eventSlot event))).native observer) := by
  obtain ⟨command, stage⟩ :=
    runtime.bindingStageCommand_is_private event payload outputEq action
  rw [runtime.bindingBlockContinuation_eq_pure who event payload outputEq execution
    action command stage, FinDist.map_pure]
  have historyEq : (runtime.application.afterSubmit
      (runtime.application.afterPrivate
        (runtime.application.afterPrivate execution who (.remember event action)) who command)
      who (.commitment event (who, eventSlot event))).principalHistory observer =
        execution.principalHistory observer := by
    simp only [MessageApplication.afterSubmit, MessageApplication.afterPrivate, different,
      ↓reduceIte]
  rw [historyEq]
  change FinDist.pure (execution.principalHistory observer, MessageInterface.View.mk
    ((execution.native.pool.submit who (.commitment event (who, eventSlot event))).2.observe
      observer)
    ((privateStep (privateStep execution.native.application who (.remember event action))
      who command).playerView observer) execution.native.receipts) = _
  rw [privateStep_playerView_other _ _ _ different,
    privateStep_playerView_other _ _ _ different]
  rfl

/-- After the actual binding block, accepting its prescribed packet completes
the graph with exactly the sampled action and typed output. Candidate freshness
and handle availability are entry conditions, not assumed acceptance. -/
theorem bindingBlockContinuation_handle (runtime : EventGraphRuntime graph)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (viewNode : nodeView graph event = .bind owner payload outputEq codeEq)
    (execution next : runtime.application.PolicyExecution) (action : graph.Action event)
    (ready : execution.native.application.config.cut.Ready event)
    (timely : execution.native.application.WithinDeadline runtime event)
    (fresh : execution.native.application.candidates.lookup (owner, eventSlot event) = .fresh)
    (vacant : execution.native.application.accepted (.inr event) = none)
    (unused : execution.native.application.HandleUnused (owner, eventSlot event))
    (supported : next ∈
      (runtime.bindingBlockContinuation owner event payload outputEq execution action).support)
    (nonce : Nat) :
    (handle runtime next.native.application
      ⟨(owner, nonce), .commitment event (owner, eventSlot event)⟩).map State.config =
      some (execution.native.application.config.complete event ready action
        (cast (congrArg EventField.Value outputEq.symm)
          (cast (congrArg EventField.Action outputEq) action))) := by
  obtain ⟨command, stage⟩ :=
    runtime.bindingStageCommand_is_private event payload outputEq action
  rw [runtime.bindingBlockContinuation_eq_pure owner event payload outputEq
    execution action command stage, FinDist.mem_support_pure] at supported
  subst next
  let first := privateStep execution.native.application owner (.remember event action)
  let second := privateStep first owner command
  have firstFacts := privateStep_facts execution.native.application owner (.remember event action)
  have secondFacts := privateStep_facts first owner command
  have configEq : second.config = execution.native.application.config :=
    secondFacts.1.trans firstFacts.1
  have acceptedEq : second.accepted = execution.native.application.accepted :=
    (privateStep_accepted first owner command).trans
      (privateStep_accepted execution.native.application owner (.remember event action))
  have secondReady : second.config.cut.Ready event := by simpa only [configEq] using ready
  have secondTimely : second.WithinDeadline runtime event := by
    have clockEq : second.clock = execution.native.application.clock :=
      secondFacts.2.1.trans firstFacts.2.1
    have activatedEq : second.activatedAt = execution.native.application.activatedAt :=
      secondFacts.2.2.trans firstFacts.2.2
    simpa only [State.WithinDeadline, clockEq, activatedEq] using timely
  have secondVacant : second.accepted (.inr event) = none := by
    simpa only [acceptedEq] using vacant
  have secondUnused : second.HandleUnused (owner, eventSlot event) := by
    simpa only [State.HandleUnused, acceptedEq] using unused
  have firstFresh : first.candidates.lookup (owner, eventSlot event) = .fresh := by
    simpa only [first, remember_candidates] using fresh
  have result := runtime.bindingStageCommand_result first owner event payload outputEq
    action command stage firstFresh
  have actionRoundtrip : cast (congrArg EventField.Action outputEq.symm)
      (cast (congrArg EventField.Action outputEq) action) = action := by
    simp only [cast_cast, cast_eq]
  change (handle runtime second
    ⟨(owner, nonce), .commitment event (owner, eventSlot event)⟩).map State.config = _
  rw [runtime.handle_commitment_eq second (owner, nonce) event (owner, eventSlot event)
    owner payload outputEq codeEq viewNode secondReady secondTimely rfl rfl
    secondVacant secondUnused, Option.map_some]
  change some (second.config.complete event secondReady
    (cast (congrArg EventField.Action outputEq.symm) (second.bindingResult _ payload))
    (cast (congrArg EventField.Value outputEq.symm) (second.bindingResult _ payload))) = _
  change second.bindingResult _ payload = _ at result
  rw [result, actionRoundtrip]
  simp only [configEq]

/-- Reserved inclusion of the submitted binding packet realizes exactly one
graph step through the actual message pool and service instruction. -/
theorem bindingBlockContinuation_includeLatest_law (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (viewNode : nodeView graph event = .bind owner payload outputEq codeEq)
    (execution : runtime.application.PolicyExecution) (action : graph.Action event)
    (ready : execution.native.application.config.cut.Ready event)
    (timely : execution.native.application.WithinDeadline runtime event)
    (fresh : execution.native.application.candidates.lookup (owner, eventSlot event) = .fresh)
    (vacant : execution.native.application.accepted (.inr event) = none)
    (unused : execution.native.application.HandleUnused (owner, eventSlot event))
    (serialFresh : execution.native.pool.lookup
      (owner, execution.native.pool.nextSerial owner) = none) :
    ((runtime.bindingBlockContinuation owner event payload outputEq execution action).bind
        (runtime.serviceStep players wire (.includeLatest event owner))).map
        (fun next => next.native.application.config) =
      execution.native.application.config.step event ready action := by
  obtain ⟨command, stage⟩ :=
    runtime.bindingStageCommand_is_private event payload outputEq action
  let staged := runtime.application.afterPrivate
    (runtime.application.afterPrivate execution owner (.remember event action)) owner command
  let submitted := runtime.application.afterSubmit staged owner
    (.commitment event (owner, eventSlot event))
  have block : runtime.bindingBlockContinuation owner event payload outputEq execution action =
      FinDist.pure submitted :=
    runtime.bindingBlockContinuation_eq_pure owner event payload outputEq execution action
      command stage
  have acceptedProjection := runtime.bindingBlockContinuation_handle owner event payload
    outputEq codeEq viewNode execution submitted action ready timely fresh vacant unused
    (by rw [block]; exact FinDist.mem_support_pure.mpr rfl)
    (execution.native.pool.nextSerial owner)
  change (handle runtime staged.native.application
    ⟨(owner, staged.native.pool.nextSerial owner),
      .commitment event (owner, eventSlot event)⟩).map State.config = _ at acceptedProjection
  cases accepted : handle runtime staged.native.application
      ⟨(owner, staged.native.pool.nextSerial owner),
        .commitment event (owner, eventSlot event)⟩ with
  | none => simp [accepted] at acceptedProjection
  | some nextState =>
      have configEq := Option.some.inj (by
        simpa only [accepted, Option.map_some] using acceptedProjection)
      have inclusion := runtime.serviceStep_includeLatest_afterSubmit_native players wire
        staged event owner (.commitment event (owner, eventSlot event)) nextState rfl
        serialFresh accepted
      have projected := congrArg (fun law => law.map
        (fun native : runtime.application.State => native.application.config)) inclusion
      simp only [FinDist.map_comp, Function.comp_def, FinDist.map_pure] at projected
      rw [block, FinDist.pure_bind]
      change (runtime.serviceStep players wire (.includeLatest event owner)
        (runtime.application.afterSubmit staged owner
          (.commitment event (owner, eventSlot event)))).map
          (fun next => next.native.application.config) = _
      rw [projected, configEq]
      have graphLaw := execution.native.application.config.step_eq_map_of_code event ready
        outputEq (.bind owner payload) codeEq
        (cast (congrArg EventField.Action outputEq) action)
        (FinDist.pure (cast (congrArg EventField.Action outputEq) action)) rfl
      simpa only [cast_cast, cast_eq, FinDist.map_pure] using graphLaw.symm

/-- Three prescribed owner invocations followed by their reserved inclusion
implement the exact normalized binding-policy kernel. This is a local service
law; preservation through intervening wire/reaction instructions is separate. -/
theorem runServicePlan_compiled_bind_includeLatest (runtime : EventGraphRuntime graph)
    (owner : Player) (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (execution : runtime.application.PolicyExecution)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (viewNode : nodeView graph event = .bind owner payload outputEq codeEq)
    (playersOwner : players owner = runtime.compilePlayerPolicy owner policy)
    (grant : execution.native.application.serviceGrant = some event)
    (ready : execution.native.application.config.cut.Ready event)
    (actor : graph.actor? event = some owner)
    (stage : stagingCount (execution.principalHistory owner) event = 0)
    (notSubmitted : submittedAt (execution.principalHistory owner) event = false)
    (emptyCache : execution.native.application.remembered event = none)
    (timely : execution.native.application.WithinDeadline runtime event)
    (fresh : execution.native.application.candidates.lookup (owner, eventSlot event) = .fresh)
    (vacant : execution.native.application.accepted (.inr event) = none)
    (unused : execution.native.application.HandleUnused (owner, eventSlot event))
    (serialFresh : execution.native.pool.lookup
      (owner, execution.native.pool.nextSerial owner) = none) :
    (runtime.runServicePlan players wire
      (List.replicate 3 (.player owner) ++ [.includeLatest event owner]) execution).map
        (fun next => next.native.application.config) =
      (graph.normalizePolicy owner policy event actor
        (graph.playerObserve owner execution.native.application.config)).bind
          (execution.native.application.config.step event ready) := by
  rw [runtime.runServicePlan_append,
    runtime.runServicePlan_compiled_bind_block owner policy players wire execution
      event owner payload outputEq codeEq viewNode playersOwner grant ready actor
      stage notSubmitted emptyCache, FinDist.bind_bind, FinDist.map_bind]
  apply FinDist.bind_congr
  intro action _
  simpa only [runServicePlan, FinDist.bind_pure] using
    runtime.bindingBlockContinuation_includeLatest_law players wire owner event payload
      outputEq codeEq viewNode execution action ready timely fresh vacant unused serialFresh

end Vegas.EventGraphRuntime
