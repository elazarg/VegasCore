/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventHonestBlockBase
import Vegas.Pending.EventHonestReaction
import Vegas.Pending.EventResolutionAcceptance

/-! # Honest resolution through adaptive message reactions -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

private theorem resolution_reacted_action (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (profile : graph.BehavioralProfile)
    (wire : runtime.application.WirePolicy) (execution : runtime.application.PolicyExecution)
    (boundary : HonestBoundary runtime inputs execution)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (viewNode : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (grant : execution.native.application.serviceGrant = some event)
    (ready : execution.native.application.config.cut.Ready event)
    (timely : execution.native.application.WithinDeadline runtime event)
    (actor : graph.actor? event = some owner) (action : graph.Action event)
    (plan : List (ServiceInstruction graph))
    (allowed : ∀ instruction ∈ plan, HonestReactionInstruction instruction) :
    let law := (runtime.resolutionBlockContinuation owner event payload binding checks outputEq
      execution action).bind (runtime.runServicePlan (runtime.compileProfile profile) wire
        (plan ++ [.includeLatest event owner]))
    law.map (fun next => next.native.application.config) =
      execution.native.application.config.step event ready action ∧
    ∀ next ∈ law.support, HonestBoundary runtime inputs next := by
  dsimp only
  let first := runtime.application.afterPrivate execution owner (.remember event action)
  let second := runtime.application.afterPrivate first owner (.remember event action)
  have empty := boundary.remembered_unfinished event ready.1
  have firstState : first.native.application =
      { execution.native.application with
        remembered := Function.update execution.native.application.remembered
          event (some action) } := by
    change privateStep execution.native.application owner (.remember event action) = _
    simp only [privateStep, dite_eq_left actor, empty]
  have firstRemembered : first.native.application.remembered event = some action := by
    rw [firstState]
    simp
  have secondState : second.native.application = first.native.application := by
    change privateStep first.native.application owner (.remember event action) = _
    simp only [privateStep, dite_eq_left actor, firstRemembered]
  have secondReady : second.native.application.config.cut.Ready event := by
    simpa only [secondState, firstState] using ready
  have secondTimely : second.native.application.WithinDeadline runtime event := by
    simpa only [State.WithinDeadline, secondState, firstState] using timely
  have secondInvariant : second.native.application.Invariant inputs :=
    privateStep_invariant first.native.application
      (privateStep_invariant execution.native.application boundary.invariant owner
        (.remember event action)) owner (.remember event action)
  have secondBinding : second.native.application.BindingInvariant :=
    privateStep_bindingInvariant first.native.application
      (privateStep_bindingInvariant execution.native.application boundary.bindingInvariant owner
        (.remember event action)) owner (.remember event action)
  obtain ⟨result, packet, _, submission, handled⟩ :=
    runtime.handle_resolutionSubmission_eq second.native event owner payload binding checks
      outputEq codeEq viewNode secondReady secondTimely action
      (by rw [secondState]; exact firstRemembered) secondBinding
      (execution.native.pool.nextSerial owner)
  let accepted := second.native.application.complete event secondReady action
    (cast (congrArg EventField.Value outputEq.symm) result)
  let message : Message Player (Payload graph) :=
    ⟨(owner, execution.native.pool.nextSerial owner), packet⟩
  let submitted := runtime.application.afterSubmit second owner packet
  have addressed : packet.event? graph = some event := by
    obtain ⟨selected, selectedEq, selectedAddress⟩ := runtime.resolutionSubmission_address owner
      event payload binding checks outputEq action
      (MessageApplication.State.observe runtime.application second.native owner)
    rw [submission] at selectedEq
    cases MessageInterface.PlayerCommand.submit.inj selectedEq
    exact selectedAddress
  have block : runtime.resolutionBlockContinuation owner event payload binding checks outputEq
      execution action = FinDist.pure submitted := by
    simp only [resolutionBlockContinuation, runtime.application.playerStep_private_eq,
      FinDist.pure_bind]
    rw [submission, runtime.application.playerStep_submit_eq]
  have grantBefore : second.native.application.serviceGrant = some event := by
    simpa only [secondState, firstState] using grant
  have grantAccepted : accepted.serviceGrant = some event := grantBefore
  have submittedHandled : handle runtime submitted.native.application message = some accepted := by
    simpa only [submitted, MessageApplication.afterSubmit, application, message, handle_submitStep]
      using handled
  have submittedGrant : submitted.native.application.serviceGrant = some event := by
    simpa only [submitted, MessageApplication.afterSubmit, application, submitStep_serviceGrant]
      using grantBefore
  have reactionState : runtime.HonestReactionState event owner submitted.native.application
      accepted message submitted := by
    refine ⟨?_, Or.inl ⟨rfl, ?_⟩⟩
    · simp [submitted, MessageApplication.afterSubmit, submittedAt, addressed]
    · change List.append (α := Message Player (Payload graph)) execution.native.pool.pending
        [message] = [message]
      rw [boundary.pending_empty]
      rfl
  have reacted next (member : next ∈ (runtime.runServicePlan (runtime.compileProfile profile)
      wire (plan ++ [.includeLatest event owner]) submitted).support) :=
    runtime.runServicePlan_honestReaction_includeLatest profile wire event owner
      submitted.native.application accepted message submittedHandled actor rfl addressed
      submittedGrant
      grantAccepted plan allowed submitted next reactionState member
  rw [block, FinDist.pure_bind]
  constructor
  · have projected : (runtime.runServicePlan (runtime.compileProfile profile) wire
        (plan ++ [.includeLatest event owner]) submitted).map
          (fun next => next.native.application.config) = FinDist.pure accepted.config := by
      apply FinDist.eq_pure_of_support_subset_singleton
      intro config supported
      rw [FinDist.support_map] at supported
      obtain ⟨next, member, rfl⟩ := supported
      change next.native.application.config = accepted.config
      rw [(reacted next member).1]
    rw [projected]
    have immediate := runtime.resolutionBlockContinuation_includeLatest_law
      (runtime.compileProfile profile) wire owner event payload binding checks outputEq codeEq
      viewNode execution action ready timely boundary.bindingInvariant actor empty
      (boundary.lookup_eq_none (owner, execution.native.pool.nextSerial owner))
    rw [block, FinDist.pure_bind] at immediate
    have includeLaw := runtime.serviceStep_includeLatest_afterSubmit_native
      (runtime.compileProfile profile) wire second event owner packet accepted addressed
      (boundary.lookup_eq_none (owner, execution.native.pool.nextSerial owner)) handled
    have includeConfig := congrArg (fun law : FinDist runtime.application.State =>
      law.map (fun native => native.application.config)) includeLaw
    simp only [FinDist.map_comp, Function.comp_def, FinDist.map_pure] at includeConfig
    rw [includeConfig] at immediate
    exact immediate
  · intro next member
    obtain ⟨nextState, nextEmpty, nextHistory⟩ := reacted next member
    have afterInvariant : next.native.application.Invariant inputs := by
      rw [nextState]
      exact handle_invariant runtime second.native.application accepted message
        secondInvariant handled
    have afterBinding : next.native.application.BindingInvariant := by
      rw [nextState]
      exact handle_bindingInvariant runtime second.native.application accepted message
        secondBinding handled
    apply boundary.after_completed_event event afterInvariant afterBinding nextEmpty
    · rw [nextState]
      exact Finset.mem_insert_self _ _
    · rw [nextState]
      simpa only [accepted, State.complete, Config.complete, secondState, firstState] using
        execution.native.application.config.cut.completed_subset_complete event ready
    · intro query different
      rw [nextState]
      change second.native.application.remembered query = _
      rw [secondState, firstState]
      exact Function.update_of_ne different _ _
    · intro who query different
      rw [(nextHistory who query).1, (nextHistory who query).2]
      by_cases same : who = owner
      · subst who
        simp [submitted, second, first, MessageApplication.afterSubmit,
          MessageApplication.afterPrivate, stagingCount, submittedAt, stagesEvent,
          addressed, different.symm]
      · simp [submitted, second, first, MessageApplication.afterSubmit,
          MessageApplication.afterPrivate, same]
    · intro query different
      rw [nextState]
      change second.native.application.accepted (.inr query) = _
      rw [secondState, firstState]
    · intro query who different
      rw [nextState]
      change second.native.application.candidates.lookup (who, eventSlot query) = _
      rw [secondState, firstState]
    · intro query who different unused
      rw [nextState]
      simpa only [State.HandleUnused, accepted, State.complete, secondState, firstState]
        using unused

/-- The complete prescribed resolution block, including arbitrary wire/player
reactions before reserved inclusion, implements one normalized graph step and
restores the clean boundary. -/
theorem HonestBoundary.resolve_reacted_block (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (profile : graph.BehavioralProfile)
    (wire : runtime.application.WirePolicy) (execution : runtime.application.PolicyExecution)
    (boundary : HonestBoundary runtime inputs execution)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (viewNode : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (grant : execution.native.application.serviceGrant = some event)
    (ready : execution.native.application.config.cut.Ready event)
    (timely : execution.native.application.WithinDeadline runtime event)
    (actor : graph.actor? event = some owner)
    (plan : List (ServiceInstruction graph))
    (allowed : ∀ instruction ∈ plan, HonestReactionInstruction instruction) :
    let law := runtime.runServicePlan (runtime.compileProfile profile) wire
      (List.replicate 3 (.player owner) ++ (plan ++ [.includeLatest event owner])) execution
    law.map (fun next => next.native.application.config) =
      graph.normalizedPolicyStep profile execution.native.application.config event ready ∧
    ∀ next ∈ law.support, HonestBoundary runtime inputs next := by
  dsimp only
  rw [runtime.runServicePlan_append,
    runtime.runServicePlan_compiled_resolve_block owner (profile owner)
      (runtime.compileProfile profile) wire execution event owner payload binding checks
      outputEq codeEq viewNode rfl grant ready actor
      (boundary.history_unfinished owner event ready.1).1
      (boundary.history_unfinished owner event ready.1).2
      (boundary.remembered_unfinished event ready.1), FinDist.bind_bind]
  constructor
  · rw [FinDist.map_bind]
    have perAction : ∀ action, _ := fun action =>
      (resolution_reacted_action runtime inputs profile wire execution boundary event owner
        payload binding checks outputEq codeEq viewNode grant ready timely actor action
        plan allowed).1
    calc
      _ = (graph.normalizePolicy owner (profile owner) event actor
          (graph.playerObserve owner execution.native.application.config)).bind
            (execution.native.application.config.step event ready) :=
        FinDist.bind_congr fun action _ => perAction action
      _ = _ := by
        unfold normalizedPolicyStep
        split
        · rename_i who owned
          have same := Option.some.inj (owned.symm.trans actor)
          subst who
          rfl
        · rename_i ownerless
          rw [actor] at ownerless
          contradiction
  · intro next member
    rw [FinDist.support_bind] at member
    simp only [Set.mem_iUnion] at member
    obtain ⟨action, _, supported⟩ := member
    exact (resolution_reacted_action runtime inputs profile wire execution boundary event owner
      payload binding checks outputEq codeEq viewNode grant ready timely actor action
      plan allowed).2 next supported

end Vegas.EventGraphRuntime
