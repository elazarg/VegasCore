/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventHonestBoundary
import Vegas.Pending.EventServiceLaw
import Vegas.EventGraph.StateCongruence

/-! # Chance and idle blocks of the prescribed event service -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Boundary conditions survive semantic progress when the associated private
tables and history counters are unchanged. -/
theorem HonestBoundary.frame {runtime : EventGraphRuntime graph} {inputs : graph.Inputs}
    {before after : runtime.application.PolicyExecution}
    (boundary : HonestBoundary runtime inputs before)
    (invariant : after.native.application.Invariant inputs)
    (binding : after.native.application.BindingInvariant)
    (completed : before.native.application.config.cut.completed ⊆
      after.native.application.config.cut.completed)
    (pending : after.native.pool.pending = [])
    (accepted : after.native.application.accepted = before.native.application.accepted)
    (candidates : after.native.application.candidates = before.native.application.candidates)
    (remembered : after.native.application.remembered = before.native.application.remembered)
    (history : ∀ who event,
      stagingCount (after.principalHistory who) event =
        stagingCount (before.principalHistory who) event ∧
      submittedAt (after.principalHistory who) event =
        submittedAt (before.principalHistory who) event) :
    HonestBoundary runtime inputs after := by
  have unfinished event (h : event ∉ after.native.application.config.cut.completed) :
      event ∉ before.native.application.config.cut.completed := fun done => h (completed done)
  refine ⟨invariant, binding, pending, ?_, ?_, ?_, ?_, ?_⟩
  · intro event h
    rw [remembered]
    exact boundary.remembered_unfinished event (unfinished event h)
  · intro who event h
    rw [(history who event).1, (history who event).2]
    exact boundary.history_unfinished who event (unfinished event h)
  · intro event h
    rw [accepted]
    exact boundary.accepted_unfinished event (unfinished event h)
  · intro event owner h actor
    rw [candidates]
    exact boundary.canonical_fresh_unfinished event owner (unfinished event h) actor
  · intro event owner h actor
    simpa only [State.HandleUnused, accepted] using
      boundary.canonical_unused_unfinished event owner (unfinished event h) actor

/-- A public application command preserves a clean boundary. Sample and expiry
commands may complete an event; none changes the pending pool or private staging. -/
theorem environmentPolicyStep_honestBoundary (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (execution next : runtime.application.PolicyExecution)
    (command : EnvironmentCommand graph)
    (boundary : HonestBoundary runtime inputs execution)
    (member : next ∈ (runtime.application.environmentPolicyStep execution
      (.application command)).support) : HonestBoundary runtime inputs next := by
  have native : next.native ∈ ((runtime.application.environmentPolicyStep execution
      (.application command)).map MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, member, rfl⟩
  rw [runtime.application.environmentStep_native] at native
  simp only [MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
    FinDist.support_map, Set.mem_image] at native
  obtain ⟨state, supported, stateEq⟩ := native
  have applicationEq : next.native.application = state := by rw [← stateEq]
  have tables := environmentStep_tables runtime execution.native.application state command supported
  have histories := runtime.application.environmentStep_principalHistory execution
    (.application command) next member
  apply boundary.frame
  · rw [applicationEq]
    exact environmentStep_invariant runtime execution.native.application state command
      boundary.invariant supported
  · rw [applicationEq]
    exact environmentStep_bindingInvariant runtime execution.native.application state command
      boundary.bindingInvariant supported
  · rw [applicationEq]
    exact environmentStep_completed_subset runtime execution.native.application state command
      supported
  · rw [← stateEq]
    exact boundary.pending_empty
  · rw [applicationEq]
    exact tables.1
  · rw [applicationEq]
    exact tables.2
  · rw [applicationEq]
    exact environmentStep_remembered runtime execution.native.application state command supported
  · intro who event
    rw [histories]
    exact ⟨rfl, rfl⟩

/-- A granted unavailable event causes every prescribed player to wait. -/
theorem compileProfile_wait_of_not_ready (runtime : EventGraphRuntime graph)
    (profile : graph.BehavioralProfile) (execution : runtime.application.PolicyExecution)
    (event : graph.EventId) (who : Player)
    (grant : execution.native.application.serviceGrant = some event)
    (unready : ¬execution.native.application.config.cut.Ready event) :
    runtime.compileProfile profile who (execution.principalHistory who)
      (MessageApplication.State.observe runtime.application execution.native who) =
        FinDist.pure .wait := by
  have unreadyView : ¬execution.native.application.publicView.EventReady event :=
    fun ready => unready ((State.publicView_eventReady _ _).mp ready)
  have observedGrant : (MessageApplication.State.observe runtime.application
      execution.native who).application.publicView.serviceGrant = some event := grant
  have observedUnready : ¬(MessageApplication.State.observe runtime.application
      execution.native who).application.publicView.EventReady event := unreadyView
  unfold compileProfile compilePlayerPolicy
  rw [observedGrant]
  simp [observedUnready]

private structure Quiet (runtime : EventGraphRuntime graph)
    (before after : runtime.application.PolicyExecution) : Prop where
  native : after.native = before.native
  history : ∀ who event,
    stagingCount (after.principalHistory who) event =
      stagingCount (before.principalHistory who) event ∧
    submittedAt (after.principalHistory who) event =
      submittedAt (before.principalHistory who) event

private theorem Quiet.refl (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution) : Quiet runtime execution execution :=
  ⟨rfl, fun _ _ => ⟨rfl, rfl⟩⟩

private theorem Quiet.trans {runtime : EventGraphRuntime graph}
    {before middle after : runtime.application.PolicyExecution}
    (first : Quiet runtime before middle) (second : Quiet runtime middle after) :
    Quiet runtime before after :=
  ⟨second.native.trans first.native, fun who event =>
    ⟨(second.history who event).1.trans (first.history who event).1,
      (second.history who event).2.trans (first.history who event).2⟩⟩

private theorem Quiet.boundary {runtime : EventGraphRuntime graph} {inputs : graph.Inputs}
    {before after : runtime.application.PolicyExecution}
    (quiet : Quiet runtime before after) (boundary : HonestBoundary runtime inputs before) :
    HonestBoundary runtime inputs after := by
  apply boundary.frame
  · simpa only [quiet.native] using boundary.invariant
  · simpa only [quiet.native] using boundary.bindingInvariant
  · rw [quiet.native]
  · simpa only [quiet.native] using boundary.pending_empty
  · rw [quiet.native]
  · rw [quiet.native]
  · rw [quiet.native]
  · exact quiet.history

private theorem environmentPolicyStep_quiet (runtime : EventGraphRuntime graph)
    (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.EnvironmentPolicyCommand)
    (law : (runtime.application.environmentPolicyStep execution command).map
      MessageInterface.PolicyExecution.native = FinDist.pure execution.native)
    (member : next ∈ (runtime.application.environmentPolicyStep execution command).support) :
    Quiet runtime execution next := by
  have projected : next.native ∈ ((runtime.application.environmentPolicyStep execution command).map
      MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, member, rfl⟩
  rw [law, FinDist.mem_support_pure] at projected
  refine ⟨projected, ?_⟩
  intro who event
  rw [runtime.application.environmentStep_principalHistory execution command next member]
  exact ⟨rfl, rfl⟩

private def IdleInstruction (event : graph.EventId) : ServiceInstruction graph → Prop
  | .player _ | .wire | .includeLatest _ _ => True
  | .sample selected => selected = event
  | _ => False

private theorem serviceStep_idle (runtime : EventGraphRuntime graph)
    (profile : graph.BehavioralProfile) (wire : runtime.application.WirePolicy)
    (event : graph.EventId) (instruction : ServiceInstruction graph)
    (execution next : runtime.application.PolicyExecution)
    (allowed : IdleInstruction event instruction)
    (grant : execution.native.application.serviceGrant = some event)
    (unready : ¬execution.native.application.config.cut.Ready event)
    (empty : execution.native.pool.pending = [])
    (member : next ∈ (runtime.serviceStep (runtime.compileProfile profile) wire
      instruction execution).support) : Quiet runtime execution next := by
  cases instruction with
  | player who =>
      simp only [serviceStep, MessageApplication.invoke] at member
      rw [runtime.compileProfile_wait_of_not_ready profile execution event who grant unready,
        FinDist.pure_bind, runtime.application.playerStep_wait,
        FinDist.mem_support_pure] at member
      subst next
      refine ⟨rfl, ?_⟩
      intro observer query
      by_cases same : observer = who
      · subst observer
        simp [stagingCount, submittedAt, stagesEvent]
      · simp [same]
  | wire =>
      simp only [serviceStep, MessageApplication.invoke, MessageApplication.wireEnvironment,
        FinDist.bind_map, FinDist.support_bind, Set.mem_iUnion] at member
      obtain ⟨command, _, step⟩ := member
      apply environmentPolicyStep_quiet runtime execution next
        (command.toEnvironmentCommand runtime.application) _ step
      rw [runtime.application.environmentStep_native]
      have missing id : execution.native.pool.lookup id = none := by
        simp only [MessagePool.lookup, empty, List.find?_nil]
      cases command with
      | wait => rfl
      | deliver who id =>
          simp [WireCommand.toEnvironmentCommand,
            MessageApplication.EnvironmentPolicyCommand.toAction,
            MessageApplication.step, MessagePool.deliver, missing, MessagePool.Result.invalid]
      | «include» id =>
          simp [WireCommand.toEnvironmentCommand,
            MessageApplication.EnvironmentPolicyCommand.toAction,
            MessageApplication.step, runtime.application.includePending_missing _ _ (missing id)]
  | includeLatest selected owner =>
      have absent : runtime.latestEventSubmissionCommand selected owner
          (MessageApplication.State.environmentView runtime.application execution.native) =
            .wait := by
        unfold latestEventSubmissionCommand
        change (match latestEventSubmission? execution.native.pool selected owner with
          | some message => MessageInterface.EnvironmentPolicyCommand.include message.id
          | none => .wait) = _
        unfold latestEventSubmission?
        rw [empty]
        rfl
      change next ∈ (runtime.application.environmentPolicyStep execution
        (runtime.latestEventSubmissionCommand selected owner
          (MessageApplication.State.environmentView runtime.application execution.native))).support
          at member
      rw [absent] at member
      exact environmentPolicyStep_quiet runtime execution next .wait
        (by rw [runtime.application.environmentStep_native]; rfl) member
  | sample selected =>
      have same : selected = event := allowed
      subst selected
      apply environmentPolicyStep_quiet runtime execution next (.application (.executeSample event))
        _ member
      rw [runtime.application.environmentStep_native]
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step]
      change (environmentStep runtime execution.native.application (.executeSample event)).map
        (fun application => ({ execution.native with application } : runtime.application.State)) = _
      rw [environmentStep_executeSample_of_not_ready runtime _ event unready, FinDist.map_pure]
  | grant | tick | expire => contradiction

private theorem runServicePlan_idle (runtime : EventGraphRuntime graph)
    (profile : graph.BehavioralProfile) (wire : runtime.application.WirePolicy)
    (event : graph.EventId) (plan : List (ServiceInstruction graph))
    (execution next : runtime.application.PolicyExecution)
    (allowed : ∀ instruction ∈ plan, IdleInstruction event instruction)
    (grant : execution.native.application.serviceGrant = some event)
    (unready : ¬execution.native.application.config.cut.Ready event)
    (empty : execution.native.pool.pending = [])
    (member : next ∈ (runtime.runServicePlan (runtime.compileProfile profile) wire
      plan execution).support) : Quiet runtime execution next := by
  induction plan generalizing execution with
  | nil =>
      simp only [runServicePlan, FinDist.mem_support_pure] at member
      subst next
      exact .refl runtime execution
  | cons instruction rest ih =>
      simp only [runServicePlan, FinDist.support_bind, Set.mem_iUnion] at member
      obtain ⟨middle, head, tail⟩ := member
      have first := serviceStep_idle runtime profile wire event instruction execution middle
        (allowed instruction List.mem_cons_self) grant unready empty head
      exact first.trans (ih middle
        (fun selected selectedMem => allowed selected (List.mem_cons_of_mem _ selectedMem))
        (by simpa only [first.native] using grant)
        (by simpa only [first.native] using unready)
        (by simpa only [first.native] using empty) tail)

/-- The concrete execution record after a public service grant. -/
def afterGrant (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution) (event : graph.EventId) :
    runtime.application.PolicyExecution :=
  { execution with
    native := { execution.native with
      application := { execution.native.application with serviceGrant := some event } }
    environmentHistory := execution.environmentHistory ++
      [⟨MessageApplication.State.environmentView runtime.application execution.native,
        .application (.grant event)⟩]
    nativeTrace := execution.nativeTrace ++ [.environment (.grant event)] }

theorem serviceStep_grant_eq (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy) (wire : runtime.application.WirePolicy)
    (execution : runtime.application.PolicyExecution) (event : graph.EventId) :
    runtime.serviceStep players wire (.grant event) execution =
      FinDist.pure (runtime.afterGrant execution event) := by
  simp only [serviceStep, MessageApplication.environmentPolicyStep,
    MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.advance,
    MessageApplication.step]
  simp only [application, environmentStep, FinDist.map_pure, FinDist.pure_bind]
  rfl

theorem HonestBoundary.afterGrant {runtime : EventGraphRuntime graph} {inputs : graph.Inputs}
    {execution : runtime.application.PolicyExecution}
    (boundary : HonestBoundary runtime inputs execution) (event : graph.EventId) :
    HonestBoundary runtime inputs (runtime.afterGrant execution event) := by
  apply environmentPolicyStep_honestBoundary runtime inputs execution _ (.grant event) boundary
  change runtime.afterGrant execution event ∈
    (runtime.serviceStep (fun _ _ _ => FinDist.pure .wait)
      (fun _ _ => FinDist.pure .wait) (.grant event) execution).support
  rw [runtime.serviceStep_grant_eq, FinDist.mem_support_pure]

omit [DecidableEq Player] in
private theorem eventServicePlan_tail_idle (roster : List Player) (reactionRounds : Nat)
    (event : graph.EventId) :
    ∀ instruction ∈ (eventServicePlan roster reactionRounds event).tail,
      IdleInstruction event instruction := by
  intro instruction member
  simp only [eventServicePlan, List.cons_append, List.nil_append, List.tail_cons] at member
  cases actor : graph.actor? event <;>
    simp only [actor, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  · rcases member with impossible | rfl
    · contradiction
    rfl
  · rcases member with (head | head) | rfl
    · rcases head with head | head
      · have same := List.eq_of_mem_replicate head
        subst instruction
        trivial
      · simp only [List.mem_flatten] at head
        obtain ⟨round, roundMem, instructionMem⟩ := head
        have same := List.eq_of_mem_replicate roundMem
        subst round
        rcases List.mem_cons.mp instructionMem with rfl | player
        · trivial
        · obtain ⟨who, _, rfl⟩ := List.mem_map.mp player
          trivial
    · subst instruction
      trivial
    · rfl

/-- Visiting an unavailable event neither changes the native graph state nor
consumes staging resources. Wire choices still execute and retain their histories. -/
theorem HonestBoundary.unready_block (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (profile : graph.BehavioralProfile)
    (wire : runtime.application.WirePolicy) (roster : List Player) (reactionRounds : Nat)
    (execution : runtime.application.PolicyExecution)
    (boundary : HonestBoundary runtime inputs execution) (event : graph.EventId)
    (unready : ¬execution.native.application.config.cut.Ready event) :
    (runtime.runServicePlan (runtime.compileProfile profile) wire
        (eventServicePlan roster reactionRounds event) execution).map
          (fun next => next.native.application.config) =
        FinDist.pure execution.native.application.config ∧
      ∀ next ∈ (runtime.runServicePlan (runtime.compileProfile profile) wire
        (eventServicePlan roster reactionRounds event) execution).support,
        HonestBoundary runtime inputs next := by
  have plan : eventServicePlan roster reactionRounds event =
      .grant event :: (eventServicePlan roster reactionRounds event).tail := by
    simp [eventServicePlan]
  rw [plan, runServicePlan, runtime.serviceStep_grant_eq, FinDist.pure_bind]
  have quiet next (member : next ∈ (runtime.runServicePlan (runtime.compileProfile profile)
      wire (eventServicePlan roster reactionRounds event).tail
        (runtime.afterGrant execution event)).support) :
      Quiet runtime (runtime.afterGrant execution event) next :=
    runServicePlan_idle runtime profile wire event _ _ next
      (eventServicePlan_tail_idle roster reactionRounds event) rfl unready
      boundary.pending_empty member
  constructor
  · apply FinDist.eq_pure_of_support_subset_singleton
    intro config member
    rw [FinDist.support_map] at member
    obtain ⟨next, supported, rfl⟩ := member
    change next.native.application.config = execution.native.application.config
    have configEq := congrArg (fun native : runtime.application.State => native.application.config)
      (quiet next supported).native
    exact configEq
  · intro next supported
    exact (quiet next supported).boundary (boundary.afterGrant event)

/-- A ready chance block executes exactly the graph's retained probability
kernel. Grants and message histories do not replace chance with a player choice. -/
theorem HonestBoundary.sample_block (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (profile : graph.BehavioralProfile)
    (wire : runtime.application.WirePolicy) (roster : List Player) (reactionRounds : Nat)
    (execution : runtime.application.PolicyExecution)
    (boundary : HonestBoundary runtime inputs execution) (event : graph.EventId)
    (ready : execution.native.application.config.cut.Ready event)
    (ownerless : graph.actor? event = none)
    (payload : L.Ty) (law : PublicDist graph.layout payload)
    (outputEq : graph.outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .sample payload law)
    (viewNode : nodeView graph event = .sample payload law outputEq codeEq) :
    (runtime.runServicePlan (runtime.compileProfile profile) wire
        (eventServicePlan roster reactionRounds event) execution).map
          (fun next => next.native.application.config) =
        graph.normalizedPolicyStep profile execution.native.application.config event ready ∧
      ∀ next ∈ (runtime.runServicePlan (runtime.compileProfile profile) wire
        (eventServicePlan roster reactionRounds event) execution).support,
        HonestBoundary runtime inputs next := by
  have plan : eventServicePlan roster reactionRounds event = [.grant event, .sample event] := by
    simp [eventServicePlan, ownerless]
  simp only [plan, runServicePlan, runtime.serviceStep_grant_eq, FinDist.pure_bind,
    FinDist.bind_pure]
  let granted := runtime.afterGrant execution event
  have grantedBoundary := boundary.afterGrant event
  constructor
  · change (runtime.application.environmentPolicyStep granted
      (.application (.executeSample event))).map
        (fun next => next.native.application.config) = _
    have nativeLaw := runtime.application.environmentStep_native granted
      (.application (.executeSample event))
    have projected := congrArg (fun measure : FinDist runtime.application.State =>
      measure.map (fun native => native.application.config)) nativeLaw
    simp only [FinDist.map_comp, Function.comp_def] at projected
    rw [projected]
    simp only [MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step]
    change ((environmentStep runtime granted.native.application (.executeSample event)).map
      (fun application => ({ granted.native with application } : runtime.application.State))).map
        (fun native => native.application.config) = _
    rw [environmentStep_executeSample_eq runtime granted.native.application event ready
      payload law outputEq codeEq viewNode, FinDist.map_comp, FinDist.map_comp]
    change (execution.native.application.config.step event ready
      (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)).map id = _
    rw [FinDist.map_id]
    have singleton : Subsingleton (graph.Action event) := by
      change Subsingleton (graph.outputLayout event).Action
      rw [outputEq]
      infer_instance
    unfold normalizedPolicyStep
    split
    · rename_i owner actor
      rw [ownerless] at actor
      contradiction
    · congr 1
      exact @Subsingleton.elim _ singleton _ _
  · intro next member
    exact environmentPolicyStep_honestBoundary runtime inputs granted next
      (.executeSample event) grantedBoundary member

end Vegas.EventGraphRuntime
