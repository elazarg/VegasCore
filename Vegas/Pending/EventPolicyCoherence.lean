/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventPolicyBlock
import Vegas.Pending.EventBindingAcceptance

/-! # Coherence of partially executed prescribed event policies

The three prescribed owner calls need not occur in one clean block: an event
can become ready during reaction traffic after its reserved calls.  The
predicate below therefore describes all partial stages using the actual
authenticated history and private application state.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- History/cache coherence for one prescribed owner and event.  Submission
is allowed only after both private stages, while a positive private stage has
one immutable remembered action. -/
structure PolicyCoherent (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution)
    (owner : Player) (event : graph.EventId) : Prop where
  actor : graph.actor? event = some owner
  stage_le : stagingCount (execution.principalHistory owner) event ≤ 2
  empty_iff :
    stagingCount (execution.principalHistory owner) event = 0 ↔
      execution.native.application.remembered event = none
  cached_of_stage : 0 < stagingCount (execution.principalHistory owner) event →
    ∃ action, execution.native.application.remembered event = some action
  submitted_stage : submittedAt (execution.principalHistory owner) event = true →
    stagingCount (execution.principalHistory owner) event = 2

/-- At the second binding stage the canonical candidate has exactly the typed
meaning of the cached action.  This formulation includes failure: an
unprepared canonical slot has `bindingResult = failure`. -/
def BindingPolicyCoherent (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload) : Prop :=
  PolicyCoherent runtime execution owner event ∧
    (stagingCount (execution.principalHistory owner) event < 2 →
      execution.native.application.candidates.lookup (owner, eventSlot event) = .fresh) ∧
    (stagingCount (execution.principalHistory owner) event = 2 →
      ∀ action, execution.native.application.remembered event = some action →
        execution.native.application.bindingResult (owner, eventSlot event) payload =
          cast (congrArg EventField.Action outputEq) action)

/-- A fresh native execution is coherent at every strategic event. -/
theorem policyCoherent_initial (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (owner : Player) (event : graph.EventId)
    (actor : graph.actor? event = some owner) :
    PolicyCoherent runtime
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial inputs)))
      owner event := by
  refine ⟨actor, ?_, ?_, ?_, ?_⟩ <;>
    simp [stagingCount, submittedAt, State.initial, MessageApplication.State.initial,
      MessageApplication.PolicyExecution.initial]

/-- An authenticated private command by another principal preserves the
owner's partial prescribed stage. -/
theorem PolicyCoherent.afterPrivate_other
    (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution)
    (owner other : Player) (event : graph.EventId)
    (coherent : PolicyCoherent runtime execution owner event)
    (different : owner ≠ other) (command : PrivateCommand graph) :
    PolicyCoherent runtime (runtime.application.afterPrivate execution other command)
      owner event := by
  have history :
      (runtime.application.afterPrivate execution other command).principalHistory owner =
        execution.principalHistory owner := by
    simp [MessageApplication.afterPrivate, different]
  have observation := privateStep_playerView_other
    execution.native.application other owner different command
  have remembered :
      (runtime.application.afterPrivate execution other command).native.application.remembered
          event = execution.native.application.remembered event := by
    have memory := congrArg (fun view => view.remembered event) observation
    change (privateStep execution.native.application other command).remembered event = _
    simpa [State.playerView, coherent.actor] using memory
  refine ⟨coherent.actor, ?_, ?_, ?_, ?_⟩
  · simpa only [history] using coherent.stage_le
  · simpa only [history, remembered] using coherent.empty_iff
  · simpa only [history, remembered] using coherent.cached_of_stage
  · simpa only [history] using coherent.submitted_stage

/-- The first prescribed call advances a coherent empty event to stage one
and installs exactly the sampled action. -/
theorem PolicyCoherent.afterRemember
    (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution)
    (owner : Player) (event : graph.EventId)
    (coherent : PolicyCoherent runtime execution owner event)
    (stage : stagingCount (execution.principalHistory owner) event = 0)
    (action : graph.Action event) :
    PolicyCoherent runtime
      (runtime.application.afterPrivate execution owner (.remember event action))
      owner event := by
  have empty := coherent.empty_iff.mp stage
  have remembered := runtime.afterPrivate_remembered_same execution owner event action
    coherent.actor empty
  have history := runtime.afterPrivate_history_self execution owner (.remember event action)
  have count : stagingCount
      ((runtime.application.afterPrivate execution owner
        (.remember event action)).principalHistory owner) event = 1 := by
    rw [history, stagingCount_append_remember, stage]
  have notSubmitted := runtime.submittedAt_afterPrivate execution owner
    (.remember event action) event
  refine ⟨coherent.actor, by omega, ?_, ?_, ?_⟩
  · constructor
    · omega
    · intro impossible
      rw [remembered] at impossible
      contradiction
  · intro _
    exact ⟨action, remembered⟩
  · intro submitted
    rw [notSubmitted] at submitted
    have prior := coherent.submitted_stage submitted
    omega

/-- Initial binding events satisfy the stronger candidate/cache clause
vacuously, since their prescribed stage is zero. -/
theorem bindingPolicyCoherent_initial (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (owner : Player) (event : graph.EventId)
    (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (actor : graph.actor? event = some owner) :
    BindingPolicyCoherent runtime
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial inputs)))
      owner event payload outputEq := by
  refine ⟨policyCoherent_initial runtime inputs owner event actor, ?_, ?_⟩
  · intro _
    rfl
  · simp [stagingCount, MessageApplication.PolicyExecution.initial]

/-- Private work by another principal cannot alter either the prescribed
owner's cache/history phase or its canonical candidate meaning. -/
theorem bindingPolicyCoherent_afterPrivate_other
    (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution)
    (owner other : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (coherent : BindingPolicyCoherent runtime execution owner event payload outputEq)
    (different : owner ≠ other) (command : PrivateCommand graph) :
    BindingPolicyCoherent runtime
      (runtime.application.afterPrivate execution other command)
      owner event payload outputEq := by
  have history :
      (runtime.application.afterPrivate execution other command).principalHistory owner =
        execution.principalHistory owner := by
    simp [MessageApplication.afterPrivate, different]
  have observation := privateStep_playerView_other
    execution.native.application other owner different command
  have candidate :
      ((runtime.application.afterPrivate execution other command).native.application.candidates
          ).lookup (owner, eventSlot event) =
        execution.native.application.candidates.lookup (owner, eventSlot event) := by
    have lookup := congrArg (fun view => view.candidates (eventSlot event)) observation
    change (privateStep execution.native.application other command).candidates.lookup
      (owner, eventSlot event) = _
    simpa [State.playerView] using lookup
  refine ⟨coherent.1.afterPrivate_other runtime execution owner other event different command,
    ?_, ?_⟩
  · intro stage
    rw [candidate]
    apply coherent.2.1
    simpa only [history] using stage
  intro stage action remembered
  have priorStage : stagingCount (execution.principalHistory owner) event = 2 := by
    simpa only [history] using stage
  have priorRemembered : execution.native.application.remembered event = some action := by
    have memory := congrArg (fun view => view.remembered event) observation
    have actor := coherent.1.actor
    have rawMemory :
        (privateStep execution.native.application other command).remembered event =
          execution.native.application.remembered event := by
      simpa [State.playerView, actor] using memory
    change (privateStep execution.native.application other command).remembered event =
      some action at remembered
    have prior : execution.native.application.remembered event = some action :=
      rawMemory.symm.trans remembered
    exact prior
  have prior := coherent.2.2 priorStage action priorRemembered
  unfold State.bindingResult at prior ⊢
  rw [candidate]
  exact prior

/-- The second resolution call repeats the cached action.  First-write memory
keeps the action immutable while the authenticated history advances to stage
two. -/
theorem PolicyCoherent.afterResolveStage
    (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution)
    (owner : Player) (event : graph.EventId)
    (coherent : PolicyCoherent runtime execution owner event)
    (stage : stagingCount (execution.principalHistory owner) event = 1)
    (action : graph.Action event)
    (cached : execution.native.application.remembered event = some action) :
    PolicyCoherent runtime
      (runtime.application.afterPrivate execution owner (.remember event action))
      owner event := by
  have history := runtime.afterPrivate_history_self execution owner (.remember event action)
  have count : stagingCount
      ((runtime.application.afterPrivate execution owner
        (.remember event action)).principalHistory owner) event = 2 := by
    rw [history, stagingCount_append_remember, stage]
  have memory :
      (runtime.application.afterPrivate execution owner
        (.remember event action)).native.application.remembered event = some action := by
    change (privateStep execution.native.application owner
      (.remember event action)).remembered event = some action
    simp [privateStep, coherent.actor, cached]
  have notSubmitted := runtime.submittedAt_afterPrivate execution owner
    (.remember event action) event
  refine ⟨coherent.actor, by omega, ?_, ?_, ?_⟩
  · constructor
    · omega
    · intro impossible
      rw [memory] at impossible
      contradiction
  · intro _
    exact ⟨action, memory⟩
  · intro submitted
    exact count

/-- The second binding call establishes both stage-two cache coherence and the
canonical candidate meaning.  The premise is freshness at stage one, before
the prescribed preparation command. -/
theorem BindingPolicyCoherent.afterBindingStage
    (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (coherent : BindingPolicyCoherent runtime execution owner event payload outputEq)
    (stage : stagingCount (execution.principalHistory owner) event = 1)
    (action : graph.Action event)
    (cached : execution.native.application.remembered event = some action)
    (command : PrivateCommand graph)
    (commandEq : runtime.bindingStageCommand event payload outputEq action =
      .privateCommand command) :
    BindingPolicyCoherent runtime
      (runtime.application.afterPrivate execution owner command)
      owner event payload outputEq := by
  have fresh : execution.native.application.candidates.lookup
      (owner, eventSlot event) = .fresh := coherent.2.1 (by omega)
  have history := runtime.afterPrivate_history_self execution owner command
  have count : stagingCount
      ((runtime.application.afterPrivate execution owner command).principalHistory owner)
        event = 2 := by
    rw [history]
    have appended := runtime.stagingCount_append_bindingStageCommand
      (execution.principalHistory owner)
      (MessageApplication.State.observe runtime.application execution.native owner)
      event payload outputEq action
    rw [commandEq] at appended
    simpa [stage] using appended
  have memory :
      (runtime.application.afterPrivate execution owner command).native.application.remembered
          event = some action := by
    change (privateStep execution.native.application owner command).remembered event = some action
    unfold bindingStageCommand at commandEq
    generalize resultEq : cast (congrArg EventField.Action outputEq) action = result at commandEq
    cases result with
    | failure =>
        have same : PrivateCommand.remember event action = command := by
          injection commandEq
        subst command
        simp [privateStep, coherent.1.actor, cached]
    | success value =>
        have same : PrivateCommand.prepare event.val ⟨payload, value⟩ = command := by
          injection commandEq
        subst command
        simp [privateStep, cached]
  have notSubmitted := runtime.submittedAt_afterPrivate execution owner command event
  have base : PolicyCoherent runtime
      (runtime.application.afterPrivate execution owner command) owner event := by
    refine ⟨coherent.1.actor, by omega, ?_, ?_, ?_⟩
    · constructor
      · omega
      · intro impossible
        rw [memory] at impossible
        contradiction
    · intro _
      exact ⟨action, memory⟩
    · intro _
      exact count
  refine ⟨base, ?_, ?_⟩
  · intro impossible
    omega
  intro _ selected selectedCache
  have selectedEq : selected = action := by
    rw [memory] at selectedCache
    exact Option.some.inj selectedCache.symm
  subst selected
  change (privateStep execution.native.application owner command).bindingResult
    (owner, eventSlot event) payload = _
  exact runtime.bindingStageCommand_result execution.native.application owner event payload
    outputEq action command commandEq fresh

/-- The third prescribed call records an addressed submission without
changing the application cache or candidate catalogue. -/
theorem PolicyCoherent.afterSubmit
    (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution)
    (owner : Player) (event : graph.EventId)
    (coherent : PolicyCoherent runtime execution owner event)
    (stage : stagingCount (execution.principalHistory owner) event = 2)
    (payload : Payload graph) (addressed : payload.event? graph = some event) :
    PolicyCoherent runtime (runtime.application.afterSubmit execution owner payload)
      owner event := by
  have history := runtime.afterSubmit_history_self execution owner payload
  have count : stagingCount
      ((runtime.application.afterSubmit execution owner payload).principalHistory owner)
        event = 2 := by
    rw [history]
    simpa [stagingCount, stagesEvent] using stage
  have submitted : submittedAt
      ((runtime.application.afterSubmit execution owner payload).principalHistory owner)
        event = true := by
    rw [history, submittedAt_append_submit, addressed]
    simp
  refine ⟨coherent.actor, by omega, ?_, ?_, ?_⟩
  · simpa only [count, Nat.reduceEqDiff, false_iff] using
      (show (runtime.application.afterSubmit execution owner payload).native.application.remembered
          event ≠ none from by
        have positive : 0 < stagingCount (execution.principalHistory owner) event := by omega
        obtain ⟨action, cached⟩ := coherent.cached_of_stage positive
        simp [MessageApplication.afterSubmit, cached])
  · intro _
    have positive : 0 < stagingCount (execution.principalHistory owner) event := by omega
    obtain ⟨action, cached⟩ := coherent.cached_of_stage positive
    exact ⟨action, by simpa [MessageApplication.afterSubmit] using cached⟩
  · intro _
    exact count

/-- A private command by the same owner preserves every event it neither
stages nor mutates in the remembered table.  This is the frame used for all
owned events other than the current service grant. -/
theorem PolicyCoherent.afterPrivate_irrelevant
    (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution)
    (owner : Player) (event : graph.EventId)
    (coherent : PolicyCoherent runtime execution owner event)
    (command : PrivateCommand graph)
    (notStage : stagesEvent (runtime := runtime) event (.privateCommand command) = false)
    (memory : (privateStep execution.native.application owner command).remembered event =
      execution.native.application.remembered event) :
    PolicyCoherent runtime (runtime.application.afterPrivate execution owner command)
      owner event := by
  have history := runtime.afterPrivate_history_self execution owner command
  have count : stagingCount
      ((runtime.application.afterPrivate execution owner command).principalHistory owner) event =
        stagingCount (execution.principalHistory owner) event := by
    rw [history]
    simp [stagingCount, notStage]
  refine ⟨coherent.actor, ?_, ?_, ?_, ?_⟩
  · simpa only [count] using coherent.stage_le
  · change _ = 0 ↔ (privateStep execution.native.application owner command).remembered
      event = none
    simpa only [count, memory] using coherent.empty_iff
  · change 0 < _ → ∃ action,
      (privateStep execution.native.application owner command).remembered event = some action
    simpa only [count, memory] using coherent.cached_of_stage
  · have submitted := runtime.submittedAt_afterPrivate execution owner command event
    rw [submitted, count]
    exact coherent.submitted_stage

/-- A submission for another address is a history-only frame for this event. -/
theorem PolicyCoherent.afterSubmit_other
    (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution)
    (owner : Player) (event : graph.EventId)
    (coherent : PolicyCoherent runtime execution owner event)
    (payload : Payload graph) (other : payload.event? graph ≠ some event) :
    PolicyCoherent runtime (runtime.application.afterSubmit execution owner payload)
      owner event := by
  have history := runtime.afterSubmit_history_self execution owner payload
  have count : stagingCount
      ((runtime.application.afterSubmit execution owner payload).principalHistory owner) event =
        stagingCount (execution.principalHistory owner) event := by
    rw [history]
    simp [stagingCount, stagesEvent]
  have submitted : submittedAt
      ((runtime.application.afterSubmit execution owner payload).principalHistory owner) event =
        submittedAt (execution.principalHistory owner) event := by
    rw [history, submittedAt_append_submit]
    simp [other]
  refine ⟨coherent.actor, ?_, ?_, ?_, ?_⟩
  · simpa only [count] using coherent.stage_le
  · rw [count]
    simpa [MessageApplication.afterSubmit] using coherent.empty_iff
  · rw [count]
    simpa [MessageApplication.afterSubmit] using coherent.cached_of_stage
  · rw [submitted, count]
    exact coherent.submitted_stage

/-- Addressed submission preserves the completed binding-stage meaning. -/
theorem BindingPolicyCoherent.afterSubmit
    (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution)
    (owner : Player) (event : graph.EventId) (bindingPayload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner bindingPayload)
    (coherent : BindingPolicyCoherent runtime execution owner event bindingPayload outputEq)
    (stage : stagingCount (execution.principalHistory owner) event = 2)
    (packet : Payload graph) (addressed : packet.event? graph = some event) :
    BindingPolicyCoherent runtime
      (runtime.application.afterSubmit execution owner packet)
      owner event bindingPayload outputEq := by
  refine ⟨coherent.1.afterSubmit runtime execution owner event stage packet addressed,
    ?_, ?_⟩
  · intro impossible
    have history := runtime.afterSubmit_history_self execution owner packet
    have count : stagingCount
        ((runtime.application.afterSubmit execution owner packet).principalHistory owner) event =
          2 := by
      rw [history]
      simpa [stagingCount, stagesEvent] using stage
    omega
  · intro _ action cached
    have cachedBefore : execution.native.application.remembered event = some action := by
      simpa [MessageApplication.afterSubmit] using cached
    have meaning := coherent.2.2 stage action cachedBefore
    simpa [MessageApplication.afterSubmit] using meaning

/-- Simultaneous coherence of all events owned by one prescribed player. -/
def PolicyCoherentAll (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution) (owner : Player) : Prop :=
  ∀ event, graph.actor? event = some owner →
    PolicyCoherent runtime execution owner event

theorem PolicyCoherent.afterWait
    (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution)
    (owner : Player) (event : graph.EventId)
    (coherent : PolicyCoherent runtime execution owner event) :
    PolicyCoherent runtime
      { execution with principalHistory := fun other =>
          if other = owner then execution.principalHistory owner ++
            [⟨MessageApplication.State.observe runtime.application execution.native owner,
              .wait⟩]
          else execution.principalHistory other }
      owner event := by
  have history : (if owner = owner then execution.principalHistory owner ++
      [⟨MessageApplication.State.observe runtime.application execution.native owner, .wait⟩]
    else execution.principalHistory owner) = execution.principalHistory owner ++
      [⟨MessageApplication.State.observe runtime.application execution.native owner, .wait⟩] := by
    simp
  refine ⟨coherent.actor, ?_, ?_, ?_, ?_⟩
  · simpa [history, stagingCount, stagesEvent] using coherent.stage_le
  · simpa [history, stagingCount, stagesEvent] using coherent.empty_iff
  · simpa [history, stagingCount, stagesEvent] using coherent.cached_of_stage
  · simpa [history, stagingCount, stagesEvent, submittedAt] using coherent.submitted_stage

theorem policyCoherentAll_initial (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (owner : Player) :
    PolicyCoherentAll runtime
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial inputs))) owner := by
  intro event actor
  exact policyCoherent_initial runtime inputs owner event actor

def CommandAt (runtime : EventGraphRuntime graph) (event : graph.EventId)
    (command : Command runtime) : Prop :=
  command = .wait ∨ stagesEvent event command = true ∨
    ∃ packet, command = .submit packet ∧ packet.event? graph = some event

@[simp] theorem stagesEvent_bindingStageCommand
    (runtime : EventGraphRuntime graph) (event : graph.EventId)
    (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (action : graph.Action event) :
    stagesEvent event (runtime.bindingStageCommand event payload outputEq action) = true := by
  unfold bindingStageCommand
  generalize cast (congrArg EventField.Action outputEq) action = result
  cases result <;> simp [stagesEvent]

@[simp] theorem resolutionPayload_event
    (runtime : EventGraphRuntime graph) (owner who : Player) (event : graph.EventId)
    (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (action : graph.Action event) (view : runtime.application.View) :
    (runtime.resolutionPayload who event payload binding checks outputEq action view).event?
      graph = some event := by
  obtain ⟨packet, commandEq, address⟩ := runtime.resolutionSubmission_address who event
    payload binding checks outputEq action view
  have packetEq : runtime.resolutionPayload who event payload binding checks outputEq action
      view = packet := by
    exact MessageInterface.PlayerCommand.submit.inj commandEq
  simpa only [packetEq] using address

theorem compilePlayerPolicy_commandAt
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (history : List (Entry runtime)) (view : runtime.application.View)
    (event : graph.EventId)
    (grant : view.application.publicView.serviceGrant = some event)
    (command : Command runtime)
    (member : command ∈ (runtime.compilePlayerPolicy owner policy history view).support) :
    runtime.CommandAt event command := by
  unfold compilePlayerPolicy at member
  rw [grant] at member
  repeat' first | split at member
  all_goals subst_vars
  all_goals
    simp_all only [CommandAt, stagesEvent, resolutionSubmission,
      FinDist.mem_support_pure, FinDist.support_map, Set.mem_image, decide_eq_true_eq,
      Bool.false_eq_true, reduceCtorEq, Option.some.injEq]
  all_goals subst_vars
  all_goals try {
    exact Or.inr (Or.inl (stagesEvent_bindingStageCommand _ _ _ _ _ _)) }
  all_goals try { simp [Payload.event?] }
  all_goals aesop

/-- A supported compiled private command cannot occur after the two private
stages, and a preparation command occurs exactly at stage one. -/
theorem compilePlayerPolicy_private_stage
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (history : List (Entry runtime)) (view : runtime.application.View)
    (command : PrivateCommand graph)
    (member : (.privateCommand command : Command runtime) ∈
      (runtime.compilePlayerPolicy owner policy history view).support) :
    ∃ event, view.application.publicView.serviceGrant = some event ∧
      stagingCount history event < 2 ∧
      stagesEvent event (.privateCommand command : Command runtime) = true := by
  unfold compilePlayerPolicy at member
  repeat' first | split at member
  all_goals subst_vars
  all_goals
    simp_all only [FinDist.mem_support_pure, FinDist.support_map, Set.mem_image,
      MessageInterface.PlayerCommand.privateCommand.injEq, reduceCtorEq,
      Option.some.injEq]
  all_goals try {
    exact ⟨_, rfl, by omega, stagesEvent_bindingStageCommand _ _ _ _ _ _⟩ }
  all_goals simp [stagesEvent, resolutionSubmission] at *
  all_goals aesop

/-- A private command that stages one event leaves the remembered action of
every distinct event unchanged. -/
theorem privateStep_remembered_other_of_stagesEvent
    (runtime : EventGraphRuntime graph) (state : State graph) (owner : Player)
    (event query : graph.EventId) (command : PrivateCommand graph)
    (actor : graph.actor? event = some owner) (different : query ≠ event)
    (staged : stagesEvent (runtime := runtime) event (.privateCommand command) = true) :
    (privateStep state owner command).remembered query = state.remembered query := by
  cases command with
  | prepare serial raw => rfl
  | remember remembered action =>
      simp only [stagesEvent, decide_eq_true_eq] at staged
      subst remembered
      cases cached : state.remembered event <;>
        simp [privateStep, actor, cached, Function.update, different]

/-- A private command cannot stage two distinct events. -/
theorem stagesEvent_other_of_stagesEvent
    (runtime : EventGraphRuntime graph) (event query : graph.EventId)
    (command : PrivateCommand graph) (different : query ≠ event)
    (staged : stagesEvent (runtime := runtime) event (.privateCommand command) = true) :
    stagesEvent (runtime := runtime) query (.privateCommand command) = false := by
  cases command with
  | remember remembered action =>
      simp only [stagesEvent, decide_eq_true_eq] at staged
      subst remembered
      simp [stagesEvent, different.symm]
  | prepare serial raw =>
      simp only [stagesEvent, decide_eq_true_eq] at staged
      subst serial
      simp only [stagesEvent, decide_eq_false_iff_not]
      intro same
      exact different (Fin.ext same.symm)

/-- At private stage zero, every supported compiled private command is the
remember command carrying the freshly sampled action for the granted event. -/
theorem compilePlayerPolicy_private_zero_is_remember
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (execution : runtime.application.PolicyExecution)
    (event : graph.EventId)
    (grant : execution.native.application.serviceGrant = some event)
    (stage : stagingCount (execution.principalHistory owner) event = 0)
    (command : PrivateCommand graph)
    (member : (.privateCommand command : Command runtime) ∈
      (runtime.compilePlayerPolicy owner policy (execution.principalHistory owner)
        (MessageApplication.State.observe runtime.application execution.native owner)).support) :
    ∃ action, command = .remember event action := by
  have observedGrant :
      (MessageApplication.State.observe runtime.application execution.native
        owner).application.publicView.serviceGrant = some event := by
    change execution.native.application.serviceGrant = some event
    exact grant
  unfold compilePlayerPolicy at member
  rw [observedGrant] at member
  repeat' first | split at member
  all_goals
    simp_all only [FinDist.mem_support_pure, FinDist.support_map, Set.mem_image,
      MessageInterface.PlayerCommand.privateCommand.injEq,
      reduceCtorEq, Option.some.injEq]
  all_goals aesop

@[simp] theorem bindingStageCommand_ne_submit
    (runtime : EventGraphRuntime graph) (event : graph.EventId)
    (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (action : graph.Action event) (packet : Payload graph) :
    runtime.bindingStageCommand event payload outputEq action ≠ .submit packet := by
  obtain ⟨command, commandEq⟩ :=
    runtime.bindingStageCommand_is_private event payload outputEq action
  rw [commandEq]
  simp

@[simp] theorem submit_ne_bindingStageCommand
    (runtime : EventGraphRuntime graph) (event : graph.EventId)
    (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (action : graph.Action event) (packet : Payload graph) :
    (.submit packet : Command runtime) ≠
      runtime.bindingStageCommand event payload outputEq action :=
  (runtime.bindingStageCommand_ne_submit event owner payload outputEq action packet).symm

/-- A supported compiled submission occurs only after both private stages of
the granted event. -/
theorem compilePlayerPolicy_submit_stage
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (execution : runtime.application.PolicyExecution)
    (event : graph.EventId)
    (grant : execution.native.application.serviceGrant = some event)
    (packet : Payload graph)
    (member : (.submit packet : Command runtime) ∈
      (runtime.compilePlayerPolicy owner policy (execution.principalHistory owner)
        (MessageApplication.State.observe runtime.application execution.native owner)).support) :
    2 ≤ stagingCount (execution.principalHistory owner) event := by
  have observedGrant :
      (MessageApplication.State.observe runtime.application execution.native
        owner).application.publicView.serviceGrant = some event := by
    change execution.native.application.serviceGrant = some event
    exact grant
  unfold compilePlayerPolicy at member
  rw [observedGrant] at member
  generalize countEq : stagingCount (execution.principalHistory owner) event = count at member
  repeat' first | split at member
  all_goals subst_vars
  all_goals
    simp_all only [FinDist.mem_support_pure, FinDist.support_map, Set.mem_image,
      reduceCtorEq, MessageInterface.PlayerCommand.submit.injEq, Option.some.injEq,
      submit_ne_bindingStageCommand]
  all_goals first
    | omega
    | (rcases member with ⟨_, _, impossible⟩; contradiction)

/-- Any non-wait command supported by the compiled policy at a grant is
authenticated to the graph actor of that granted event. -/
theorem compilePlayerPolicy_nonwait_actor
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (history : List (Entry runtime)) (view : runtime.application.View)
    (event : graph.EventId)
    (grant : view.application.publicView.serviceGrant = some event)
    (command : Command runtime) (notWait : command ≠ .wait)
    (member : command ∈ (runtime.compilePlayerPolicy owner policy history view).support) :
    graph.actor? event = some owner := by
  unfold compilePlayerPolicy at member
  rw [grant] at member
  repeat' first | split at member
  all_goals subst_vars
  all_goals
    simp_all only [FinDist.mem_support_pure, FinDist.support_map, Set.mem_image,
      reduceCtorEq, Option.some.injEq]

/-- At stage one, any private command that stages the granted event advances
to stage two while retaining the already immutable cached action. -/
theorem PolicyCoherent.afterPrivate_stageOne
    (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution)
    (owner : Player) (event : graph.EventId)
    (coherent : PolicyCoherent runtime execution owner event)
    (stage : stagingCount (execution.principalHistory owner) event = 1)
    (command : PrivateCommand graph)
    (staged : stagesEvent (runtime := runtime) event (.privateCommand command) = true) :
    PolicyCoherent runtime (runtime.application.afterPrivate execution owner command)
      owner event := by
  obtain ⟨action, cached⟩ := coherent.cached_of_stage (by omega)
  have history := runtime.afterPrivate_history_self execution owner command
  have count : stagingCount
      ((runtime.application.afterPrivate execution owner command).principalHistory owner) event =
        2 := by
    rw [history]
    calc
      stagingCount (execution.principalHistory owner ++
          [⟨MessageApplication.State.observe runtime.application execution.native owner,
            .privateCommand command⟩]) event =
          stagingCount (execution.principalHistory owner) event + 1 := by
            simp [stagingCount, staged]
      _ = 2 := by omega
  have memory :
      (runtime.application.afterPrivate execution owner command).native.application.remembered
          event = some action := by
    change (privateStep execution.native.application owner command).remembered event = some action
    cases command with
    | prepare serial raw => exact cached
    | remember remembered selected =>
        simp only [stagesEvent, decide_eq_true_eq] at staged
        subst remembered
        simp [privateStep, coherent.actor, cached]
  refine ⟨coherent.actor, by omega, ?_, ?_, ?_⟩
  · constructor
    · omega
    · intro impossible
      rw [memory] at impossible
      contradiction
  · exact fun _ => ⟨action, memory⟩
  · intro _
    exact count

/-- One actual supported player transition under the compiled owner policy
preserves simultaneous coherence of every event owned by that player. -/
theorem compilePlayerPolicy_playerStep_policyCoherentAll
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (execution next : runtime.application.PolicyExecution)
    (event : graph.EventId)
    (grant : execution.native.application.serviceGrant = some event)
    (coherent : PolicyCoherentAll runtime execution owner)
    (command : Command runtime)
    (commandMem : command ∈
      (runtime.compilePlayerPolicy owner policy (execution.principalHistory owner)
        (MessageApplication.State.observe runtime.application execution.native owner)).support)
    (stepMem : next ∈ (runtime.application.playerStep owner execution command).support) :
    PolicyCoherentAll runtime next owner := by
  have atEvent := runtime.compilePlayerPolicy_commandAt owner policy
    (execution.principalHistory owner)
    (MessageApplication.State.observe runtime.application execution.native owner)
    event (by
      change execution.native.application.serviceGrant = some event
      exact grant) command commandMem
  cases command with
  | wait =>
      simp only [MessageApplication.playerStep, MessageApplication.PlayerCommand.toAction,
        MessageApplication.advance, FinDist.pure_bind, FinDist.mem_support_pure] at stepMem
      subst next
      intro query actor
      exact (coherent query actor).afterWait runtime execution owner query
  | replay id =>
      simp [CommandAt, stagesEvent] at atEvent
  | privateCommand privateCommand =>
      rw [runtime.application.playerStep_private_eq] at stepMem
      simp only [FinDist.mem_support_pure] at stepMem
      subst next
      obtain ⟨stagedEvent, stagedGrant, stageLt, staged⟩ :=
        runtime.compilePlayerPolicy_private_stage owner policy
          (execution.principalHistory owner)
          (MessageApplication.State.observe runtime.application execution.native owner)
          privateCommand commandMem
      have stagedEq : stagedEvent = event := by
        change execution.native.application.serviceGrant = some stagedEvent at stagedGrant
        rw [grant] at stagedGrant
        exact Option.some.inj stagedGrant.symm
      subst stagedEvent
      have eventActor : graph.actor? event = some owner :=
        runtime.compilePlayerPolicy_nonwait_actor owner policy
          (execution.principalHistory owner)
          (MessageApplication.State.observe runtime.application execution.native owner)
          event (by
            change execution.native.application.serviceGrant = some event
            exact grant) (.privateCommand privateCommand) (by simp) commandMem
      have current := coherent event eventActor
      have currentAfter : PolicyCoherent runtime
          (runtime.application.afterPrivate execution owner privateCommand) owner event := by
        rcases Nat.eq_zero_or_pos
            (stagingCount (execution.principalHistory owner) event) with stageZero | stagePositive
        · obtain ⟨action, commandEq⟩ :=
            runtime.compilePlayerPolicy_private_zero_is_remember owner policy execution event
              grant stageZero privateCommand commandMem
          subst privateCommand
          exact current.afterRemember runtime execution owner event stageZero action
        · have stageOne : stagingCount (execution.principalHistory owner) event = 1 := by
            omega
          exact current.afterPrivate_stageOne runtime execution owner event stageOne
            privateCommand staged
      intro query queryActor
      by_cases same : query = event
      · subst query
        exact currentAfter
      · apply (coherent query queryActor).afterPrivate_irrelevant runtime execution owner query
          privateCommand
        · exact runtime.stagesEvent_other_of_stagesEvent event query privateCommand same staged
        · exact runtime.privateStep_remembered_other_of_stagesEvent
            execution.native.application owner event query privateCommand eventActor same staged
  | submit packet =>
      rw [runtime.application.playerStep_submit_eq] at stepMem
      simp only [FinDist.mem_support_pure] at stepMem
      subst next
      have eventActor : graph.actor? event = some owner :=
        runtime.compilePlayerPolicy_nonwait_actor owner policy
          (execution.principalHistory owner)
          (MessageApplication.State.observe runtime.application execution.native owner)
          event (by
            change execution.native.application.serviceGrant = some event
            exact grant) (.submit packet) (by simp) commandMem
      have stageGe := runtime.compilePlayerPolicy_submit_stage owner policy execution event
        grant packet commandMem
      have stage : stagingCount (execution.principalHistory owner) event = 2 := by
        have stageLe := (coherent event eventActor).stage_le
        omega
      rcases atEvent with wait | staged | addressed
      · contradiction
      · simp [stagesEvent] at staged
      · obtain ⟨addressedPacket, packetEq, packetAddress⟩ := addressed
        injection packetEq with packetEq
        subst addressedPacket
        intro query queryActor
        by_cases same : query = event
        · subst query
          exact (coherent event eventActor).afterSubmit runtime execution owner event stage
            packet packetAddress
        · apply (coherent query queryActor).afterSubmit_other runtime execution owner query
            packet
          intro queryAddress
          rw [packetAddress] at queryAddress
          exact same (Option.some.inj queryAddress.symm)

/-- An actual supported invocation of the compiled owner policy preserves
coherence of all of that owner's strategic events. -/
theorem compilePlayerPolicy_invoke_policyCoherentAll
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (execution next : runtime.application.PolicyExecution)
    (event : graph.EventId)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy owner policy)
    (grant : execution.native.application.serviceGrant = some event)
    (coherent : PolicyCoherentAll runtime execution owner)
    (supported : next ∈
      (runtime.application.invoke players environment execution (.player owner)).support) :
    PolicyCoherentAll runtime next owner := by
  simp only [MessageApplication.invoke, ownerCompiled, FinDist.support_bind,
    Set.mem_iUnion] at supported
  obtain ⟨command, commandMem, stepMem⟩ := supported
  exact runtime.compilePlayerPolicy_playerStep_policyCoherentAll owner policy execution next
    event grant coherent command commandMem stepMem

end Vegas.EventGraphRuntime
