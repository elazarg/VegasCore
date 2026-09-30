/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventPrescribedBoundary
import Vegas.Pending.EventServiceGrant

/-! # Completion of submissions first made during a service visit -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- A first submission recorded during a finite plan has a concrete crossing
step, with supported executions on both sides. -/
theorem runServicePlan_first_submission (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (plan : List (ServiceInstruction graph))
    (before after : runtime.application.PolicyExecution) (owner : Player) (event : graph.EventId)
    (notSubmitted : submittedAt (before.principalHistory owner) event = false)
    (submitted : submittedAt (after.principalHistory owner) event = true)
    (member : after ∈ (runtime.runServicePlan players wire plan before).support) :
    ∃ (priorPlan : List (ServiceInstruction graph)) (instruction : ServiceInstruction graph)
        (remaining : List (ServiceInstruction graph))
        (prior next : runtime.application.PolicyExecution),
      plan = priorPlan ++ instruction :: remaining ∧
      prior ∈ (runtime.runServicePlan players wire priorPlan before).support ∧
      submittedAt (prior.principalHistory owner) event = false ∧
      next ∈ (runtime.serviceStep players wire instruction prior).support ∧
      submittedAt (next.principalHistory owner) event = true ∧
      after ∈ (runtime.runServicePlan players wire remaining next).support := by
  induction plan generalizing before with
  | nil =>
      simp only [runServicePlan, PMF.mem_support_pure_iff _ _] at member
      subst after
      rw [notSubmitted] at submitted
      contradiction
  | cons instruction rest ih =>
      simp only [runServicePlan, PMF.support_bind, Set.mem_iUnion] at member
      obtain ⟨middle, first, tail⟩ := member
      cases recorded : submittedAt (middle.principalHistory owner) event with
      | true =>
          exact ⟨[], instruction, rest, before, middle, rfl,
            by simp [runServicePlan], notSubmitted, first, recorded, tail⟩
      | false =>
          obtain ⟨priorPlan, crossing, remaining, prior, next, split, priorMem,
              priorFalse, nextMem, nextTrue, tailMem⟩ := ih middle recorded tail
          refine ⟨instruction :: priorPlan, crossing, remaining, prior, next,
            by simp only [List.cons_append, split], ?_, priorFalse, nextMem, nextTrue, tailMem⟩
          simp only [runServicePlan, PMF.support_bind, Set.mem_iUnion]
          exact ⟨middle, first, priorMem⟩

/-- The compiled owner records a new event submission only while that event
is ready; a player submission itself does not advance the graph. -/
theorem serviceStep_new_submission_ready (runtime : EventGraphRuntime graph)
    (owner : Player) (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (before after : runtime.application.PolicyExecution) (event : graph.EventId)
    (notSubmitted : submittedAt (before.principalHistory owner) event = false)
    (submitted : submittedAt (after.principalHistory owner) event = true)
    (member : after ∈ (runtime.serviceStep players wire instruction before).support) :
    after.native.application.config.cut.Ready event := by
  have impossible (histories : after.principalHistory owner = before.principalHistory owner) :
      False := by
    rw [histories, notSubmitted] at submitted
    contradiction
  cases instruction with
  | player who =>
      simp only [serviceStep, MessageApplication.invoke, PMF.support_bind,
        Set.mem_iUnion] at member
      obtain ⟨command, chosen, step⟩ := member
      by_cases same : who = owner
      · subst who
        rw [prescribed] at chosen
        have history := runtime.application.playerStep_history_self owner before command after step
        rw [history] at submitted
        cases command with
        | privateCommand command | wait | replay id =>
            simp only [submittedAt, List.any_append, List.any_cons, List.any_nil,
              Bool.or_false] at submitted
            change submittedAt (before.principalHistory owner) event = true at submitted
            rw [notSubmitted] at submitted
            contradiction
        | submit packet =>
            have addressed : packet.event? graph = some event := by
              simp only [submittedAt, List.any_append, List.any_cons, List.any_nil,
                Bool.or_false] at submitted
              change (submittedAt (before.principalHistory owner) event ||
                decide (packet.event? graph = some event)) = true at submitted
              rw [notSubmitted, Bool.false_or, decide_eq_true_eq] at submitted
              exact submitted
            have turn := runtime.compilePlayerPolicy_submit_turn owner policy
              (before.principalHistory owner)
              (MessageApplication.State.observe runtime.application before.native owner)
              packet event chosen addressed
            have ready := (runtime.compilePlayerPolicy_submit_ready_notSubmitted owner policy
              (before.principalHistory owner)
              (MessageApplication.State.observe runtime.application before.native owner)
              event packet turn chosen).1
            rw [runtime.application.playerStep_submit_eq, PMF.mem_support_pure_iff _ _] at step
            subst after
            exact (before.native.application.publicView_eventReady event).mp ready
      · exact (impossible (runtime.application.playerStep_other_history who owner (Ne.symm same)
          before command after step)).elim
  | wire =>
      simp only [serviceStep, MessageApplication.invoke, PMF.support_bind,
        Set.mem_iUnion] at member
      obtain ⟨command, _, step⟩ := member
      exact (impossible (congrFun (runtime.application.environmentStep_principalHistory before
        command after step) owner)).elim
  | grant query | includeLatest query who | sample query | tick | expire query =>
      exact (impossible (congrFun (runtime.application.environmentStep_principalHistory before
        _ after member) owner)).elim

/-- The live inclusion state of one prescribed owner event, by its node kind.
A sample has no owner, so it carries no protection. -/
def OwnerEventProtection (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (execution : runtime.application.PolicyExecution) (owner : Player)
    (event : graph.EventId) : Prop :=
  match nodeView graph event with
  | .bind .. => BindingProtectionState runtime inputs execution owner event
  | .resolve .. => ResolutionProtectionState runtime inputs execution owner event
  | .sample .. => False

omit [DecidableEq Player] in
private theorem nodeOwner_eq {event : graph.EventId} {owner nodeOwner : Player}
    {field : EventField Player L} (outputEq : graph.outputLayout event = field)
    {code : EventCode graph.layout field}
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) = code)
    (codeActor : code.actor = some nodeOwner)
    (actor : graph.actor? event = some owner) : nodeOwner = owner :=
  Option.some.inj (codeActor.symm.trans (((EventCode.actor_cast outputEq
    (graph.nodes event)).symm.trans (congrArg EventCode.actor codeEq)).symm.trans actor))

/-- A ready owner event with a matching pending packet is protected at any
state reached from a prescribed-owner boundary by a clock-free plan. -/
theorem OwnerEventProtection.of_ready (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (ordered : graph.BarrierOrdered)
    (feasible : runtime.ServiceFeasible) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (plan : List (ServiceInstruction graph))
    (before start : runtime.application.PolicyExecution)
    (boundary : PrescribedOwnerBoundary runtime inputs before owner)
    (clockFree : serviceTicks plan = 0)
    (member : start ∈ (runtime.runServicePlan players wire plan before).support)
    (event : graph.EventId) (actor : graph.actor? event = some owner)
    (ready : start.native.application.config.cut.Ready event)
    (pending : ∃ message ∈ start.native.pool.pending, Payload.Matches event owner message) :
    OwnerEventProtection runtime inputs start owner event := by
  have progress := runtime.runServicePlan_facts inputs players wire plan before start
    boundary.invariant member
  have zeroProgress : State.ServiceProgress inputs 0 before.native.application
      start.native.application := by simpa only [clockFree] using progress
  have age := boundary.age.of_zero_progress zeroProgress
    (runtime.runServicePlan_activationOrigin inputs players wire plan before start
      boundary.invariant member)
  obtain ⟨entered, activated⟩ := progress.invariant.activatedAt_eq_some_of_ready_actor
    event ready (by rw [actor]; rfl)
  have timely := age.withinDeadline runtime feasible event actor entered activated ready.1
  have authorship := runtime.runServicePlan_authorship players wire plan before start
    boundary.authorship member
  have canonical := runtime.runServicePlan_canonicalCommitments owner policy players prescribed
    wire plan before start boundary.canonical member
  have resources := runtime.runServicePlan_canonicalResources owner policy players prescribed
    wire plan before start boundary.canonical boundary.resources member
  have submissions := runtime.runServicePlan_prescribedBindingSubmissions owner policy players
    prescribed wire plan before start boundary.bindingSubmissions member
  have origins := runtime.runServicePlan_resolutionOriginInvariant inputs ordered owner policy
    players prescribed wire plan before start
    ⟨boundary.invariant, boundary.policyCoherent, boundary.resolutionOrigins⟩ member
  have bindingInvariant := runtime.runServicePlan_bindingInvariant players wire plan before start
    boundary.bindingInvariant member
  unfold OwnerEventProtection
  cases viewNode : nodeView graph event with
  | sample payload law outputEq codeEq =>
      have ownerless : graph.actor? event = none :=
        (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
          (congrArg EventCode.actor codeEq)
      rw [ownerless] at actor
      contradiction
  | bind nodeOwner payload outputEq codeEq =>
      exact ⟨progress.invariant, ready, timely, authorship, canonical, resources, submissions,
        pending⟩
  | resolve nodeOwner payload binding checks outputEq codeEq =>
      exact ⟨progress.invariant, origins.2.1, ready, timely, authorship, origins.2.2,
        bindingInvariant, pending⟩

/-- Clock-free service either completes a protected event or keeps it
protected. -/
theorem OwnerEventProtection.preserved {runtime : EventGraphRuntime graph}
    {inputs : graph.Inputs} {owner : Player} {event : graph.EventId}
    {before : runtime.application.PolicyExecution}
    (holds : OwnerEventProtection runtime inputs before owner event)
    (ordered : graph.BarrierOrdered) (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (plan : List (ServiceInstruction graph))
    (after : runtime.application.PolicyExecution)
    (actor : graph.actor? event = some owner)
    (clockFree : ∀ instruction ∈ plan, instruction.ticks = 0)
    (member : after ∈ (runtime.runServicePlan players wire plan before).support) :
    event ∈ after.native.application.config.cut.completed ∨
      OwnerEventProtection runtime inputs after owner event := by
  unfold OwnerEventProtection at holds ⊢
  cases viewNode : nodeView graph event with
  | sample payload law outputEq codeEq =>
      rw [viewNode] at holds
      exact holds.elim
  | bind nodeOwner payload outputEq codeEq =>
      obtain rfl := nodeOwner_eq outputEq codeEq rfl actor
      rw [viewNode] at holds
      exact runtime.runServicePlan_bindingProtection inputs nodeOwner policy players prescribed
        wire plan before after event payload outputEq codeEq viewNode holds clockFree member
  | resolve nodeOwner payload binding checks outputEq codeEq =>
      obtain rfl := nodeOwner_eq outputEq codeEq rfl actor
      rw [viewNode] at holds
      exact runtime.runServicePlan_resolutionProtection inputs ordered nodeOwner policy players
        prescribed wire plan before after event payload binding checks outputEq codeEq viewNode
        holds clockFree member

/-- Reserved inclusion after clock-free reactions completes a protected event. -/
theorem OwnerEventProtection.includeLatest_complete {runtime : EventGraphRuntime graph}
    {inputs : graph.Inputs} {owner : Player} {event : graph.EventId}
    {before : runtime.application.PolicyExecution}
    (holds : OwnerEventProtection runtime inputs before owner event)
    (ordered : graph.BarrierOrdered) (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (reactions : List (ServiceInstruction graph))
    (after : runtime.application.PolicyExecution)
    (actor : graph.actor? event = some owner)
    (clockFree : ∀ instruction ∈ reactions, instruction.ticks = 0)
    (member : after ∈ (runtime.runServicePlan players wire
      (reactions ++ [.includeLatest event owner]) before).support) :
    event ∈ after.native.application.config.cut.completed := by
  unfold OwnerEventProtection at holds
  cases viewNode : nodeView graph event with
  | sample payload law outputEq codeEq =>
      rw [viewNode] at holds
      exact holds.elim
  | bind nodeOwner payload outputEq codeEq =>
      obtain rfl := nodeOwner_eq outputEq codeEq rfl actor
      rw [viewNode] at holds
      exact runtime.runServicePlan_bindingProtection_includeLatest inputs nodeOwner policy players
        prescribed wire reactions before after event payload outputEq codeEq viewNode holds
        clockFree member
  | resolve nodeOwner payload binding checks outputEq codeEq =>
      obtain rfl := nodeOwner_eq outputEq codeEq rfl actor
      rw [viewNode] at holds
      exact runtime.runServicePlan_resolutionProtection_includeLatest inputs ordered nodeOwner
        policy players prescribed wire reactions before after event payload binding checks
        outputEq codeEq viewNode holds clockFree member

/-- A protected event is ready and still has a matching pending packet. -/
theorem OwnerEventProtection.live {runtime : EventGraphRuntime graph} {inputs : graph.Inputs}
    {execution : runtime.application.PolicyExecution} {owner : Player} {event : graph.EventId}
    (holds : OwnerEventProtection runtime inputs execution owner event) :
    execution.native.application.config.cut.Ready event ∧
      ∃ message ∈ execution.native.pool.pending, Payload.Matches event owner message := by
  unfold OwnerEventProtection at holds
  split at holds
  · exact ⟨holds.ready, holds.pending⟩
  · exact ⟨holds.ready, holds.pending⟩
  · exact holds.elim

/-- An owner event that is submitted by the end of a clock-free plan is
protected from the point of its submission: at the plan start if the
submission predates the plan, otherwise right after its first submission
inside the plan. -/
theorem runServicePlan_submitted_protected (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (ordered : graph.BarrierOrdered)
    (feasible : runtime.ServiceFeasible) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (plan : List (ServiceInstruction graph))
    (before after : runtime.application.PolicyExecution)
    (boundary : PrescribedOwnerBoundary runtime inputs before owner)
    (clockFree : ∀ instruction ∈ plan, instruction.ticks = 0)
    (event : graph.EventId) (actor : graph.actor? event = some owner)
    (submitted : submittedAt (after.principalHistory owner) event = true)
    (member : after ∈ (runtime.runServicePlan players wire plan before).support) :
    ∃ (startPlan rest : List (ServiceInstruction graph))
        (start : runtime.application.PolicyExecution),
      plan = startPlan ++ rest ∧
      start ∈ (runtime.runServicePlan players wire startPlan before).support ∧
      after ∈ (runtime.runServicePlan players wire rest start).support ∧
      (event ∈ start.native.application.config.cut.completed ∨
        OwnerEventProtection runtime inputs start owner event) := by
  have startNil : before ∈ (runtime.runServicePlan players wire [] before).support := by
    simp [runServicePlan]
  by_cases already : event ∈ before.native.application.config.cut.completed
  · exact ⟨[], plan, before, rfl, startNil, member, Or.inl already⟩
  cases initially : submittedAt (before.principalHistory owner) event with
  | true =>
      obtain ⟨ready, pending⟩ := boundary.pending event actor already initially
      exact ⟨[], plan, before, rfl, startNil, member, Or.inr
        (OwnerEventProtection.of_ready runtime inputs ordered feasible owner policy players
          prescribed wire [] before before boundary rfl startNil event actor ready pending)⟩
  | false =>
      obtain ⟨priorPlan, instruction, remaining, prior, next, splitPlan, priorMem, priorFalse,
          nextMem, nextTrue, remainingMem⟩ := runtime.runServicePlan_first_submission players
        wire plan before after owner event initially submitted member
      have nextReady := runtime.serviceStep_new_submission_ready owner policy players prescribed
        wire instruction prior next event priorFalse nextTrue nextMem
      have pending := runtime.serviceStep_new_submission players wire instruction prior next
        owner event priorFalse nextTrue nextMem
      let firstPlan := priorPlan ++ [instruction]
      have wholePlan : plan = firstPlan ++ remaining := by
        simp only [firstPlan, List.append_assoc, List.singleton_append, splitPlan]
      have nextSupported : next ∈
          (runtime.runServicePlan players wire firstPlan before).support := by
        rw [runtime.runServicePlan_append, PMF.support_bind]
        simp only [Set.mem_iUnion]
        exact ⟨prior, priorMem, by simpa only [runServicePlan, PMF.bind_pure] using nextMem⟩
      have ticks : serviceTicks firstPlan = 0 := by
        unfold serviceTicks
        apply List.sum_eq_zero_iff.mpr
        intro value valueMem
        obtain ⟨current, currentMem, rfl⟩ := List.mem_map.mp valueMem
        apply clockFree current
        rw [wholePlan]
        exact List.mem_append_left _ currentMem
      exact ⟨firstPlan, remaining, next, wholePlan, nextSupported, remainingMem, Or.inr
        (OwnerEventProtection.of_ready runtime inputs ordered feasible owner policy players
          prescribed wire firstPlan before next boundary ticks nextSupported event actor nextReady
          pending)⟩

/-- Clock-free service from a prescribed-owner boundary re-establishes the
owner's pending-submission invariant. -/
theorem runServicePlan_ownerSubmissionsPending (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (ordered : graph.BarrierOrdered)
    (feasible : runtime.ServiceFeasible) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (plan : List (ServiceInstruction graph))
    (before after : runtime.application.PolicyExecution)
    (boundary : PrescribedOwnerBoundary runtime inputs before owner)
    (clockFree : ∀ instruction ∈ plan, instruction.ticks = 0)
    (member : after ∈ (runtime.runServicePlan players wire plan before).support) :
    OwnerSubmissionsPending runtime after owner := by
  intro event actor unfinished submitted
  obtain ⟨startPlan, rest, start, planEq, startMem, restMem, protectedStart⟩ :=
    runtime.runServicePlan_submitted_protected inputs ordered feasible owner policy players
      prescribed wire plan before after boundary clockFree event actor submitted member
  have startInvariant := (runtime.runServicePlan_facts inputs players wire startPlan before start
    boundary.invariant startMem).invariant
  have restFacts := runtime.runServicePlan_facts inputs players wire rest start after
    startInvariant restMem
  rcases protectedStart with completed | holds
  · exact (unfinished (restFacts.completed completed)).elim
  have restFree : ∀ instruction ∈ rest, instruction.ticks = 0 := by
    intro instruction instructionMem
    apply clockFree instruction
    rw [planEq]
    exact List.mem_append_right _ instructionMem
  rcases holds.preserved ordered policy players prescribed wire rest after actor restFree
      restMem with completed | holdsAfter
  · exact (unfinished completed).elim
  · exact holdsAfter.live

/-- Any submission of an owner event that exists by the end of a clock-free
plan, whether made during the plan or before it, is completed by the event's
reserved inclusion that follows. -/
theorem runServicePlan_submission_tail_complete (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (ordered : graph.BarrierOrdered)
    (feasible : runtime.ServiceFeasible) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (plan : List (ServiceInstruction graph))
    (before after : runtime.application.PolicyExecution) (event : graph.EventId)
    (boundary : PrescribedOwnerBoundary runtime inputs before owner)
    (actor : graph.actor? event = some owner)
    (clockFree : ∀ instruction ∈ plan, instruction.ticks = 0)
    (submitted : submittedAt (after.principalHistory owner) event = true)
    (member : after ∈ (runtime.runServicePlan players wire
      (plan ++ [.includeLatest event owner]) before).support) :
    event ∈ after.native.application.config.cut.completed := by
  rw [runtime.runServicePlan_append, PMF.support_bind] at member
  simp only [Set.mem_iUnion] at member
  obtain ⟨middle, planMem, inclusionMem⟩ := member
  have included := inclusionMem
  simp only [runServicePlan, PMF.bind_pure] at included
  have histories := runtime.application.environmentStep_principalHistory middle _ after included
  have middleSubmitted : submittedAt (middle.principalHistory owner) event = true := by
    rw [histories] at submitted
    exact submitted
  obtain ⟨startPlan, rest, start, planEq, startMem, restMem, protectedStart⟩ :=
    runtime.runServicePlan_submitted_protected inputs ordered feasible owner policy players
      prescribed wire plan before middle boundary clockFree event actor middleSubmitted planMem
  have tailMem : after ∈ (runtime.runServicePlan players wire
      (rest ++ [.includeLatest event owner]) start).support := by
    rw [runtime.runServicePlan_append, PMF.support_bind]
    simp only [Set.mem_iUnion]
    exact ⟨middle, restMem, inclusionMem⟩
  rcases protectedStart with completed | holds
  · have startInvariant := (runtime.runServicePlan_facts inputs players wire startPlan before
      start boundary.invariant startMem).invariant
    exact (runtime.runServicePlan_facts inputs players wire _ start after startInvariant
      tailMem).completed completed
  · have restFree : ∀ instruction ∈ rest, instruction.ticks = 0 := by
      intro instruction instructionMem
      apply clockFree instruction
      rw [planEq]
      exact List.mem_append_right _ instructionMem
    exact holds.includeLatest_complete ordered policy players prescribed wire rest after actor
      restFree tailMem

end Vegas.EventGraphRuntime
