/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventPrescribedBoundary
import Vegas.Pending.EventServiceReachability
import Vegas.Pending.EventServiceLaw
import Vegas.EventGraph.StateCongruence
import Vegas.Pending.EventServiceGrant
import Vegas.Pending.EventServicePosition
import Vegas.Pending.EventSubmissionCompletion

/-! # Prescribed-owner safety at arbitrary service prefixes -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

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
      PMF.pure (runtime.afterGrant execution event) := by
  simp only [serviceStep, MessageApplication.environmentPolicyStep,
    MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.advance,
    MessageApplication.step]
  simp only [application, environmentStep, PMF.pure_map, PMF.pure_bind]
  rfl

theorem append_cons_eq_append_cases {α : Type} (marker : α) :
    ∀ (before after executed remaining : List α),
      before ++ marker :: after = executed ++ remaining →
      (∃ tail, before = executed ++ tail ∧
        remaining = tail ++ marker :: after) ∨
      ∃ tail, executed = before ++ marker :: tail ∧
        after = tail ++ remaining := by
  intro before
  induction before with
  | nil =>
      intro after executed remaining equality
      cases executed with
      | nil =>
          left
          exact ⟨[], rfl, by simpa using equality.symm⟩
      | cons head tail =>
          simp only [List.nil_append, List.cons_append] at equality
          injection equality with headEq restEq
          subst head
          right
          exact ⟨tail, rfl, restEq⟩
  | cons head before ih =>
      intro after executed remaining equality
      cases executed with
      | nil =>
          left
          refine ⟨head :: before, rfl, ?_⟩
          simpa only [List.nil_append, List.cons_append] using equality.symm
      | cons selected executed =>
          simp only [List.cons_append] at equality
          injection equality with headEq restEq
          subst selected
          rcases ih after executed remaining restEq with left | right
          · obtain ⟨tail, beforeEq, remainingEq⟩ := left
            left
            exact ⟨tail, by simp only [List.cons_append, beforeEq], remainingEq⟩
          · obtain ⟨tail, executedEq, afterEq⟩ := right
            right
            exact ⟨tail, by simp only [List.cons_append, executedEq], afterEq⟩

/-- One complete visit of a ready event owned by the prescribed player
finishes that event, from any coherent partial private stage. -/
theorem runServicePlan_owned_ready_event_complete
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (ordered : graph.BarrierOrdered) (feasible : runtime.ServiceFeasible)
    (owner : Player) (policy : graph.BehavioralPolicy owner)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy)
    (before after : runtime.application.PolicyExecution)
    (boundary : PrescribedOwnerBoundary runtime inputs before owner)
    (event : graph.EventId) (actor : graph.actor? event = some owner)
    (ready : before.native.application.config.cut.Ready event)
    (member : after ∈ (runtime.runServicePlan players wire
      (eventServicePlan roster reactionRounds event) before).support) :
    event ∈ after.native.application.config.cut.completed := by
  let granted := runtime.afterGrant before event
  have grantMem : granted ∈
      (runtime.serviceStep players wire (.grant event) before).support := by
    rw [runtime.serviceStep_grant_eq, PMF.mem_support_pure_iff _ _]
  have planEq : eventServicePlan roster reactionRounds event =
      .grant event :: (List.replicate 3 (.player owner) ++
        (List.replicate reactionRounds (.wire :: roster.map .player)).flatten ++
        [.includeLatest event owner, .sample event]) := by
    simp [eventServicePlan, actor]
  rw [planEq, runServicePlan, runtime.serviceStep_grant_eq,
    PMF.pure_bind] at member
  have grantedInvariant := runtime.serviceStep_facts inputs players wire (.grant event)
    before granted boundary.invariant grantMem |>.invariant
  have grantedPolicy := runtime.serviceStep_policyCoherentAll owner policy players wire
    (.grant event) before granted prescribed boundary.policyCoherent grantMem
  have grantedBinding := runtime.serviceStep_bindingPolicyCoherentAll owner policy players wire
    (.grant event) before granted prescribed boundary.canonical boundary.bindingCoherent grantMem
  have grantedAuthorship := runtime.serviceStep_authorship players wire (.grant event)
    before granted boundary.authorship grantMem
  have grantedCanonical := runtime.serviceStep_canonicalCommitments owner policy players prescribed
    wire (.grant event) before granted boundary.canonical grantMem
  have grantedResources := runtime.serviceStep_canonicalResources owner players wire (.grant event)
    before granted boundary.canonical boundary.resources grantMem
  have grantedSubmissions := runtime.serviceStep_prescribedBindingSubmissions owner policy players
    prescribed wire (.grant event) before granted boundary.bindingSubmissions grantMem
  have grantedOrigins := runtime.serviceStep_resolutionOrigins inputs ordered owner policy players
    prescribed wire (.grant event) before granted boundary.invariant boundary.policyCoherent
    boundary.resolutionOrigins grantMem
  have grantedBindingInvariant := runtime.serviceStep_bindingInvariant players wire (.grant event)
    before granted boundary.bindingInvariant grantMem
  have grantedReady : granted.native.application.config.cut.Ready event := by
    simpa [granted, afterGrant] using ready
  have grantedActor : graph.actor? event = some owner := actor
  have grantedTurn : granted.native.application.publicView.ownTurn? owner = some event :=
    PublicView.ownTurn?_of_ownTurn _ owner event
      (granted.native.application.ownTurn_of_ready ordered owner event
        ((State.publicView_eventReady _ event).mpr grantedReady) actor)
  obtain ⟨entered, activated⟩ :=
    grantedInvariant.activatedAt_eq_some_of_ready_actor event grantedReady (by simp [actor])
  have grantedAge : granted.native.application.OwnerActivationAgeOne owner := by
    apply boundary.age.of_zero_progress
      (runtime.serviceStep_facts inputs players wire (.grant event) before granted
        boundary.invariant grantMem)
    exact runtime.serviceStep_activationOrigin players wire (.grant event) before granted grantMem
  have timely := grantedAge.withinDeadline runtime feasible event actor entered activated
    grantedReady.1
  let reactions : List (ServiceInstruction graph) :=
    (List.replicate reactionRounds
      (.wire :: roster.map fun who => ServiceInstruction.player who)).flatten
  have clockFree : ∀ instruction ∈ reactions, instruction.ticks = 0 := by
    intro instruction instructionMem
    dsimp [reactions] at instructionMem
    simp only [List.mem_flatten] at instructionMem
    obtain ⟨round, roundMem, inRound⟩ := instructionMem
    have roundEq := List.eq_of_mem_replicate roundMem
    subst round
    rcases List.mem_cons.mp inRound with rfl | playerMem
    · rfl
    · obtain ⟨who, _, rfl⟩ := List.mem_map.mp playerMem
      rfl
  by_cases initially : submittedAt (granted.principalHistory owner) event = true
  · -- The owner served its turn before this visit; its packet is still pending.
    obtain ⟨_, pending⟩ := boundary.pending event actor ready.1 (by
      simpa [granted, afterGrant] using initially)
    have holds := OwnerEventProtection.of_ready runtime inputs ordered feasible owner policy
      players prescribed wire [.grant event] before granted boundary rfl
      (by simpa only [runServicePlan, PMF.bind_pure] using grantMem) event actor grantedReady
      pending
    let work := List.replicate 3 (ServiceInstruction.player owner) ++ reactions
    have workFree : ∀ instruction ∈ work, instruction.ticks = 0 := by
      intro instruction instructionMem
      rcases List.mem_append.mp instructionMem with ownerCall | reaction
      · rw [List.eq_of_mem_replicate ownerCall]
        rfl
      · exact clockFree instruction reaction
    have visitEq : List.replicate 3 (ServiceInstruction.player owner) ++
        (List.replicate reactionRounds (.wire :: roster.map .player)).flatten ++
          [.includeLatest event owner, .sample event] =
        (work ++ [.includeLatest event owner]) ++ [.sample event] := by
      simp [work, reactions]
    rw [visitEq, runtime.runServicePlan_append, PMF.support_bind] at member
    simp only [Set.mem_iUnion] at member
    obtain ⟨included, includeMem, sampleMem⟩ := member
    have done := holds.includeLatest_complete ordered policy players prescribed wire work
      included actor workFree includeMem
    have includedInvariant := (runtime.runServicePlan_facts inputs players wire
      (work ++ [.includeLatest event owner]) granted included grantedInvariant
      includeMem).invariant
    exact (runtime.runServicePlan_facts inputs players wire [.sample event] included after
      includedInvariant sampleMem).completed done
  have notSubmitted : submittedAt (granted.principalHistory owner) event = false :=
    Bool.eq_false_of_not_eq_true initially
  cases viewNode : nodeView graph event with
  | sample payload law outputEq codeEq =>
      have ownerless : graph.actor? event = none := by
        unfold EventGraph.actor?
        exact (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
          (congrArg EventCode.actor codeEq)
      rw [ownerless] at actor
      contradiction
  | bind nodeOwner payload outputEq codeEq =>
      have ownerEq : nodeOwner = owner := by
        unfold EventGraph.actor? at actor
        have transformed :=
          (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
            (congrArg EventCode.actor codeEq)
        exact Option.some.inj (transformed.symm.trans actor)
      subst nodeOwner
      exact runtime.runServicePlan_bind_partial_reactions_sample_complete inputs owner policy
        players prescribed wire reactions granted after event payload outputEq codeEq viewNode
          grantedTurn
        grantedReady timely (grantedBinding event payload outputEq actor grantedReady.1)
        notSubmitted grantedInvariant grantedAuthorship grantedCanonical grantedResources
        grantedSubmissions clockFree (by simpa [reactions] using member)
  | resolve nodeOwner payload binding checks outputEq codeEq =>
      have ownerEq : nodeOwner = owner := by
        unfold EventGraph.actor? at actor
        have transformed :=
          (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
            (congrArg EventCode.actor codeEq)
        exact Option.some.inj (transformed.symm.trans actor)
      subst nodeOwner
      exact runtime.runServicePlan_resolve_partial_reactions_sample_complete inputs ordered owner
        policy players prescribed wire reactions granted after event payload binding checks outputEq
        codeEq viewNode grantedTurn grantedReady timely (grantedPolicy event actor) notSubmitted
        ⟨grantedInvariant, grantedPolicy, grantedOrigins⟩ grantedAuthorship
        grantedBindingInvariant clockFree (by simpa [reactions] using member)

/-- Clock-free concrete service preserves the full prescribed-owner boundary
once the endpoint submission boundary has been established. -/
theorem PrescribedOwnerBoundary.after_zero_plan
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (ordered : graph.BarrierOrdered)
    (owner : Player) (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy)
    (plan : List (ServiceInstruction graph))
    (before after : runtime.application.PolicyExecution)
    (boundary : PrescribedOwnerBoundary runtime inputs before owner)
    (clockFree : serviceTicks plan = 0)
    (pending : OwnerSubmissionsPending runtime after owner)
    (member : after ∈ (runtime.runServicePlan players wire plan before).support) :
    PrescribedOwnerBoundary runtime inputs after owner := by
  have progress := runtime.runServicePlan_facts inputs players wire plan before after
    boundary.invariant member
  have origin := runtime.runServicePlan_activationOrigin inputs players wire plan before after
    boundary.invariant member
  have policyCoherent := runtime.runServicePlan_policyCoherentAll owner policy players wire plan
    before after prescribed boundary.policyCoherent member
  have canonical := runtime.runServicePlan_canonicalCommitments owner policy players prescribed wire
    plan before after boundary.canonical member
  refine ⟨progress.invariant, ?_, policyCoherent,
    runtime.runServicePlan_bindingPolicyCoherentAll owner policy players wire plan before after
      prescribed boundary.canonical boundary.bindingCoherent member,
    runtime.runServicePlan_authorship players wire plan before after boundary.authorship member,
    canonical,
    runtime.runServicePlan_canonicalResources owner policy players prescribed wire plan before after
      boundary.canonical boundary.resources member,
    runtime.runServicePlan_prescribedBindingSubmissions owner policy players prescribed wire plan
      before after boundary.bindingSubmissions member,
    ?_, runServicePlan_bindingInvariant runtime players wire plan before after
      boundary.bindingInvariant member,
    pending⟩
  · apply boundary.age.of_zero_progress
    · simpa only [clockFree] using progress
    · exact origin
  · exact (runtime.runServicePlan_resolutionOriginInvariant inputs ordered owner policy players
      prescribed wire plan before after
      ⟨boundary.invariant, boundary.policyCoherent, boundary.resolutionOrigins⟩ member).2.2

/-- The non-clock components of the boundary are ordinary service
invariants; callers may supply an age proof produced by a completed epoch. -/
theorem PrescribedOwnerBoundary.after_plan_of_age
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (ordered : graph.BarrierOrdered)
    (owner : Player) (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy)
    (plan : List (ServiceInstruction graph))
    (before after : runtime.application.PolicyExecution)
    (boundary : PrescribedOwnerBoundary runtime inputs before owner)
    (age : after.native.application.OwnerActivationAgeOne owner)
    (pending : OwnerSubmissionsPending runtime after owner)
    (member : after ∈ (runtime.runServicePlan players wire plan before).support) :
    PrescribedOwnerBoundary runtime inputs after owner := by
  have progress := runtime.runServicePlan_facts inputs players wire plan before after
    boundary.invariant member
  have policyCoherent := runtime.runServicePlan_policyCoherentAll owner policy players wire plan
    before after prescribed boundary.policyCoherent member
  have canonical := runtime.runServicePlan_canonicalCommitments owner policy players prescribed wire
    plan before after boundary.canonical member
  refine ⟨progress.invariant, age, policyCoherent,
    runtime.runServicePlan_bindingPolicyCoherentAll owner policy players wire plan before after
      prescribed boundary.canonical boundary.bindingCoherent member,
    runtime.runServicePlan_authorship players wire plan before after boundary.authorship member,
    canonical,
    runtime.runServicePlan_canonicalResources owner policy players prescribed wire plan before after
      boundary.canonical boundary.resources member,
    runtime.runServicePlan_prescribedBindingSubmissions owner policy players prescribed wire plan
      before after boundary.bindingSubmissions member,
    ?_, runServicePlan_bindingInvariant runtime players wire plan before after
      boundary.bindingInvariant member,
    pending⟩
  exact (runtime.runServicePlan_resolutionOriginInvariant inputs ordered owner policy players
    prescribed wire plan before after
    ⟨boundary.invariant, boundary.policyCoherent, boundary.resolutionOrigins⟩ member).2.2

theorem PrescribedOwnerBoundary.after_event
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (ordered : graph.BarrierOrdered) (feasible : runtime.ServiceFeasible)
    (owner : Player) (policy : graph.BehavioralPolicy owner)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy)
    (before after : runtime.application.PolicyExecution)
    (boundary : PrescribedOwnerBoundary runtime inputs before owner)
    (event : graph.EventId)
    (member : after ∈ (runtime.runServicePlan players wire
      (eventServicePlan roster reactionRounds event) before).support) :
    PrescribedOwnerBoundary runtime inputs after owner := by
  have clockFree : ∀ instruction ∈ eventServicePlan roster reactionRounds event,
      instruction.ticks = 0 := by
    intro instruction instructionMem
    have zero := eventServicePlan_ticks roster reactionRounds event
    unfold serviceTicks at zero
    exact List.sum_eq_zero_iff.mp zero _ (List.mem_map.mpr ⟨instruction, instructionMem, rfl⟩)
  exact boundary.after_zero_plan runtime inputs ordered owner policy players prescribed wire
    (eventServicePlan roster reactionRounds event) before after
    (eventServicePlan_ticks roster reactionRounds event)
    (runtime.runServicePlan_ownerSubmissionsPending inputs ordered feasible owner policy players
      prescribed wire _ before after boundary clockFree member) member

/-- Whole-event boundary and completion laws compose across an arbitrary
event sweep while retaining every entry-ready prescribed event. -/
theorem runEventSweep_prescribedOwner_of_blocks
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (owner : Player) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (events : List graph.EventId)
    (before after : runtime.application.PolicyExecution)
    (boundary : PrescribedOwnerBoundary runtime inputs before owner)
    (blockBoundary : ∀ start event finish,
      PrescribedOwnerBoundary runtime inputs start owner →
      finish ∈ (runtime.runServicePlan players wire
        (eventServicePlan roster reactionRounds event) start).support →
      PrescribedOwnerBoundary runtime inputs finish owner)
    (blockComplete : ∀ start event finish,
      PrescribedOwnerBoundary runtime inputs start owner →
      graph.actor? event = some owner →
      start.native.application.config.cut.Ready event →
      finish ∈ (runtime.runServicePlan players wire
        (eventServicePlan roster reactionRounds event) start).support →
      event ∈ finish.native.application.config.cut.completed)
    (member : after ∈ (runtime.runServicePlan players wire
      (events.flatMap (eventServicePlan roster reactionRounds)) before).support) :
    PrescribedOwnerBoundary runtime inputs after owner ∧
      ∀ event ∈ events, graph.actor? event = some owner →
        before.native.application.config.cut.Ready event →
          event ∈ after.native.application.config.cut.completed := by
  induction events generalizing before with
  | nil =>
      simp only [List.flatMap_nil, runServicePlan, PMF.mem_support_pure_iff _ _] at member
      subst after
      exact ⟨boundary, by simp⟩
  | cons event rest ih =>
      simp only [List.flatMap_cons, runtime.runServicePlan_append,
        PMF.support_bind, Set.mem_iUnion] at member
      obtain ⟨middle, headMem, tailMem⟩ := member
      have middleBoundary := blockBoundary before event middle boundary headMem
      have tail := ih middle middleBoundary tailMem
      refine ⟨tail.1, ?_⟩
      intro query queryMem actor ready
      rcases List.mem_cons.mp queryMem with same | restMem
      · subst query
        have completedMiddle := blockComplete before _ middle boundary actor ready headMem
        exact (runtime.runServicePlan_facts inputs players wire
          (rest.flatMap (eventServicePlan roster reactionRounds)) middle after
          middleBoundary.invariant tailMem).completed completedMiddle
      · have progress := runtime.runServicePlan_facts inputs players wire
          (eventServicePlan roster reactionRounds event) before middle boundary.invariant headMem
        rcases progress.ready_or_completed query ready with completed | middleReady
        · exact (runtime.runServicePlan_facts inputs players wire
            (rest.flatMap (eventServicePlan roster reactionRounds)) middle after
            middleBoundary.invariant tailMem).completed completed
        · exact tail.2 query restMem actor middleReady

theorem runEventSweep_prescribedOwner
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (ordered : graph.BarrierOrdered) (feasible : runtime.ServiceFeasible)
    (owner : Player) (policy : graph.BehavioralPolicy owner)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy)
    (events : List graph.EventId)
    (before after : runtime.application.PolicyExecution)
    (boundary : PrescribedOwnerBoundary runtime inputs before owner)
    (member : after ∈ (runtime.runServicePlan players wire
      (events.flatMap (eventServicePlan roster reactionRounds)) before).support) :
    PrescribedOwnerBoundary runtime inputs after owner ∧
      ∀ event ∈ events, graph.actor? event = some owner →
        before.native.application.config.cut.Ready event →
          event ∈ after.native.application.config.cut.completed := by
  apply runtime.runEventSweep_prescribedOwner_of_blocks inputs owner roster reactionRounds players
    wire events before after boundary
  · intro start event finish startBoundary supported
    exact startBoundary.after_event runtime inputs ordered feasible owner policy roster
      reactionRounds players prescribed wire start finish event supported
  · intro start event finish startBoundary actor ready supported
    exact runtime.runServicePlan_owned_ready_event_complete inputs ordered feasible owner policy
      roster reactionRounds players prescribed wire start finish startBoundary event actor ready
      supported
  · exact member

theorem runServicePlan_expire_principalHistory
    (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (events : List graph.EventId)
    (before after : runtime.application.PolicyExecution)
    (owner : Player)
    (member : after ∈ (runtime.runServicePlan players wire
      (events.map ServiceInstruction.expire) before).support) :
    after.principalHistory owner = before.principalHistory owner := by
  induction events generalizing before with
  | nil =>
      simp only [List.map_nil, runServicePlan, PMF.mem_support_pure_iff _ _] at member
      subst after
      rfl
  | cons event rest ih =>
      simp only [List.map_cons, runServicePlan, PMF.support_bind,
        Set.mem_iUnion] at member
      obtain ⟨middle, first, tail⟩ := member
      exact (ih middle tail).trans (congrFun
        (runtime.application.environmentStep_principalHistory before _ middle first) owner)

/-- Expiry commands never touch the message pool. -/
theorem runServicePlan_expire_pending
    (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (events : List graph.EventId)
    (before after : runtime.application.PolicyExecution)
    (member : after ∈ (runtime.runServicePlan players wire
      (events.map ServiceInstruction.expire) before).support) :
    after.native.pool.pending = before.native.pool.pending := by
  induction events generalizing before with
  | nil =>
      simp only [List.map_nil, runServicePlan, PMF.mem_support_pure_iff _ _] at member
      subst after
      rfl
  | cons event rest ih =>
      simp only [List.map_cons, runServicePlan, PMF.support_bind,
        Set.mem_iUnion] at member
      obtain ⟨middle, first, tail⟩ := member
      exact (ih middle tail).trans (congrArg MessagePool.pending
        (runtime.environmentPolicyStep_application_pool before middle (.expire event) first))

/-- One actual adaptive epoch restores the complete prescribed-owner
boundary. In particular, every activation present at epoch entry is serviced
before the unique clock tick. -/
theorem serviceEpoch_prescribedOwnerBoundary
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (ordered : graph.BarrierOrdered) (feasible : runtime.ServiceFeasible)
    (owner : Player) (policy : graph.BehavioralPolicy owner)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (before after : runtime.application.PolicyExecution)
    (boundary : PrescribedOwnerBoundary runtime inputs before owner)
    (member : after ∈ (runtime.serviceEpoch roster reactionRounds players wire order
      before).support) :
    PrescribedOwnerBoundary runtime inputs after owner := by
  simp only [serviceEpoch, PMF.support_bind, Set.mem_iUnion] at member
  obtain ⟨chosen, _, planMem⟩ := member
  let sweep := chosen.val.flatMap (eventServicePlan roster reactionRounds)
  let expires := (List.finRange graph.order.eventCount).map ServiceInstruction.expire
  have epochEq : epochPlan chosen roster reactionRounds = sweep ++ [.tick] ++ expires := by rfl
  rw [epochEq, runtime.runServicePlan_append, PMF.support_bind] at planMem
  simp only [Set.mem_iUnion] at planMem
  obtain ⟨ticked, tickedMem, expiryMem⟩ := planMem
  obtain ⟨swept, sweepMem, tickMem⟩ :=
    runtime.runServicePlan_support_append players wire sweep [.tick] before ticked tickedMem
  have sweepLaw := runtime.runEventSweep_prescribedOwner inputs ordered feasible owner policy roster
    reactionRounds players prescribed wire chosen.val before swept boundary sweepMem
  have tickStep : ticked ∈ (runtime.serviceStep players wire .tick swept).support := by
    simpa only [runServicePlan, PMF.bind_pure] using tickMem
  have tickProgress := runtime.serviceStep_facts inputs players wire .tick swept ticked
    sweepLaw.1.invariant tickStep
  have combinedMem : ticked ∈ (runtime.runServicePlan players wire
      (sweep ++ [.tick]) before).support := by
    rw [runtime.runServicePlan_append, PMF.support_bind]
    simp only [Set.mem_iUnion]
    exact ⟨swept, sweepMem, tickMem⟩
  have progress := runtime.runServicePlan_facts inputs players wire (sweep ++ [.tick]) before
    ticked boundary.invariant combinedMem
  have sweepTicks : serviceTicks sweep = 0 := by
    dsimp [sweep]
    induction chosen.val with
    | nil => rfl
    | cons event rest ih =>
        simp [List.flatMap_cons, serviceTicks_append, eventServicePlan_ticks, ih]
  have progressOne : State.ServiceProgress inputs 1 before.native.application
      ticked.native.application := by
    simpa only [serviceTicks_append, sweepTicks, Nat.zero_add, serviceTicks_cons,
      serviceTicks_nil, Nat.add_zero, ServiceInstruction.ticks] using progress
  have serviced : ∀ event, graph.actor? event = some owner → ∀ entered,
      before.native.application.activatedAt event = some entered →
        event ∈ ticked.native.application.config.cut.completed := by
    intro event actor entered activated
    have ready := (boundary.invariant.activated_iff event).mp (by simp [activated]) |>.1
    exact tickProgress.completed
      (sweepLaw.2 event (ServiceOrder.mem chosen event) actor ready)
  have tickAge : ticked.native.application.OwnerActivationAgeOne owner :=
    State.OwnerActivationAgeOne.after_epoch progressOne
      (runtime.runServicePlan_activationOrigin inputs players wire (sweep ++ [.tick]) before
        ticked boundary.invariant combinedMem)
      serviced
  have tickHistory := congrFun
    (runtime.application.environmentStep_principalHistory swept _ ticked tickStep) owner
  have tickPool := congrArg MessagePool.pending
    (runtime.environmentPolicyStep_application_pool swept ticked .advanceClock tickStep)
  have tickPending := sweepLaw.1.pending.frame tickProgress.completed tickHistory tickPool
  have tickBoundary := sweepLaw.1.after_plan_of_age runtime inputs ordered owner policy players
    prescribed wire [.tick] swept ticked tickAge tickPending tickMem
  have expiryProgress := runtime.runServicePlan_facts inputs players wire expires ticked after
    tickBoundary.invariant expiryMem
  have expiryHistory := runtime.runServicePlan_expire_principalHistory players wire
    (List.finRange graph.order.eventCount) ticked after owner expiryMem
  have expiryPool := runtime.runServicePlan_expire_pending players wire
    (List.finRange graph.order.eventCount) ticked after expiryMem
  have expiryPending := tickBoundary.pending.frame expiryProgress.completed expiryHistory
    expiryPool
  apply tickBoundary.after_zero_plan runtime inputs ordered owner policy players prescribed wire
    expires ticked after
  · dsimp [expires]
    unfold serviceTicks
    rw [List.map_map]
    apply List.sum_eq_zero_iff.mpr
    intro value valueMem
    obtain ⟨event, _, rfl⟩ := List.mem_map.mp valueMem
    rfl
  · exact expiryPending
  · exact expiryMem

theorem runService_prescribedOwnerBoundary
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (ordered : graph.BarrierOrdered) (feasible : runtime.ServiceFeasible)
    (owner : Player) (policy : graph.BehavioralPolicy owner)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    ∀ count before after,
      PrescribedOwnerBoundary runtime inputs before owner →
      after ∈ (runtime.runService roster reactionRounds players wire order count
        before).support →
      PrescribedOwnerBoundary runtime inputs after owner := by
  intro count
  induction count with
  | zero =>
      intro before after boundary member
      simp only [runService, PMF.mem_support_pure_iff _ _] at member
      simpa only [member] using boundary
  | succ count ih =>
      intro before after boundary member
      simp only [runService, PMF.support_bind, Set.mem_iUnion] at member
      obtain ⟨middle, epochMem, tailMem⟩ := member
      exact ih middle after
        (runtime.serviceEpoch_prescribedOwnerBoundary inputs ordered feasible owner policy roster
          reactionRounds players prescribed wire order before middle boundary epochMem)
        tailMem

theorem EpochBoundary.prescribedOwnerBoundary
    (runtime : EventGraphRuntime graph) (inputs : PMF graph.Inputs)
    (ordered : graph.BarrierOrdered) (feasible : runtime.ServiceFeasible)
    (owner : Player) (policy : graph.BehavioralPolicy owner)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (execution : runtime.application.PolicyExecution)
    (boundary : EpochBoundary runtime inputs roster reactionRounds players wire order execution) :
    ∃ input ∈ inputs.support, PrescribedOwnerBoundary runtime input execution owner := by
  obtain ⟨input, inputMem, count, member⟩ := boundary
  refine ⟨input, inputMem, ?_⟩
  exact runtime.runService_prescribedOwnerBoundary input ordered feasible owner policy roster
    reactionRounds players prescribed wire order count _ execution
    (runtime.prescribedOwnerBoundary_initial input owner) member

/-- Every prefix of one selected epoch keeps the prescribed owner's live
activations at age at most one. Prefixes before the tick are clock-free;
prefixes after it contain the entire event sweep. -/
theorem epochPlan_prefix_ownerActivationAgeOne
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (ordered : graph.BarrierOrdered) (feasible : runtime.ServiceFeasible)
    (owner : Player) (policy : graph.BehavioralPolicy owner)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy)
    (chosen : ServiceOrder graph)
    (executed remaining : List (ServiceInstruction graph))
    (before after : runtime.application.PolicyExecution)
    (boundary : PrescribedOwnerBoundary runtime inputs before owner)
    (split : epochPlan chosen roster reactionRounds = executed ++ remaining)
    (member : after ∈ (runtime.runServicePlan players wire executed before).support) :
    after.native.application.OwnerActivationAgeOne owner := by
  let sweep := chosen.val.flatMap (eventServicePlan roster reactionRounds)
  let expires := (List.finRange graph.order.eventCount).map ServiceInstruction.expire
  have epochEq : epochPlan chosen roster reactionRounds = sweep ++ .tick :: expires := by
    simp [epochPlan, sweep, expires]
  have decomposition : sweep ++ .tick :: expires = executed ++ remaining := by
    rw [← split]
    exact epochEq.symm
  rcases append_cons_eq_append_cases (.tick : ServiceInstruction graph)
      sweep expires executed remaining decomposition with beforeTick | afterTick
  · obtain ⟨tail, sweepEq, _⟩ := beforeTick
    have sweepTicks : serviceTicks sweep = 0 := by
      dsimp [sweep]
      induction chosen.val with
      | nil => rfl
      | cons event rest ih =>
          simp [List.flatMap_cons, serviceTicks_append, eventServicePlan_ticks, ih]
    have executedTicks : serviceTicks executed = 0 := by
      rw [sweepEq, serviceTicks_append] at sweepTicks
      omega
    apply boundary.age.of_zero_progress
    · simpa only [executedTicks] using
        runtime.runServicePlan_facts inputs players wire executed before after
          boundary.invariant member
    · exact runtime.runServicePlan_activationOrigin inputs players wire executed before after
        boundary.invariant member
  · obtain ⟨tail, executedEq, expiresEq⟩ := afterTick
    have executedShape : executed = (sweep ++ [.tick]) ++ tail := by
      simpa only [List.append_assoc, List.singleton_append] using executedEq
    rw [executedShape, runtime.runServicePlan_append, PMF.support_bind] at member
    simp only [Set.mem_iUnion] at member
    obtain ⟨ticked, tickedMem, tailMem⟩ := member
    obtain ⟨swept, sweepMem, tickMem⟩ :=
      runtime.runServicePlan_support_append players wire sweep [.tick] before ticked tickedMem
    have sweepLaw := runtime.runEventSweep_prescribedOwner inputs ordered feasible owner policy
      roster reactionRounds players prescribed wire chosen.val before swept boundary sweepMem
    have tickStep : ticked ∈ (runtime.serviceStep players wire .tick swept).support := by
      simpa only [runServicePlan, PMF.bind_pure] using tickMem
    have tickProgress := runtime.serviceStep_facts inputs players wire .tick swept ticked
      sweepLaw.1.invariant tickStep
    have combinedMem : ticked ∈ (runtime.runServicePlan players wire
        (sweep ++ [.tick]) before).support := by
      rw [runtime.runServicePlan_append, PMF.support_bind]
      simp only [Set.mem_iUnion]
      exact ⟨swept, sweepMem, tickMem⟩
    have sweepTicks : serviceTicks sweep = 0 := by
      dsimp [sweep]
      induction chosen.val with
      | nil => rfl
      | cons event rest ih =>
          simp [List.flatMap_cons, serviceTicks_append, eventServicePlan_ticks, ih]
    have progress := runtime.runServicePlan_facts inputs players wire (sweep ++ [.tick]) before
      ticked boundary.invariant combinedMem
    have progressOne : State.ServiceProgress inputs 1 before.native.application
        ticked.native.application := by
      simpa only [serviceTicks_append, sweepTicks, Nat.zero_add, serviceTicks_cons,
        serviceTicks_nil, Nat.add_zero, ServiceInstruction.ticks] using progress
    have serviced : ∀ event, graph.actor? event = some owner → ∀ entered,
        before.native.application.activatedAt event = some entered →
          event ∈ ticked.native.application.config.cut.completed := by
      intro event actor entered activated
      have ready := (boundary.invariant.activated_iff event).mp (by simp [activated]) |>.1
      exact tickProgress.completed
        (sweepLaw.2 event (ServiceOrder.mem chosen event) actor ready)
    have tickAge : ticked.native.application.OwnerActivationAgeOne owner :=
      State.OwnerActivationAgeOne.after_epoch progressOne
        (runtime.runServicePlan_activationOrigin inputs players wire (sweep ++ [.tick]) before
          ticked boundary.invariant combinedMem)
        serviced
    have expiresTicks : serviceTicks expires = 0 := by
      dsimp [expires]
      unfold serviceTicks
      rw [List.map_map]
      apply List.sum_eq_zero_iff.mpr
      intro value valueMem
      obtain ⟨event, _, rfl⟩ := List.mem_map.mp valueMem
      rfl
    have tailTicks : serviceTicks tail = 0 := by
      rw [expiresEq, serviceTicks_append] at expiresTicks
      omega
    apply tickAge.of_zero_progress
    · simpa only [tailTicks] using
        runtime.runServicePlan_facts inputs players wire tail ticked after
          tickProgress.invariant tailMem
    · exact runtime.runServicePlan_activationOrigin inputs players wire tail ticked after
        tickProgress.invariant tailMem

namespace ServiceReachable

/-- The prescribed owner's activation-age bound holds at every actual
small-step control prefix, including positions inside an event visit and the
post-tick expiry sweep. -/
theorem ownerActivationAgeOne
    (runtime : EventGraphRuntime graph) (inputs : PMF graph.Inputs)
    (ordered : graph.BarrierOrdered) (feasible : runtime.ServiceFeasible)
    (owner : Player) (policy : graph.BehavioralPolicy owner)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (control : ServiceControl runtime)
    (reachable : ServiceReachable runtime inputs roster reactionRounds players wire order
      control) :
    control.execution.native.application.OwnerActivationAgeOne owner := by
  have position := reachable.position runtime inputs roster reactionRounds players wire order
  rcases position with boundaryPosition | runningPosition
  · obtain ⟨_, epochBoundary⟩ := boundaryPosition
    obtain ⟨input, _, ownerBoundary⟩ := epochBoundary.prescribedOwnerBoundary runtime inputs
      ordered feasible owner policy roster reactionRounds players prescribed wire order
      control.execution
    exact ownerBoundary.age
  · obtain ⟨before, chosen, executed, epochBoundary, _, split, member⟩ := runningPosition
    obtain ⟨input, _, ownerBoundary⟩ := epochBoundary.prescribedOwnerBoundary runtime inputs
      ordered feasible owner policy roster reactionRounds players prescribed wire order before
    exact runtime.epochPlan_prefix_ownerActivationAgeOne input ordered feasible owner policy roster
      reactionRounds players prescribed wire chosen executed control.plan before control.execution
      ownerBoundary split member

end ServiceReachable

end Vegas.EventGraphRuntime
