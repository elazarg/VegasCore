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
      simp only [runServicePlan, FinDist.mem_support_pure] at member
      subst after
      rw [notSubmitted] at submitted
      contradiction
  | cons instruction rest ih =>
      simp only [runServicePlan, FinDist.support_bind, Set.mem_iUnion] at member
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
          simp only [runServicePlan, FinDist.support_bind, Set.mem_iUnion]
          exact ⟨middle, first, priorMem⟩

/-- The compiled owner records a new event submission only while that event
is ready; a player submission itself does not advance the graph. -/
theorem serviceStep_new_submission_ready (runtime : EventGraphRuntime graph)
    (owner : Player) (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (before after : runtime.application.PolicyExecution) (event : graph.EventId)
    (grant : before.native.application.serviceGrant = some event)
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
      simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind,
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
            have ready := (runtime.compilePlayerPolicy_submit_ready_notSubmitted owner policy
              (before.principalHistory owner)
              (MessageApplication.State.observe runtime.application before.native owner)
              event packet grant chosen).1
            rw [runtime.application.playerStep_submit_eq, FinDist.mem_support_pure] at step
            subst after
            exact (before.native.application.publicView_eventReady event).mp ready
      · exact (impossible (runtime.application.playerStep_other_history who owner (Ne.symm same)
          before command after step)).elim
  | wire =>
      simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind,
        Set.mem_iUnion] at member
      obtain ⟨command, _, step⟩ := member
      exact (impossible (congrFun (runtime.application.environmentStep_principalHistory before
        command after step) owner)).elim
  | grant query | includeLatest query who | sample query | tick | expire query =>
      exact (impossible (congrFun (runtime.application.environmentStep_principalHistory before
        _ after member) owner)).elim

/-- Any submission made during a clock-free visit is either included during
that visit or consumed by its reserved inclusion. The event may be unready
at visit entry and become ready only during a wire reaction. -/
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
    (grant : before.native.application.serviceGrant = some event)
    (noGrant : ∀ instruction ∈ plan, ∀ query, instruction ≠ .grant query)
    (clockFree : ∀ instruction ∈ plan, instruction.ticks = 0)
    (submitted : submittedAt (after.principalHistory owner) event = true)
    (member : after ∈ (runtime.runServicePlan players wire
      (plan ++ [.includeLatest event owner]) before).support) :
    event ∈ after.native.application.config.cut.completed := by
  by_cases already : event ∈ before.native.application.config.cut.completed
  · exact (runtime.runServicePlan_facts inputs players wire _ before after boundary.invariant
      member).completed already
  rw [runtime.runServicePlan_append, FinDist.support_bind] at member
  simp only [Set.mem_iUnion] at member
  obtain ⟨middle, planMem, inclusionMem⟩ := member
  have included := inclusionMem
  simp only [runServicePlan, FinDist.bind_pure] at included
  have histories := runtime.application.environmentStep_principalHistory middle _ after included
  have middleSubmitted : submittedAt (middle.principalHistory owner) event = true := by
    rw [histories] at submitted
    exact submitted
  obtain ⟨priorPlan, instruction, remaining, prior, next, splitPlan, priorMem, priorFalse,
      nextMem, nextTrue, remainingMem⟩ := runtime.runServicePlan_first_submission players wire
    plan before middle owner event (boundary.unsubmitted event actor already)
    middleSubmitted planMem
  have priorSubset : ∀ current ∈ priorPlan, current ∈ plan := by
    intro current currentMem
    rw [splitPlan]
    exact List.mem_append_left _ currentMem
  have priorGrant : prior.native.application.serviceGrant = some event := by
    rw [runtime.runServicePlan_serviceGrant_eq players wire priorPlan before prior
      (fun current currentMem => noGrant current (priorSubset current currentMem)) priorMem]
    exact grant
  have nextReady := runtime.serviceStep_new_submission_ready owner policy players prescribed wire
    instruction prior next event priorGrant priorFalse nextTrue nextMem
  have pending := runtime.serviceStep_new_submission players wire instruction prior next owner
    event priorFalse nextTrue nextMem
  let firstPlan := priorPlan ++ [instruction]
  have wholePlan : plan = firstPlan ++ remaining := by
    simp only [firstPlan, List.append_assoc, List.singleton_append, splitPlan]
  have firstSubset : ∀ current ∈ firstPlan, current ∈ plan := by
    intro current currentMem
    rw [wholePlan]
    exact List.mem_append_left _ currentMem
  have nextSupported : next ∈ (runtime.runServicePlan players wire firstPlan before).support := by
    rw [runtime.runServicePlan_append, FinDist.support_bind]
    simp only [Set.mem_iUnion]
    exact ⟨prior, priorMem, by simpa only [runServicePlan, FinDist.bind_pure] using nextMem⟩
  have ticks : serviceTicks firstPlan = 0 := by
    unfold serviceTicks
    apply List.sum_eq_zero_iff.mpr
    intro value valueMem
    obtain ⟨current, currentMem, rfl⟩ := List.mem_map.mp valueMem
    exact clockFree current (firstSubset current currentMem)
  have progress := runtime.runServicePlan_facts inputs players wire firstPlan before next
    boundary.invariant nextSupported
  have zeroProgress : State.ServiceProgress inputs 0 before.native.application
      next.native.application := by simpa only [ticks] using progress
  have age := boundary.age.of_zero_progress zeroProgress
    (runtime.runServicePlan_activationOrigin inputs players wire firstPlan before next
      boundary.invariant nextSupported)
  obtain ⟨entered, activated⟩ := progress.invariant.activatedAt_eq_some_of_ready_actor
    event nextReady (by rw [actor]; rfl)
  have timely := age.withinDeadline runtime feasible event actor entered activated nextReady.1
  have nextAuthorship := runtime.runServicePlan_authorship players wire firstPlan before next
    boundary.authorship nextSupported
  have nextCanonical := runtime.runServicePlan_canonicalCommitments owner policy players prescribed
    wire firstPlan before next boundary.canonical nextSupported
  have nextResources := runtime.runServicePlan_canonicalResources owner policy players prescribed
    wire firstPlan before next boundary.canonical boundary.resources nextSupported
  have nextSubmissions := runtime.runServicePlan_prescribedBindingSubmissions owner policy players
    prescribed wire firstPlan before next boundary.bindingSubmissions nextSupported
  have nextOrigins := runtime.runServicePlan_resolutionOriginInvariant inputs ordered owner policy
    players prescribed wire firstPlan before next
    ⟨boundary.invariant, boundary.policyCoherent, boundary.resolutionOrigins⟩ nextSupported
  have nextBinding := runtime.runServicePlan_bindingInvariant players wire firstPlan before next
    boundary.bindingInvariant nextSupported
  have remainingFree : ∀ current ∈ remaining, current.ticks = 0 := by
    intro current currentMem
    apply clockFree current
    rw [wholePlan]
    exact List.mem_append_right _ currentMem
  have tailMem : after ∈ (runtime.runServicePlan players wire
      (remaining ++ [.includeLatest event owner]) next).support := by
    rw [runtime.runServicePlan_append, FinDist.support_bind]
    simp only [Set.mem_iUnion]
    exact ⟨middle, remainingMem, inclusionMem⟩
  cases viewNode : nodeView graph event with
  | sample payload law outputEq codeEq =>
      have ownerless : graph.actor? event = none :=
        (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
          (congrArg EventCode.actor codeEq)
      rw [ownerless] at actor
      contradiction
  | bind nodeOwner payload outputEq codeEq =>
      have ownerEq : nodeOwner = owner := Option.some.inj
        (((EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
          (congrArg EventCode.actor codeEq)).symm.trans actor)
      subst nodeOwner
      exact runtime.runServicePlan_bindingProtection_includeLatest inputs owner policy players
        prescribed wire remaining next after event payload outputEq codeEq viewNode
        ⟨progress.invariant, nextReady, timely, nextAuthorship, nextCanonical,
          nextResources, nextSubmissions, pending⟩ remainingFree tailMem
  | resolve nodeOwner payload binding checks outputEq codeEq =>
      have ownerEq : nodeOwner = owner := Option.some.inj
        (((EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
          (congrArg EventCode.actor codeEq)).symm.trans actor)
      subst nodeOwner
      exact runtime.runServicePlan_resolutionProtection_includeLatest inputs ordered owner policy
        players prescribed wire remaining next after event payload binding checks outputEq codeEq
        viewNode ⟨progress.invariant, nextOrigins.2.1, nextReady, timely, nextAuthorship,
          nextOrigins.2.2, nextBinding, pending⟩ remainingFree tailMem

end Vegas.EventGraphRuntime
