/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventHonestDeadline
import Vegas.Pending.EventHonestBlockBase
import Vegas.Pending.EventHonestEvent
import Vegas.Pending.EventPotential

/-! # Honest event epochs -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- At a clean boundary, retained cache entries belong only to completed
events and hence do not alter the canonical continuation. -/
theorem HonestBoundary.continuationLaw_eq
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (profile : graph.BehavioralProfile)
    (execution : runtime.application.PolicyExecution)
    (boundary : HonestBoundary runtime inputs execution) :
    execution.native.application.continuationLaw profile =
      graph.canonicalContinuation profile execution.native.application.config := by
  unfold State.continuationLaw
  apply graph.canonicalContinuation_congr_on_unfinished
  intro event unfinished who actor observation
  rw [normalizePolicy_memoizedProfile, memoizedProfile,
    boundary.remembered_unfinished event unfinished]

/-- A clean-boundary block whose configuration law is one normalized ready
step preserves the canonical continuation potential. -/
theorem HonestBoundary.ready_block_continuationLaw
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (ordered : graph.BarrierOrdered) (profile : graph.BehavioralProfile)
    (execution : runtime.application.PolicyExecution)
    (boundary : HonestBoundary runtime inputs execution)
    (event : graph.EventId)
    (ready : execution.native.application.config.cut.Ready event)
    (law : FinDist runtime.application.PolicyExecution)
    (configLaw : law.map (fun next => next.native.application.config) =
      graph.normalizedPolicyStep profile execution.native.application.config event ready)
    (boundaryLaw : ∀ next ∈ law.support, HonestBoundary runtime inputs next) :
    law.bind (fun next => next.native.application.continuationLaw profile) =
      execution.native.application.continuationLaw profile := by
  rw [boundary.continuationLaw_eq runtime inputs profile execution]
  calc
    law.bind (fun next => next.native.application.continuationLaw profile) =
        law.bind (fun next =>
          graph.canonicalContinuation profile next.native.application.config) := by
      apply FinDist.bind_congr
      intro next member
      exact (boundaryLaw next member).continuationLaw_eq runtime inputs profile next
    _ = (law.map (fun next => next.native.application.config)).bind
          (graph.canonicalContinuation profile) := by rw [FinDist.bind_map]
    _ = (graph.normalizedPolicyStep profile execution.native.application.config event ready).bind
          (graph.canonicalContinuation profile) := by rw [configLaw]
    _ = graph.canonicalContinuation profile execution.native.application.config :=
      ordered.normalizedThenCanonical_eq profile execution.native.application.config event ready

/-- An unavailable clean-boundary event block preserves the continuation
potential. -/
theorem HonestBoundary.unready_block_continuationLaw
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (profile : graph.BehavioralProfile)
    (wire : runtime.application.WirePolicy) (roster : List Player)
    (reactionRounds : Nat) (execution : runtime.application.PolicyExecution)
    (boundary : HonestBoundary runtime inputs execution) (event : graph.EventId)
    (unready : ¬execution.native.application.config.cut.Ready event) :
    (runtime.runServicePlan (runtime.compileProfile profile) wire
      (eventServicePlan roster reactionRounds event) execution).bind
        (fun next => next.native.application.continuationLaw profile) =
      execution.native.application.continuationLaw profile := by
  have block := boundary.unready_block runtime inputs profile wire roster reactionRounds
    execution event unready
  rw [boundary.continuationLaw_eq runtime inputs profile execution]
  calc
    _ = (runtime.runServicePlan (runtime.compileProfile profile) wire
          (eventServicePlan roster reactionRounds event) execution).bind
        (fun next => graph.canonicalContinuation profile
          next.native.application.config) := by
      apply FinDist.bind_congr
      intro next member
      exact (block.2 next member).continuationLaw_eq runtime inputs profile next
    _ = ((runtime.runServicePlan (runtime.compileProfile profile) wire
          (eventServicePlan roster reactionRounds event) execution).map
            (fun next => next.native.application.config)).bind
          (graph.canonicalContinuation profile) := by rw [FinDist.bind_map]
    _ = _ := by rw [block.1, FinDist.pure_bind]

theorem runEventSweep
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (profile : graph.BehavioralProfile) (wire : runtime.application.WirePolicy)
    (roster : List Player) (reactionRounds : Nat)
    (events : List graph.EventId)
    (execution : runtime.application.PolicyExecution)
    (boundary : HonestBoundary runtime inputs execution)
    (age : execution.native.application.ActivationAgeOne)
    (blockPotential : ∀ before event,
      HonestBoundary runtime inputs before → before.native.application.ActivationAgeOne →
      (runtime.runServicePlan (runtime.compileProfile profile) wire
        (eventServicePlan roster reactionRounds event) before).bind
          (fun next => next.native.application.continuationLaw profile) =
        before.native.application.continuationLaw profile)
    (blockBoundary : ∀ before event,
      HonestBoundary runtime inputs before → before.native.application.ActivationAgeOne →
      ∀ next ∈ (runtime.runServicePlan (runtime.compileProfile profile) wire
        (eventServicePlan roster reactionRounds event) before).support,
        HonestBoundary runtime inputs next)
    (blockComplete : ∀ before event,
      HonestBoundary runtime inputs before → before.native.application.ActivationAgeOne →
      before.native.application.config.cut.Ready event →
      ∀ next ∈ (runtime.runServicePlan (runtime.compileProfile profile) wire
        (eventServicePlan roster reactionRounds event) before).support,
        event ∈ next.native.application.config.cut.completed) :
    let plan := events.flatMap (eventServicePlan roster reactionRounds)
    (runtime.runServicePlan (runtime.compileProfile profile) wire plan execution).bind
        (fun next => next.native.application.continuationLaw profile) =
      execution.native.application.continuationLaw profile ∧
    ∀ next ∈ (runtime.runServicePlan (runtime.compileProfile profile) wire plan execution).support,
      HonestBoundary runtime inputs next ∧
      next.native.application.ActivationAgeOne ∧
      ∀ event ∈ events, execution.native.application.config.cut.Ready event →
        event ∈ next.native.application.config.cut.completed := by
  induction events generalizing execution with
  | nil =>
      simp only [List.flatMap_nil, runServicePlan, FinDist.pure_bind]
      constructor
      · trivial
      · intro next member
        rw [FinDist.mem_support_pure] at member
        subst next
        exact ⟨boundary, age, by simp⟩
  | cons event rest ih =>
      simp only [List.flatMap_cons]
      rw [runtime.runServicePlan_append, FinDist.bind_bind]
      have headProgress (middle) (member : middle ∈
          (runtime.runServicePlan (runtime.compileProfile profile) wire
            (eventServicePlan roster reactionRounds event) execution).support) :=
        runtime.runServicePlan_facts inputs (runtime.compileProfile profile) wire
          (eventServicePlan roster reactionRounds event) execution middle boundary.invariant member
      have headAge (middle) (member : middle ∈
          (runtime.runServicePlan (runtime.compileProfile profile) wire
            (eventServicePlan roster reactionRounds event) execution).support) :
          middle.native.application.ActivationAgeOne := by
        apply age.of_zero_progress (by
          simpa only [eventServicePlan_ticks] using headProgress middle member)
        exact runtime.runServicePlan_activationOrigin inputs (runtime.compileProfile profile) wire
          (eventServicePlan roster reactionRounds event) execution middle boundary.invariant member
      constructor
      · calc
          _ = (runtime.runServicePlan (runtime.compileProfile profile) wire
              (eventServicePlan roster reactionRounds event) execution).bind
                (fun middle => middle.native.application.continuationLaw profile) := by
            apply FinDist.bind_congr
            intro middle member
            exact (ih middle (blockBoundary execution event boundary age middle member)
              (headAge middle member)).1
          _ = _ := blockPotential execution event boundary age
      · intro next member
        rw [FinDist.support_bind] at member
        simp only [Set.mem_iUnion] at member
        obtain ⟨middle, headMem, tailMem⟩ := member
        have middleBoundary := blockBoundary execution event boundary age middle headMem
        have middleAge := headAge middle headMem
        have tail := (ih middle middleBoundary middleAge).2 next tailMem
        refine ⟨tail.1, tail.2.1, ?_⟩
        intro query queryMem initialReady
        rcases List.mem_cons.mp queryMem with same | restMem
        · subst query
          have completedMiddle := blockComplete execution event boundary age initialReady
            middle headMem
          exact (runtime.runServicePlan_facts inputs (runtime.compileProfile profile) wire
            (rest.flatMap (eventServicePlan roster reactionRounds)) middle next
            middleBoundary.invariant tailMem).completed completedMiddle
        · have progress := headProgress middle headMem
          rcases progress.ready_or_completed query initialReady with completed | ready
          · exact (runtime.runServicePlan_facts inputs (runtime.compileProfile profile) wire
              (rest.flatMap (eventServicePlan roster reactionRounds)) middle next
              middleBoundary.invariant tailMem).completed completed
          · exact tail.2.2 query restMem ready

theorem expirySweep_honestBoundary
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (profile : graph.BehavioralProfile) (wire : runtime.application.WirePolicy)
    (events : List graph.EventId) (execution next : runtime.application.PolicyExecution)
    (boundary : HonestBoundary runtime inputs execution)
    (member : next ∈ (runtime.runServicePlan (runtime.compileProfile profile) wire
      (events.map .expire) execution).support) :
    HonestBoundary runtime inputs next := by
  induction events generalizing execution with
  | nil =>
      simp only [List.map_nil, runServicePlan, FinDist.mem_support_pure] at member
      simpa [member] using boundary
  | cons event rest ih =>
      simp only [List.map_cons, runServicePlan, FinDist.support_bind,
        Set.mem_iUnion] at member
      obtain ⟨middle, head, tail⟩ := member
      have middleBoundary := environmentPolicyStep_honestBoundary runtime inputs execution middle
        (.expire event) boundary head
      exact ih middle middleBoundary tail

theorem serviceStep_tick_facts
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (profile : graph.BehavioralProfile) (wire : runtime.application.WirePolicy)
    (execution next : runtime.application.PolicyExecution)
    (boundary : HonestBoundary runtime inputs execution)
    (member : next ∈ (runtime.serviceStep (runtime.compileProfile profile) wire .tick
      execution).support) :
    HonestBoundary runtime inputs next ∧
      next.native.application.config = execution.native.application.config ∧
      next.native.application.remembered = execution.native.application.remembered := by
  have nextBoundary := environmentPolicyStep_honestBoundary runtime inputs execution next
    .advanceClock boundary member
  have native : next.native ∈
      ((runtime.application.environmentPolicyStep execution
        (.application .advanceClock)).map MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, member, rfl⟩
  rw [MessageApplication.environmentStep_native] at native
  simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
    MessageApplication.step, FinDist.support_map, Set.mem_image] at native
  obtain ⟨state, supported, same⟩ := native
  change state ∈ (Vegas.EventGraphRuntime.environmentStep runtime
    execution.native.application .advanceClock).support at supported
  rw [Vegas.EventGraphRuntime.environmentStep.eq_def] at supported
  simp only [FinDist.mem_support_pure] at supported
  subst state
  have appEq := congrArg (fun result : runtime.application.State => result.application) same.symm
  refine ⟨nextBoundary, ?_, ?_⟩
  · simp only [appEq]
  · simp only [appEq]

theorem serviceStep_tick_continuationLaw
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (profile : graph.BehavioralProfile) (wire : runtime.application.WirePolicy)
    (execution next : runtime.application.PolicyExecution)
    (boundary : HonestBoundary runtime inputs execution)
    (member : next ∈ (runtime.serviceStep (runtime.compileProfile profile) wire .tick
      execution).support) :
    next.native.application.continuationLaw profile =
      execution.native.application.continuationLaw profile := by
  obtain ⟨_, config, remembered⟩ := runtime.serviceStep_tick_facts inputs profile wire
    execution next boundary member
  unfold State.continuationLaw
  rw [config, remembered]

theorem expirySweep_continuationLaw
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    (inputs : graph.Inputs) (profile : graph.BehavioralProfile)
    (wire : runtime.application.WirePolicy)
    (execution next : runtime.application.PolicyExecution)
    (boundary : HonestBoundary runtime inputs execution)
    (age : execution.native.application.ActivationAgeOne)
    (member : next ∈ (runtime.runServicePlan (runtime.compileProfile profile) wire
      ((List.finRange graph.order.eventCount).map .expire) execution).support) :
    HonestBoundary runtime inputs next ∧
      next.native.application.continuationLaw profile =
        execution.native.application.continuationLaw profile := by
  have applicationEq := runtime.runServicePlan_expiry_application_eq feasible inputs
    (runtime.compileProfile profile) wire execution next boundary.invariant age member
  refine ⟨runtime.expirySweep_honestBoundary inputs profile wire
    (List.finRange graph.order.eventCount) execution next boundary member, ?_⟩
  unfold State.continuationLaw
  rw [applicationEq]

/-- One concrete adaptive epoch preserves the honest boundary, the one-block
activation bound, and the memoized canonical continuation, assuming the three
local laws for each clock-free event block. -/
theorem serviceEpoch_honest_of_block
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (_ordered : graph.BarrierOrdered) (feasible : runtime.ServiceFeasible)
    (profile : graph.BehavioralProfile) (roster : List Player)
    (reactionRounds : Nat) (wire : runtime.application.WirePolicy)
    (order : runtime.ServiceOrderPolicy)
    (execution : runtime.application.PolicyExecution)
    (boundary : HonestBoundary runtime inputs execution)
    (age : execution.native.application.ActivationAgeOne)
    (blockPotential : ∀ before event,
      HonestBoundary runtime inputs before → before.native.application.ActivationAgeOne →
      (runtime.runServicePlan (runtime.compileProfile profile) wire
        (eventServicePlan roster reactionRounds event) before).bind
          (fun next => next.native.application.continuationLaw profile) =
        before.native.application.continuationLaw profile)
    (blockBoundary : ∀ before event,
      HonestBoundary runtime inputs before → before.native.application.ActivationAgeOne →
      ∀ next ∈ (runtime.runServicePlan (runtime.compileProfile profile) wire
        (eventServicePlan roster reactionRounds event) before).support,
        HonestBoundary runtime inputs next)
    (blockComplete : ∀ before event,
      HonestBoundary runtime inputs before → before.native.application.ActivationAgeOne →
      before.native.application.config.cut.Ready event →
      ∀ next ∈ (runtime.runServicePlan (runtime.compileProfile profile) wire
        (eventServicePlan roster reactionRounds event) before).support,
        event ∈ next.native.application.config.cut.completed) :
    (runtime.serviceEpoch roster reactionRounds (runtime.compileProfile profile) wire order
      execution).bind (fun next => next.native.application.continuationLaw profile) =
        execution.native.application.continuationLaw profile ∧
    ∀ next ∈ (runtime.serviceEpoch roster reactionRounds
      (runtime.compileProfile profile) wire order execution).support,
      HonestBoundary runtime inputs next ∧ next.native.application.ActivationAgeOne := by
  unfold serviceEpoch
  constructor
  · rw [FinDist.bind_bind]
    apply Eq.trans (FinDist.bind_congr fun chosen _ => ?_)
    · exact FinDist.bind_const _ _
    let sweep := chosen.val.flatMap (eventServicePlan roster reactionRounds)
    let expires := (List.finRange graph.order.eventCount).map ServiceInstruction.expire
    have epochEq : epochPlan chosen roster reactionRounds = sweep ++ [.tick] ++ expires := by
      rfl
    rw [epochEq, runtime.runServicePlan_append]
    rw [runtime.runServicePlan_append, FinDist.bind_bind, FinDist.bind_bind]
    have sweepLaw := runtime.runEventSweep inputs profile wire roster reactionRounds chosen.val
      execution boundary age blockPotential blockBoundary blockComplete
    calc
      _ = (runtime.runServicePlan (runtime.compileProfile profile) wire sweep execution).bind
          (fun middle => middle.native.application.continuationLaw profile) := by
        apply FinDist.bind_congr
        intro middle middleMem
        rw [← FinDist.bind_const
          (runtime.runServicePlan (runtime.compileProfile profile) wire [.tick] middle)
          (middle.native.application.continuationLaw profile)]
        apply FinDist.bind_congr
        intro ticked tickMem
        have combinedMem : ticked ∈ (runtime.runServicePlan
            (runtime.compileProfile profile) wire (sweep ++ [.tick]) execution).support := by
          rw [runtime.runServicePlan_append, FinDist.support_bind]
          simp only [Set.mem_iUnion]
          exact ⟨middle, middleMem, by simpa [runServicePlan] using tickMem⟩
        have progress := runtime.runServicePlan_facts inputs (runtime.compileProfile profile)
          wire (sweep ++ [.tick]) execution ticked boundary.invariant combinedMem
        have origin := runtime.runServicePlan_activationOrigin inputs
          (runtime.compileProfile profile) wire (sweep ++ [.tick]) execution ticked
          boundary.invariant combinedMem
        have serviced : ∀ event entered,
            execution.native.application.activatedAt event = some entered →
              event ∈ ticked.native.application.config.cut.completed := by
          intro event entered activated
          have ready := (boundary.invariant.activated_iff event).mp (by simp [activated]) |>.1
          have tickConfig := (runtime.serviceStep_tick_facts inputs profile wire middle ticked
            (sweepLaw.2 middle middleMem).1 (by simpa [runServicePlan] using tickMem)).2.1
          rw [tickConfig]
          exact (sweepLaw.2 middle middleMem).2.2 event (ServiceOrder.mem chosen event) ready
        have sweepTicks : serviceTicks sweep = 0 := by
          dsimp [sweep]
          induction chosen.val with
          | nil => rfl
          | cons event rest ih =>
              simp [List.flatMap_cons, serviceTicks_append, eventServicePlan_ticks, ih]
        have progressOne : State.ServiceProgress inputs 1 execution.native.application
            ticked.native.application := by
          convert progress using 1
          all_goals
            simp only [serviceTicks_append, sweepTicks, serviceTicks_cons,
              serviceTicks_nil, Nat.zero_add, Nat.add_zero, ServiceInstruction.ticks]
        have tickAge := State.activationAgeOne_after_epoch
          progressOne origin serviced
        have tickBoundary := (runtime.serviceStep_tick_facts inputs profile wire middle ticked
          (sweepLaw.2 middle middleMem).1 (by simpa [runServicePlan] using tickMem)).1
        have expiryLaw (next) (nextMem) :=
          runtime.expirySweep_continuationLaw feasible inputs profile wire ticked next
            tickBoundary tickAge nextMem
        calc
          _ = ticked.native.application.continuationLaw profile := by
            rw [← FinDist.bind_const
              (runtime.runServicePlan (runtime.compileProfile profile) wire expires ticked)
              (ticked.native.application.continuationLaw profile)]
            apply FinDist.bind_congr
            intro next nextMem
            exact (expiryLaw next nextMem).2
          _ = middle.native.application.continuationLaw profile :=
            runtime.serviceStep_tick_continuationLaw inputs profile wire middle ticked
              (sweepLaw.2 middle middleMem).1 (by simpa [runServicePlan] using tickMem)
      _ = _ := sweepLaw.1
  · intro next member
    simp only [FinDist.support_bind, Set.mem_iUnion] at member
    obtain ⟨chosen, _, member⟩ := member
    let sweep := chosen.val.flatMap (eventServicePlan roster reactionRounds)
    let expires := (List.finRange graph.order.eventCount).map ServiceInstruction.expire
    have epochEq : epochPlan chosen roster reactionRounds = sweep ++ [.tick] ++ expires := by rfl
    rw [epochEq, runtime.runServicePlan_append] at member
    simp only [FinDist.support_bind, Set.mem_iUnion] at member
    obtain ⟨ticked, tickedMem, expiryMem⟩ := member
    obtain ⟨swept, sweepMem, tickMem⟩ :=
      runtime.runServicePlan_support_append (runtime.compileProfile profile) wire
        sweep [.tick] execution ticked tickedMem
    have sweepLaw := runtime.runEventSweep inputs profile wire roster reactionRounds chosen.val
      execution boundary age blockPotential blockBoundary blockComplete
    have middleFacts := sweepLaw.2 swept sweepMem
    have tickBoundary := (runtime.serviceStep_tick_facts inputs profile wire swept ticked
      middleFacts.1 (by simpa [runServicePlan] using tickMem)).1
    have combinedMem : ticked ∈ (runtime.runServicePlan (runtime.compileProfile profile) wire
        (sweep ++ [.tick]) execution).support := by
      rw [runtime.runServicePlan_append, FinDist.support_bind]
      simp only [Set.mem_iUnion]
      exact ⟨swept, sweepMem, by simpa [runServicePlan] using tickMem⟩
    have progress := runtime.runServicePlan_facts inputs (runtime.compileProfile profile) wire
      (sweep ++ [.tick]) execution ticked boundary.invariant combinedMem
    have origin := runtime.runServicePlan_activationOrigin inputs
      (runtime.compileProfile profile) wire (sweep ++ [.tick]) execution ticked
      boundary.invariant combinedMem
    have serviced : ∀ event entered,
        execution.native.application.activatedAt event = some entered →
          event ∈ ticked.native.application.config.cut.completed := by
      intro event entered activated
      have ready := (boundary.invariant.activated_iff event).mp (by simp [activated]) |>.1
      have tickConfig := (runtime.serviceStep_tick_facts inputs profile wire swept ticked
        middleFacts.1 (by simpa [runServicePlan] using tickMem)).2.1
      rw [tickConfig]
      exact middleFacts.2.2 event (ServiceOrder.mem chosen event) ready
    have sweepTicks : serviceTicks sweep = 0 := by
      dsimp [sweep]
      induction chosen.val with
      | nil => rfl
      | cons event rest ih =>
          simp [List.flatMap_cons, serviceTicks_append, eventServicePlan_ticks, ih]
    have progressOne : State.ServiceProgress inputs 1 execution.native.application
        ticked.native.application := by
      convert progress using 1
      all_goals
        simp only [serviceTicks_append, sweepTicks, serviceTicks_cons,
          serviceTicks_nil, Nat.zero_add, Nat.add_zero, ServiceInstruction.ticks]
    have tickAge := State.activationAgeOne_after_epoch
      progressOne origin serviced
    have final := runtime.expirySweep_continuationLaw feasible inputs profile wire ticked next
      tickBoundary tickAge expiryMem
    have applicationEq := runtime.runServicePlan_expiry_application_eq feasible inputs
      (runtime.compileProfile profile) wire ticked next tickBoundary.invariant tickAge expiryMem
    refine ⟨final.1, ?_⟩
    rw [applicationEq]
    exact tickAge

/-- An actual honest service epoch preserves the memoized continuation and
restores both clean-boundary invariants. -/
theorem serviceEpoch_honest
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (ordered : graph.BarrierOrdered) (feasible : runtime.ServiceFeasible)
    (profile : graph.BehavioralProfile) (roster : List Player)
    (reactionRounds : Nat) (wire : runtime.application.WirePolicy)
    (order : runtime.ServiceOrderPolicy)
    (execution : runtime.application.PolicyExecution)
    (boundary : HonestBoundary runtime inputs execution)
    (age : execution.native.application.ActivationAgeOne) :
    (runtime.serviceEpoch roster reactionRounds (runtime.compileProfile profile) wire order
      execution).bind (fun next => next.native.application.continuationLaw profile) =
        execution.native.application.continuationLaw profile ∧
    ∀ next ∈ (runtime.serviceEpoch roster reactionRounds
      (runtime.compileProfile profile) wire order execution).support,
      HonestBoundary runtime inputs next ∧ next.native.application.ActivationAgeOne := by
  apply runtime.serviceEpoch_honest_of_block inputs ordered feasible profile roster
    reactionRounds wire order execution boundary age
  · intro before event beforeBoundary beforeAge
    by_cases ready : before.native.application.config.cut.Ready event
    · have block := beforeBoundary.ready_event_block runtime inputs feasible profile wire roster
        reactionRounds before beforeAge event ready
      exact beforeBoundary.ready_block_continuationLaw runtime inputs ordered profile before event
        ready _ block.1 block.2
    · exact beforeBoundary.unready_block_continuationLaw runtime inputs profile wire roster
        reactionRounds before event ready
  · intro before event beforeBoundary beforeAge next member
    by_cases ready : before.native.application.config.cut.Ready event
    · exact (beforeBoundary.ready_event_block runtime inputs feasible profile wire roster
        reactionRounds before beforeAge event ready).2 next member
    · exact (beforeBoundary.unready_block runtime inputs profile wire roster reactionRounds
        before event ready).2 next member
  · intro before event beforeBoundary beforeAge ready next member
    have block := beforeBoundary.ready_event_block runtime inputs feasible profile wire roster
      reactionRounds before beforeAge event ready
    have supported : next.native.application.config ∈
        (graph.normalizedPolicyStep profile before.native.application.config event
          ready).support := by
      rw [← block.1, FinDist.support_map]
      exact ⟨next, member, rfl⟩
    rw [graph.normalizedPolicyStep_cut profile _ event ready _ supported]
    exact Finset.mem_insert_self _ _

end Vegas.EventGraphRuntime
