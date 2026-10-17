/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingLateBeliefs
import Vegas.Examples.CommitSeedSignallingDelivery
import Interaction.ReactiveResponseAccounting
import Vegas.Pending.PhaseSeedEmissionUnique
import GameTheoryExtensions.Math.Probability.Expectation

/-! # One original packet across the two hidden late polling positions -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob)

private theorem transition_environment_prefix (seed : Seeds) (before : app.Control)
    (after : app.ProtocolState) (joint : Player → Option app.Action)
    (reached : after ∈ (app.transition initial horizon (family seed) (some before)
      joint).support) :
    ∃ next, after = some next ∧ before.execution.environmentRecall <+:
      next.execution.environmentRecall := by
  rcases before with ⟨remaining, actor, execution⟩
  cases actor with
  | some owner =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨_, rfl, by rw [app.respond_environmentRecall]⟩
  | none =>
      cases remaining with
      | zero =>
          cases (PMF.mem_support_pure_iff _ _).mp reached
          exact ⟨_, rfl, List.prefix_refl _⟩
      | succ remaining =>
          obtain ⟨command, _chosen, moved⟩ :=
            Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
          obtain ⟨next, environmentMoved, rfl⟩ := PMF.support_map .. ▸ moved
          exact ⟨_, rfl, ⟨_, (app.environmentStep_environmentRecall execution next
            command environmentMoved).symm⟩⟩

theorem tracePrefix_environment_prefix (seed : Seeds) (before after : app.Control)
    (first : (rawMenu.protocol initial horizon (family seed)).Trace (some before))
    (last : (rawMenu.protocol initial horizon (family seed)).Trace (some after))
    (retained : TracePrefix first last) :
    before.execution.environmentRecall <+: after.execution.environmentRecall := by
  have path := retained.reachesWithin
  suffices ∀ {fuel first last},
      (rawMenu.protocol initial horizon (family seed)).ReachesWithin fuel first last →
      ∀ before after : app.Control, first.state = some before → last.state = some after →
        before.execution.environmentRecall <+: after.execution.environmentRecall by
    exact this path before after rfl rfl
  intro fuel first last reached
  induction reached with
  | refl _ history =>
      intro before after firstEq lastEq
      cases Option.some.inj (firstEq.symm.trans lastEq)
      rfl
  | @step steps history target joint legal realized supported suffix ih =>
      intro before after firstEq lastEq
      have moved := supported
      change realized ∈ (app.transition initial horizon (family seed) history.state
        joint).support at moved
      rw [firstEq] at moved
      obtain ⟨middle, middleEq, retained⟩ :=
        transition_environment_prefix seed before realized joint moved
      exact retained.trans (ih middle after middleEq lastEq)

private theorem equal_prefixes {α : Type*} (first second last : List α)
    (left : first <+: last) (right : second <+: last)
    (length : first.length = second.length) : first = second := by
  obtain ⟨rest, leftEq⟩ := left
  obtain ⟨later, rightEq⟩ := right
  have same := congrArg (List.take first.length) (leftEq.trans rightEq.symm)
  have leftTake : List.take first.length (first ++ rest) = first := by
    simp only [List.take_left]
  have rightTake : List.take first.length (second ++ later) = second := by
    rw [length, List.take_left]
  rwa [leftTake, rightTake] at same

/-- Two active prefixes of one actual history with the same command count
have the same number of completed own responses. -/
private theorem active_prefix_recall_length (seed : Seeds) (current left right : app.Control)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace (some current))
    (leftTrace : (rawMenu.protocol initial horizon (family seed)).Trace (some left))
    (rightTrace : (rawMenu.protocol initial horizon (family seed)).Trace (some right))
    (leftPrefix : TracePrefix leftTrace trace) (rightPrefix : TracePrefix rightTrace trace)
    (owner : Player) (leftActive : left.actor = some owner)
    (rightActive : right.actor = some owner)
    (position : left.execution.environmentRecall.length =
      right.execution.environmentRecall.length) :
    (left.execution.recall owner).length = (right.execution.recall owner).length := by
  have same := equal_prefixes _ _ _
    (tracePrefix_environment_prefix seed left current leftTrace trace leftPrefix)
    (tracePrefix_environment_prefix seed right current rightTrace trace rightPrefix) position
  have leftCount := app.response_count_history initial horizon (family seed) left
    (rawMenu.toRawTrace initial horizon (family seed) leftTrace) owner
  have rightCount := app.response_count_history initial horizon (family seed) right
    (rawMenu.toRawTrace initial horizon (family seed) rightTrace) owner
  simp only [leftActive, ite_true] at leftCount
  simp only [rightActive, ite_true] at rightCount
  have sameActivations : app.activationHistory left.execution =
      app.activationHistory right.execution := congrArg (fun past : List app.EnvironmentEntry =>
        past.filterMap (fun entry : app.EnvironmentEntry => entry.command.actor? app)) same
  rw [sameActivations] at leftCount
  omega

/-- The single first-late callback has only one retained response record,
regardless of subsequent raw actions, phase retirement or retries. -/
theorem original_first_late_response_unique (seed : Seeds) (current : app.Control)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace (some current))
    (owner : Player) (first second : app.PlayerEntry)
    (firstRecorded : first ∈ current.execution.recall owner)
    (secondRecorded : second ∈ current.execution.recall owner)
    (firstOriginal : first.beforeView.application.2.attempt = originalAttempt)
    (secondOriginal : second.beforeView.application.2.attempt = originalAttempt)
    (firstClock : first.beforeView.application.2.native.clock = lateClock owner false)
    (secondClock : second.beforeView.application.2.native.clock = lateClock owner false) :
    first = second := by
  obtain ⟨left, leftTrace, leftPrefix, leftActive, leftView, _legal, later, leftRecall⟩ :=
    rawMenu.recorded_response_prefix initial horizon (family seed) current trace
      owner first firstRecorded
  obtain ⟨right, rightTrace, rightPrefix, rightActive, rightView, _legal, rest, rightRecall⟩ :=
    rawMenu.recorded_response_prefix initial horizon (family seed) current trace
      owner second secondRecorded
  have firstIndex := original_first_late_input_index seed left leftTrace owner leftActive
    (by rw [leftView] at firstOriginal; exact firstOriginal)
    (by rw [leftView] at firstClock; exact firstClock)
  have secondIndex := original_first_late_input_index seed right rightTrace owner rightActive
    (by rw [rightView] at secondOriginal; exact secondOriginal)
    (by rw [rightView] at secondClock; exact secondClock)
  have sameLength := active_prefix_recall_length seed current left right trace leftTrace
    rightTrace leftPrefix rightPrefix owner leftActive rightActive
      (firstIndex.trans secondIndex.symm)
  have leftEntry : (current.execution.recall owner)[(left.execution.recall owner).length]? =
      some first := by
    rw [leftRecall, List.getElem?_append_right (by omega)]
    simp only [Nat.sub_self, List.getElem?_cons_zero]
  have rightEntry : (current.execution.recall owner)[(left.execution.recall owner).length]? =
      some second := by
    rw [sameLength, rightRecall, List.getElem?_append_right (by omega)]
    simp only [Nat.sub_self, List.getElem?_cons_zero]
  exact Option.some.inj (leftEntry.symm.trans rightEntry)

private theorem runRounds_recall_prefix (seed : Seeds) (players : Player → app.Policy)
    (count : Nat) (execution final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players count execution).support)
    (owner : Player) : execution.recall owner <+: final.recall owner := by
  let invariant : app.ServiceInvariant (family seed)
      (fun next => execution.recall owner <+: next.recall owner) := {
    respond := fun next acting action retained =>
      retained.trans (app.respond_recall_prefix next acting owner action)
    environment := fun next after command retained _ moved => by
      rw [app.environmentStep_recall next after command moved]
      exact retained }
  exact invariant.runRounds players count execution final (List.prefix_refl _) reached

private theorem idle_wordRecall (seed : Seeds) (remaining : Nat) (execution : app.Execution)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩)) :
    PhaseSeedScheduler.WordRecall runtime leaks execution := by
  obtain ⟨_accounted, supported⟩ := rawMenu.roundSupported_uniform initial horizon
    (family seed) trace
  change execution ∈ (app.roundsFrom initial (family seed) rawMenu.uniformResponses
    execution.environmentRecall.length).support at supported
  rw [ReactiveApplication.roundsFrom, initial_eq_pure, PMF.pure_bind] at supported
  exact PhaseSeedScheduler.runRounds_wordRecall runtime leaks (family seed)
    rawMenu.uniformResponses execution.environmentRecall.length initialExecution execution
    (PhaseSeedScheduler.initial_wordRecall runtime leaks initialState) supported

/-- The envelope in the actual atomic submit/response transition. -/
def originalResponseEntry (execution : app.Execution) (owner : Player)
    (action : app.Action) : app.PlayerEntry :=
  ⟨execution.observe app owner, action, action.transmission.map fun material =>
    (execution.network.submit owner (app.packet
      (app.submit execution.application owner material) owner
      (execution.network.known owner) material)).1⟩

theorem respond_originalResponseEntry (execution : app.Execution) (owner : Player)
    (action : app.Action) :
    (execution.respond app owner action).recall owner = execution.recall owner ++
      [originalResponseEntry execution owner action] := by
  rcases action with ⟨transmission⟩
  cases transmission <;> simp [ReactiveApplication.Execution.respond, originalResponseEntry]

theorem pollDelay_originalResponseEntry (execution : app.Execution) (owner : Player)
    (action : app.Action) :
    originalResponseEntry (completeActivation (pollDelay execution) owner) owner action =
      originalResponseEntry (completeActivation execution owner) owner action := by
  rfl

private theorem response_entry_retained (seed : Seeds) (players : Player → app.Policy)
    (owner : Player) (execution : app.Execution) (action : app.Action) (count : Nat)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players count
      (execution.respond app owner action)).support) :
    originalResponseEntry execution owner action ∈ final.recall owner := by
  apply (runRounds_recall_prefix seed players count _ final reached owner).sublist.subset
  rw [respond_originalResponseEntry]
  exact List.mem_append_right _ (List.mem_singleton_self _)

private theorem retained_emission (seed : Seeds) (remaining : Nat) (execution : app.Execution)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player) (entry : app.PlayerEntry)
    (message : Message Player (CommitAttemptPacket graph))
    (recorded : entry ∈ execution.recall owner)
    (requested : PhaseRuntimeState.requests entry.beforeView.application.2 owner
      (originalCoordinate owner))
    (clock : entry.beforeView.application.2.native.clock -
      (entry.beforeView.application.2.native.activatedAt (bindingEvent owner)).getD
        entry.beforeView.application.2.native.clock = lateClock owner false)
    (emitted : entry.emitted = some message)
    (packet : PhaseSeedScheduler.ownPacket (originalCoordinate owner) owner message = true) :
    (lateClock owner false, message) ∈
      (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
        execution.environmentRecall (execution.observeEnvironment app)).emissions := by
  classical
  rw [PhaseSeedScheduler.localInput_word,
    idle_wordRecall seed remaining execution trace owner (originalCoordinate owner)]
  apply List.mem_flatMap.mpr
  refine ⟨(lateClock owner false, [message]), ?_, ?_⟩
  · apply List.mem_map.mpr
    refine ⟨entry, List.mem_filter.mpr ⟨recorded, decide_eq_true requested⟩, ?_⟩
    change (entry.beforeView.application.2.native.clock -
      (entry.beforeView.application.2.native.activatedAt (bindingEvent owner)).getD
        entry.beforeView.application.2.native.clock,
      entry.emitted.toList.filter
        (PhaseSeedScheduler.ownPacket (originalCoordinate owner) owner)) =
      (lateClock owner false, [message])
    rw [clock, emitted]
    simp only [Option.toList_some, List.filter_cons, packet, ite_true, List.filter_nil]
  · exact List.mem_map.mpr ⟨message, List.mem_singleton_self _, rfl⟩

private theorem localInput_ownPacket (coordinate : CommitAttemptEvent graph) (owner : Player)
    (execution : app.Execution) (clock : Nat) (message : Message Player (CommitAttemptPacket graph))
    (emitted : (clock, message) ∈ (PhaseSeedScheduler.localInput runtime leaks coordinate owner
      execution.environmentRecall (execution.observeEnvironment app)).emissions) :
    PhaseSeedScheduler.ownPacket coordinate owner message = true := by
  rw [PhaseSeedScheduler.localInput_word, PhaseSeedScheduler.word] at emitted
  obtain ⟨record, recorded, member⟩ := List.mem_flatMap.mp emitted
  obtain ⟨pair, _selected, pairEq⟩ := List.mem_map.mp recorded
  subst record
  obtain ⟨actual, member, pairEq⟩ := List.mem_map.mp member
  obtain ⟨_input, packet⟩ := List.mem_filter.mp member
  have actualEq : actual = message := congrArg Prod.snd pairEq
  subst actual
  exact packet

private theorem emissions_eq_of_one (emissions : List (Nat × Message Player
    (CommitAttemptPacket graph))) (one : emissions.length ≤ 1)
    (first second : Nat × Message Player (CommitAttemptPacket graph))
    (firstMember : first ∈ emissions) (secondMember : second ∈ emissions) : first = second := by
  cases emissions with
  | nil => exact (List.not_mem_nil firstMember).elim
  | cons head rest =>
      cases rest with
      | nil =>
          exact (List.mem_singleton.mp firstMember).trans
            (List.mem_singleton.mp secondMember).symm
      | cons next rest =>
          simp only [List.length_cons] at one
          omega

/-- Coupled actual late continuations with the same first response cannot
both accept the original binding when the true-bit path has only one packet.
The two paths may have arbitrary, different subsequent response histories. -/
theorem original_nohelper_acceptances_incompatible
    (falseSeed trueSeed : Seeds) (players : Player → app.Policy) (owner : Player)
    (execution : app.Execution) (action : app.Action)
    (falseBit : seedBits falseSeed owner = false) (trueBit : seedBits trueSeed owner = true)
    (original : execution.application.attempt = originalAttempt)
    (clock : execution.application.current.native.clock = lateClock owner false)
    (timer : execution.application.current.native.activatedAt (bindingEvent owner) = some 0)
    (requested : PhaseRuntimeState.requests execution.application.publicView owner
      (originalCoordinate owner))
    (falseRemaining trueRemaining falseCount trueCount : Nat)
    (falseFinal trueFinal : app.Execution)
    (falseTrace : (rawMenu.protocol initial horizon (family falseSeed)).Trace
      (some ⟨falseRemaining, none, falseFinal⟩))
    (trueTrace : (rawMenu.protocol initial horizon (family trueSeed)).Trace
      (some ⟨trueRemaining, none, trueFinal⟩))
    (falseReached : falseFinal ∈ (app.runRounds (family falseSeed) players falseCount
      ((completeActivation execution owner).respond app owner action)).support)
    (trueReached : trueFinal ∈ (app.runRounds (family trueSeed) players trueCount
      ((completeActivation (pollDelay execution) owner).respond app owner action)).support)
    (falseEmpty : ∀ entry, falseFinal.environmentRecall[2]? = some entry →
      ∀ message ∈ entry.beforeView.network.inputs, message.sender ≠ owner)
    (trueEmpty : ∀ entry, trueFinal.environmentRecall[2]? = some entry →
      ∀ message ∈ entry.beforeView.network.inputs, message.sender ≠ owner)
    (one : (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
      trueFinal.environmentRecall (trueFinal.observeEnvironment app)).emissions.length ≤ 1) :
    ¬ (PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner falseFinal ∧
      PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner trueFinal) := by
  intro accepted
  obtain ⟨firstMessage, firstEmission⟩ := original_binding_accepted_late_of_empty_snapshot
    falseSeed falseRemaining falseFinal falseTrace owner falseEmpty accepted.1
  have firstClock : falseSeed.2 (originalAddress owner) = false := falseBit
  rw [firstClock] at firstEmission
  obtain ⟨entry, before, prior, recorded, envelope, _retained, _acting, observed,
    beforeOriginal, beforeClock, _position⟩ := original_first_late_emission falseSeed
      falseRemaining falseFinal falseTrace owner firstMessage firstEmission
  let firstEntry := originalResponseEntry (completeActivation execution owner) owner action
  have firstRecorded : firstEntry ∈ falseFinal.recall owner :=
    response_entry_retained falseSeed players owner _ action falseCount falseFinal falseReached
  have firstOriginal : firstEntry.beforeView.application.2.attempt = originalAttempt := original
  have firstTime : firstEntry.beforeView.application.2.native.clock = lateClock owner false := clock
  have entryOriginal : entry.beforeView.application.2.attempt = originalAttempt := by
    rw [observed]
    exact beforeOriginal
  have entryClock : entry.beforeView.application.2.native.clock = lateClock owner false := by
    rw [observed]
    exact beforeClock
  have sameEntry := original_first_late_response_unique falseSeed
    ⟨falseRemaining, none, falseFinal⟩ falseTrace owner firstEntry entry firstRecorded recorded
      firstOriginal entryOriginal firstTime entryClock
  have firstEnvelope : firstEntry.emitted = some firstMessage := by
    rw [sameEntry]
    exact envelope
  have trueRecorded : firstEntry ∈ trueFinal.recall owner := by
    have retained := response_entry_retained trueSeed players owner _ action trueCount
      trueFinal trueReached
    rwa [pollDelay_originalResponseEntry] at retained
  have firstPacket := localInput_ownPacket (originalCoordinate owner) owner falseFinal
    (lateClock owner false) firstMessage firstEmission
  have trueFirst : (lateClock owner false, firstMessage) ∈
      (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
        trueFinal.environmentRecall (trueFinal.observeEnvironment app)).emissions := by
    apply retained_emission trueSeed trueRemaining trueFinal trueTrace owner firstEntry
      firstMessage trueRecorded requested _ firstEnvelope firstPacket
    change execution.application.current.native.clock -
      (execution.application.current.native.activatedAt (bindingEvent owner)).getD
        execution.application.current.native.clock = lateClock owner false
    rw [timer, Option.getD_some, Nat.sub_zero, clock]
  obtain ⟨secondMessage, secondEmission⟩ := original_binding_accepted_late_of_empty_snapshot
    trueSeed trueRemaining trueFinal trueTrace owner trueEmpty accepted.2
  have secondClock : trueSeed.2 (originalAddress owner) = true := trueBit
  rw [secondClock] at secondEmission
  have same := emissions_eq_of_one _ one _ _ trueFirst secondEmission
  have sameClock := congrArg Prod.fst same
  simp only [lateClock, Bool.false_eq_true, ite_false, ite_true, Nat.add_zero] at sameClock
  omega

/-- Averaging the two original seed bits bounds actual late acceptance by a
half. Legality and the one-packet restriction concern supported continuations,
so no restriction is placed on the policy at unrelated full native inputs. -/
theorem original_nohelper_acceptance_half
    (falseSeed trueSeed : Seeds) (players : Player → app.Policy) (owner : Player)
    (extra : Nat) (execution : app.Execution)
    (falseBit : seedBits falseSeed owner = false) (trueBit : seedBits trueSeed owner = true)
    (original : execution.application.attempt = originalAttempt)
    (position : execution.environmentRecall.length = firstLatePosition owner)
    (clock : execution.application.current.native.clock = lateClock owner false)
    (timer : execution.application.current.native.activatedAt (bindingEvent owner) = some 0)
    (requested : ready owner (bindingEvent owner) (execution.observeEnvironment app) = true)
    (noHelper : earlyCommand (markerOwner owner) execution.environmentRecall
      (execution.observeEnvironment app) = .wait)
    (falseLegal : ∀ final ∈ (app.runRounds (family falseSeed) players (extra + 3)
        execution).support,
      Nonempty ((rawMenu.protocol initial horizon (family falseSeed)).Trace
        (some ⟨0, none, final⟩)))
    (trueLegal : ∀ final ∈ (app.runRounds (family trueSeed) players (extra + 3)
        execution).support,
      Nonempty ((rawMenu.protocol initial horizon (family trueSeed)).Trace
        (some ⟨0, none, final⟩)))
    (falseEmpty : ∀ final ∈ (app.runRounds (family falseSeed) players (extra + 3)
        execution).support,
      ∀ entry, final.environmentRecall[2]? = some entry →
        ∀ message ∈ entry.beforeView.network.inputs, message.sender ≠ owner)
    (trueEmpty : ∀ final ∈ (app.runRounds (family trueSeed) players (extra + 3)
        execution).support,
      ∀ entry, final.environmentRecall[2]? = some entry →
        ∀ message ∈ entry.beforeView.network.inputs, message.sender ≠ owner)
    (one : ∀ final ∈ (app.runRounds (family trueSeed) players (extra + 3) execution).support,
      (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
        final.environmentRecall (final.observeEnvironment app)).emissions.length ≤ 1) :
    (((app.runRounds (family falseSeed) players (extra + 3) execution).toOuterMeasure
        {final | PhaseService.BindingAccepted runtime leaks (originalCoordinate owner)
          owner final}).toReal +
      ((app.runRounds (family trueSeed) players (extra + 3) execution).toOuterMeasure
        {final | PhaseService.BindingAccepted runtime leaks (originalCoordinate owner)
          owner final}).toReal) / 2 ≤ 1 / 2 := by
  classical
  let event : Set app.Execution := {final |
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner final}
  let responses := players owner ((completeActivation execution owner).recall owner)
    ((completeActivation execution owner).observe app owner)
  let falseKernel := fun action : app.Action =>
    app.runRounds (family falseSeed) players (extra + 2)
      ((completeActivation execution owner).respond app owner action)
  let trueKernel := fun action : app.Action =>
    app.runRounds (family trueSeed) players extra
      ((completeActivation (pollDelay execution) owner).respond app owner action)
  have falseSplit : app.runRounds (family falseSeed) players (extra + 3) execution =
      responses.bind falseKernel := by
    simpa only [falseBit, Bool.false_eq_true, ite_false] using
      nohelper_first_response_rounds falseSeed players owner extra execution
        original position requested noHelper
  have trueSplit : app.runRounds (family trueSeed) players (extra + 3) execution =
      responses.bind trueKernel := by
    simpa only [trueBit, ite_true] using
      nohelper_first_response_rounds trueSeed players owner extra execution
        original position requested noHelper
  have falseWhole (action : app.Action) (chosen : action ∈ responses.support)
      (final : app.Execution) (reached : final ∈ (falseKernel action).support) :
      final ∈ (app.runRounds (family falseSeed) players (extra + 3) execution).support := by
    rw [falseSplit, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨action, chosen, reached⟩
  have trueWhole (action : app.Action) (chosen : action ∈ responses.support)
      (final : app.Execution) (reached : final ∈ (trueKernel action).support) :
      final ∈ (app.runRounds (family trueSeed) players (extra + 3) execution).support := by
    rw [trueSplit, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨action, chosen, reached⟩
  have request : PhaseRuntimeState.requests execution.application.publicView owner
      (originalCoordinate owner) := by
    have actual := requested
    change decide (PhaseRuntimeState.requests execution.application.publicView owner
      ⟨execution.application.attempt, bindingEvent owner⟩) = true at actual
    have actual := of_decide_eq_true actual
    rwa [original] at actual
  have incompatible (action : app.Action) (chosen : action ∈ responses.support)
      (falseFinal trueFinal : app.Execution)
      (falseReached : falseFinal ∈ (falseKernel action).support)
      (trueReached : trueFinal ∈ (trueKernel action).support) :
      ¬ (falseFinal ∈ event ∧ trueFinal ∈ event) := by
    have falseSupported := falseWhole action chosen falseFinal falseReached
    have trueSupported := trueWhole action chosen trueFinal trueReached
    obtain ⟨falseTrace⟩ := falseLegal falseFinal falseSupported
    obtain ⟨trueTrace⟩ := trueLegal trueFinal trueSupported
    exact original_nohelper_acceptances_incompatible falseSeed trueSeed players owner execution
      action falseBit trueBit original clock timer request 0 0 (extra + 2) extra
      falseFinal trueFinal falseTrace trueTrace falseReached trueReached
      (falseEmpty falseFinal falseSupported) (trueEmpty trueFinal trueSupported)
      (one trueFinal trueSupported)
  have branchBound (action : app.Action) (chosen : action ∈ responses.support) :
      ((falseKernel action).toOuterMeasure event).toReal +
        ((trueKernel action).toOuterMeasure event).toReal ≤ 1 := by
    by_cases possible : ∃ final ∈ (falseKernel action).support, final ∈ event
    · obtain ⟨falseFinal, falseReached, accepted⟩ := possible
      have zero : (trueKernel action).toOuterMeasure event = 0 := by
        by_contra positive
        obtain ⟨trueFinal, acceptedTrue, trueReached⟩ :=
          (toOuterMeasure_ne_zero_iff (trueKernel action) event).mp positive
        exact incompatible action chosen falseFinal trueFinal falseReached trueReached
          ⟨accepted, acceptedTrue⟩
      rw [zero, ENNReal.toReal_zero, add_zero]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one
        (by simpa using outerMeasure_le_one (falseKernel action) event)
    · have zero : (falseKernel action).toOuterMeasure event = 0 := by
        by_contra positive
        obtain ⟨final, accepted, reached⟩ :=
          (toOuterMeasure_ne_zero_iff (falseKernel action) event).mp positive
        exact possible ⟨final, reached, accepted⟩
      rw [zero, ENNReal.toReal_zero, zero_add]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one
        (by simpa using outerMeasure_le_one (trueKernel action) event)
  have falseIntegrable := payoffIntegrable_toReal_toOuterMeasure responses falseKernel event
  have trueIntegrable := payoffIntegrable_toReal_toOuterMeasure responses trueKernel event
  have averaged := expect_mono branchBound (payoffIntegrable_add falseIntegrable trueIntegrable)
    (payoffIntegrable_constant responses 1)
  rw [expect_add falseIntegrable trueIntegrable, expect_constant] at averaged
  change (((app.runRounds (family falseSeed) players (extra + 3) execution).toOuterMeasure
    event).toReal + ((app.runRounds (family trueSeed) players (extra + 3)
      execution).toOuterMeasure event).toReal) / 2 ≤ 1 / 2
  rw [falseSplit, trueSplit, toReal_toOuterMeasure_bind, toReal_toOuterMeasure_bind]
  linarith

end Vegas.Examples.CommitSeedSignalling
