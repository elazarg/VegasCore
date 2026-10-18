/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingHelperEligiblePrefix
import Vegas.Examples.CommitSeedSignallingOriginalCalendar
import Vegas.Examples.CommitSeedSignallingCorrectSeedProbability
import Vegas.Examples.CommitSeedSignallingLateBeliefs
import Vegas.Examples.CommitSeedSignallingInformation
import Vegas.Pending.PhaseSeedInclusion
import Vegas.Pending.PhaseReadyResolution
import Interaction.ReactiveRoundTrace

/-! # The actual clock-three callback after a helper clock-two WAIT -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- With the late-three seed, an unsent Alice who literally waits at clock
two reaches her real clock-three callback through two passive commands.
The same future kernels choose her response there; the earlier word is kept. -/
theorem helper_wait_reaches_clock_three (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (fixed : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some alice, execution⟩))
    (bit : seedBits seed alice = true)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 2)
    (unsent : ∀ message ∈ app.outputs (execution.recall alice),
      PhaseCount.event? message.payload ≠ some (originalCoordinate alice))
    (bobAccepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob
      execution)
    (players : Player → app.Policy)
    (covered : ∀ owner past view response, response ∈ (players owner past view).support →
      response ∈ countedMenu.actions owner past view)
    (next : app.Execution)
    (reached : next ∈ (app.runRounds (family seed) players 3
      (execution.respond app alice ⟨none⟩)).support) :
    ∃ before observed action,
      before ∈ (app.runRounds (family seed) players 2
        (execution.respond app alice ⟨none⟩)).support ∧
      observed = completeActivation before alice ∧
      family seed before.environmentRecall (before.observeEnvironment app) =
        PMF.pure (.activate alice) ∧
      Nonempty ((countedMenu.protocol initial horizon (family seed)).Trace
        (some ⟨remaining - 3, some alice, observed⟩)) ∧
      observed.application.SeedRequest alice (originalCoordinate alice) ∧
      observed.application.current.native.clock = 3 ∧
      observed.environmentRecall.length = 10 ∧
      observed.recall alice = (execution.respond app alice ⟨none⟩).recall alice ∧
      PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob observed ∧
      action ∈ (players alice (observed.recall alice) (observed.observe app alice)).support ∧
      next = observed.respond app alice action := by
  classical
  have raw := countedInRaw.trace initial horizon (family seed) fixed
  have original : execution.application.attempt = originalAttempt := request.1.symm
  have count := original_first_late_input_index seed ⟨remaining, some alice, execution⟩ raw
    alice rfl original clock
  change execution.environmentRecall.length = 4 + if seedBits seed alice then 3 else 1 at count
  rw [bit] at count
  change execution.environmentRecall.length = 7 at count
  have offered : (⟨none⟩ : app.Action) ∈ countedMenu.actions alice (execution.recall alice)
      (execution.observe app alice) := PhaseCount.silence_onePacket runtime leaks bounds _ _ _
  obtain ⟨repliedTrace⟩ := countedMenu.trace_respond initial horizon (family seed) remaining
    execution alice ⟨none⟩ fixed offered
  let replied := execution.respond app alice ⟨none⟩
  have repliedRaw := countedMenu.toRawTrace initial horizon (family seed) repliedTrace
  have words := PhaseSeedScheduler.idle_wordRecall_of_trace runtime leaks countedMenu initial
    horizon (family seed) remaining replied repliedTrace
  have recalled := app.history_inputRecall initial horizon (family seed) repliedRaw
  have sameOutputs : app.outputs (replied.recall alice) = app.outputs (execution.recall alice) := by
    rw [respond_originalResponseEntry]
    simp only [ReactiveApplication.outputs, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil, originalResponseEntry, Option.map_none, List.append_nil]
  have empty : (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate alice) alice
      replied.environmentRecall (replied.observeEnvironment app)).emissions = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro emission member
    obtain ⟨input, authored, addressed, named⟩ := PhaseSeedScheduler.localInput_emission_authentic
      runtime leaks replied (originalCoordinate alice) alice words recalled emission.1 emission.2
        member
    have output : emission.2 ∈ app.outputs (replied.recall alice) := by
      rw [← recalled alice]
      exact List.mem_filter.mpr ⟨input, by simp only [authored, decide_true]⟩
    rw [sameOutputs] at output
    apply unsent emission.2 output
    simp only [PhaseCount.event?, named, Option.map_some, addressed]
  have repliedRequest : replied.application.SeedRequest alice (originalCoordinate alice) :=
    respond_request runtime leaks execution alice ⟨none⟩ alice (originalCoordinate alice) request
  have repliedOriginal : replied.application.attempt = originalAttempt := repliedRequest.1.symm
  have repliedLength : replied.environmentRecall.length = 7 := count
  have firstCommand : family seed replied.environmentRecall (replied.observeEnvironment app) =
      PMF.pure (ReactiveApplication.Command.wait : app.Command) := by
    rw [family_apply, choose_original seed _ _ repliedOriginal, repliedLength]
    change PMF.pure (lateCommand alice (seed.2 (originalAddress alice)) 2 _ _) = _
    simp only [lateCommand, empty, List.find?_nil, ite_self]
  let waited : app.Execution := { replied with environmentRecall := replied.environmentRecall ++
    [⟨replied.observeEnvironment app, .wait⟩] }
  have firstRound : app.round (family seed) players replied = PMF.pure waited := by
    rw [ReactiveApplication.round, firstCommand, PMF.pure_bind, ReactiveApplication.dispatch,
      ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind]
    rfl
  have waitedRequest : waited.application.SeedRequest alice (originalCoordinate alice) :=
    repliedRequest
  have waitedOriginal : waited.application.attempt = originalAttempt := repliedOriginal
  have waitedLength : waited.environmentRecall.length = 8 := by
    change (replied.environmentRecall ++ [_]).length = 8
    rw [List.length_append, List.length_singleton, repliedLength]
  have accounted := (countedMenu.roundSupported_uniform initial horizon (family seed)
    repliedTrace).1
  have enough : 3 ≤ remaining := by
    rw [repliedLength] at accounted
    change 7 + remaining = 64 at accounted
    omega
  have startTrace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨(remaining - 1) + 1, none, replied⟩) := by
    rw [show remaining - 1 + 1 = remaining by omega]
    exact repliedTrace
  have waitedSupport : waited ∈ (app.round (family seed) players replied).support := by
    rw [firstRound]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  obtain ⟨waitedTrace⟩ := countedMenu.trace_round initial horizon (family seed) players covered
    (remaining - 1) replied waited startTrace waitedSupport
  have advance : family seed waited.environmentRecall (waited.observeEnvironment app) =
      PMF.pure (.application .advanceClock) := by
    rw [family_apply, choose_original seed _ _ waitedOriginal, waitedLength]
    rfl
  rw [show 3 = 2 + 1 by decide, app.runRounds_add, PMF.support_bind] at reached
  obtain ⟨before, preceding, following⟩ := Set.mem_iUnion₂.mp reached
  have advanceSupport : before ∈ (app.round (family seed) players waited).support := by
    change before ∈ ((app.round (family seed) players replied).bind
      (app.runRounds (family seed) players 1)).support at preceding
    rw [firstRound, PMF.pure_bind] at preceding
    simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using preceding
  have beforeReached : before ∈ (app.runRounds (family seed) players 2 replied).support := by
    rw [ReactiveApplication.runRounds, firstRound, PMF.pure_bind]
    simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using advanceSupport
  have beforeTraceStart : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨(remaining - 2) + 2, none, replied⟩) := by
    rw [show remaining - 2 + 2 = remaining by omega]
    exact repliedTrace
  obtain ⟨beforeTrace⟩ := countedMenu.trace_runRounds initial horizon (family seed) players covered
    (remaining - 2) 2 replied before beforeTraceStart beforeReached
  have beforeLength : before.environmentRecall.length = 9 := by
    have length := app.runRounds_environmentRecall_length (family seed) players 2 replied before
      beforeReached
    rw [repliedLength] at length
    exact length
  have advanced := advanceSupport
  rw [ReactiveApplication.round, advance, PMF.pure_bind] at advanced
  obtain ⟨updated, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ advanced)
  simp only [ReactiveApplication.resume, ReactiveApplication.Command.actor?,
    PMF.mem_support_pure_iff] at resumed
  subst before
  have valid := raw_native_valid (family seed) ⟨remaining - 1, none, waited⟩
    (countedMenu.toRawTrace initial horizon (family seed) waitedTrace)
  have preserved := environment_request_or_own_resolution runtime leaks
    (serviceGraph_revealRelaxedOrdered setup .concurrentReveals) waited updated valid alice
      (originalCoordinate alice) waitedRequest (.application .advanceClock) moved
  have beforeRequest : updated.application.SeedRequest alice (originalCoordinate alice) := by
    rcases preserved with retained | expired | included
    · exact retained
    · cases expired
    · obtain ⟨_identifier, _message, _native, _ready, _action, impossible, _rest⟩ := included
      cases impossible
  have beforeOriginal : updated.application.attempt = originalAttempt := beforeRequest.1.symm
  have beforeValid := raw_native_valid (family seed) ⟨remaining - 2, none, updated⟩
    (countedMenu.toRawTrace initial horizon (family seed) beforeTrace)
  have readyEq : ready alice aliceBinding (updated.observeEnvironment app) = true := by
    apply decide_eq_true
    have visible := (updated.application.requests_publicView beforeValid alice
      (originalCoordinate alice)).mpr beforeRequest
    change PhaseRuntimeState.requests updated.application.publicView alice
      ⟨updated.application.attempt, aliceBinding⟩
    simpa only [beforeOriginal, originalCoordinate, bindingEvent, ite_true] using visible
  have nextCommand : family seed updated.environmentRecall (updated.observeEnvironment app) =
      PMF.pure (.activate alice) := by
    rw [family_apply, choose_original seed _ _ beforeOriginal, beforeLength]
    change PMF.pure (activateReady alice aliceBinding _) = _
    simp only [activateReady, readyEq, ite_true]
  have nextRound : next ∈ (app.round (family seed) players updated).support := by
    simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using following
  rw [ReactiveApplication.round, nextCommand, PMF.pure_bind, ReactiveApplication.dispatch,
    completeActivation_law, PMF.pure_bind] at nextRound
  obtain ⟨action, chosen, finalEq⟩ := PMF.support_map .. ▸ nextRound
  let observed := completeActivation updated alice
  have observedSupport : observed ∈ (updated.environmentStep app (.activate alice)).support := by
    rw [completeActivation_law]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have budget : remaining - 2 = (remaining - 3) + 1 := by omega
  have beforeNext : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨(remaining - 3) + 1, none, updated⟩) := by
    rw [← budget]
    exact beforeTrace
  obtain ⟨observedTrace⟩ := countedMenu.trace_environment initial horizon (family seed)
    (remaining - 3) updated observed (.activate alice) beforeNext
      (by rw [nextCommand]; exact (PMF.mem_support_pure_iff _ _).mpr rfl) observedSupport
  have observedRequest : observed.application.SeedRequest alice (originalCoordinate alice) :=
    beforeRequest
  have observedClock : observed.application.current.native.clock = 3 := by
    have actual := original_clock_index seed ⟨remaining - 2, none, updated⟩
      (countedMenu.toRawTrace initial horizon (family seed) beforeTrace) beforeOriginal
    rw [beforeLength] at actual
    exact actual
  have observedLength : observed.environmentRecall.length = 10 := by
    change (updated.environmentRecall ++ [_]).length = 10
    rw [List.length_append, List.length_singleton, beforeLength]
  have observedRecall : observed.recall alice = replied.recall alice := by
    change updated.recall alice = replied.recall alice
    rw [app.environmentStep_recall waited updated (.application .advanceClock) moved]
  have replyBob : PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob replied :=
    bobAccepted
  have beforeBob := original_binding_accepted_runRounds (family seed) players 2 replied updated
    beforeReached bob replyBob
  have observedBob : PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob
      observed := by
    obtain ⟨message, member, authored, tagged, named, receipted⟩ := beforeBob
    exact ⟨message, member, authored, tagged, named, receipted⟩
  exact ⟨updated, observed, action, beforeReached, rfl, nextCommand, ⟨observedTrace⟩,
    observedRequest,
    observedClock, observedLength, observedRecall, observedBob, chosen, finalEq.symm⟩

end Vegas.Examples.CommitSeedSignalling
