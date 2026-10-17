/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingBeliefs
import Vegas.Examples.CommitSeedSignallingContract
import Vegas.Pending.PhaseSeedRecall
import Interaction.ReactiveSchedulerPrefix
import Interaction.ReactiveRecordedRounds
import Interaction.ReactiveRecordedResponse

/-! # The original unread Bob seed before the late polling block -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob)

def quietAfterTwo : app.Execution := (bobFirst ⟨none⟩).respond app bob ⟨none⟩

theorem quietAfterTwo_environmentRecall : quietAfterTwo.environmentRecall =
    [⟨initialExecution.observeEnvironment app, .activate alice⟩,
      ⟨(aliceResponded ⟨none⟩).observeEnvironment app, .activate bob⟩] := by
  rw [quietAfterTwo, app.respond_environmentRecall, bobFirst_environmentRecall]

theorem quietAfterTwo_inputs : quietAfterTwo.network.inputs = [] := by
  change (bobFirst ⟨none⟩).network.inputs = []
  rw [bobFirst_quiet_network]
  rfl

theorem quiet_first_two_rounds (players : Player → app.Policy) (seed : Seeds)
    (aliceWait : players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩)
    (bobWait : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩) :
    app.runRounds (family seed) players 2 initialExecution = PMF.pure quietAfterTwo := by
  have firstRound : app.round (family seed) players initialExecution =
      PMF.pure (aliceResponded ⟨none⟩) := by
    rw [first_round, aliceWait, PMF.pure_map]
  have secondRound : app.round (family seed) players (aliceResponded ⟨none⟩) =
      PMF.pure quietAfterTwo := by
    rw [ReactiveApplication.round, family_after_alice, PMF.pure_bind,
      ReactiveApplication.dispatch, completeActivation_law, PMF.pure_bind]
    change (players bob ((bobFirst ⟨none⟩).recall bob)
      ((bobFirst ⟨none⟩).observe app bob)).map ((bobFirst ⟨none⟩).respond app bob) = _
    rw [bobFirst_recall, bobWait, PMF.pure_map]
    rfl
  rw [ReactiveApplication.runRounds, firstRound, PMF.pure_bind,
    ReactiveApplication.runRounds, secondRound, PMF.pure_bind, ReactiveApplication.runRounds]

/-- The real third command's before-view permanently records that both first
responses were silent. Later pending traffic cannot become an EARLY marker. -/
theorem quiet_prefix_snapshot (players : Player → app.Policy) (seed : Seeds)
    (aliceWait : players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩)
    (bobWait : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩)
    (extra : Nat) (execution : app.Execution)
    (reached : execution ∈ (app.runRounds (family seed) players (3 + extra)
      initialExecution).support) :
    ∀ entry, execution.environmentRecall[2]? = some entry →
      entry.beforeView.network.inputs = [] := by
  rw [show 3 + extra = 2 + (extra + 1) by omega,
    app.runRounds_add, quiet_first_two_rounds players seed aliceWait bobWait,
    PMF.pure_bind, ReactiveApplication.runRounds] at reached
  obtain ⟨middle, moved, tail⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨command, _, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
  obtain ⟨later, recalled, _⟩ :=
    app.runRounds_environmentRecall_append (family seed) players extra middle execution tail
  have complete : execution.environmentRecall = quietAfterTwo.environmentRecall ++
      [⟨quietAfterTwo.observeEnvironment app, command⟩] ++ later := by
    rw [recalled, app.dispatch_environmentRecall players command quietAfterTwo middle dispatched]
  have snapshot : execution.environmentRecall[2]? =
      some ⟨quietAfterTwo.observeEnvironment app, command⟩ := by
    rw [complete, quietAfterTwo_environmentRecall]
    rfl
  intro entry selected
  have equal : entry = ⟨quietAfterTwo.observeEnvironment app, command⟩ :=
    Option.some.inj (selected.symm.trans snapshot)
  subst entry
  exact quietAfterTwo_inputs

/-- A later packet cannot become a helper after both original first responses
were WAIT: the selector reads the immutable actual third-command snapshot. -/
theorem quiet_prefix_earlyCommand (players : Player → app.Policy) (seed : Seeds)
    (aliceWait : players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩)
    (bobWait : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩)
    (extra : Nat) (execution : app.Execution)
    (reached : execution ∈ (app.runRounds (family seed) players (3 + extra)
      initialExecution).support) (owner : Player) :
    earlyCommand owner execution.environmentRecall (execution.observeEnvironment app) = .wait := by
  unfold earlyCommand
  cases selected : execution.environmentRecall[2]? with
  | none => rfl
  | some entry =>
      change (match entry.beforeView.network.inputs.find? (fun message :
          Message Player (CommitAttemptPacket graph) => decide (message.sender = owner ∧
            message.payload.attempt = originalAttempt)) with
        | none => (ReactiveApplication.Command.wait : app.Command)
        | some message => pendingCommand message.id (execution.observeEnvironment app)) =
          ReactiveApplication.Command.wait
      rw [quiet_prefix_snapshot players seed aliceWait bobWait extra execution reached
        entry selected]
      rfl

theorem family_before_alice_congr (first second : Seeds)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) (early : past.length < 4) :
    family first past view = family second past view := by
  unfold family choose
  by_cases original : view.application.attempt = originalAttempt
  · simp only [ite_eq_left original]
    generalize cursor : past.length = position at early ⊢
    interval_cases position <;> rfl
  · simp only [ite_eq_right original]

theorem run_before_alice_seed (players : Player → app.Policy) (count : Nat)
    (early : count ≤ 4) (first second : Seeds) :
    app.runRounds (family first) players count initialExecution =
      app.runRounds (family second) players count initialExecution := by
  apply app.runRounds_eq_of_scheduler_agreement
  intro past view _ upper
  apply family_before_alice_congr first second past view
  change past.length < 0 + count at upper
  omega

/-- The original initialized joint before any seed-dependent Alice polling.
The second component retains the complete original address table. -/
def beforeAliceOriginalJoint (players : Player → app.Policy) (count : Nat) :
    PMF (app.Execution × Seeds) :=
  seedPrior.bind fun seed =>
    (app.runRounds (family seed) players count initialExecution).map fun execution =>
      (execution, seed)

theorem beforeAliceOriginalJoint_eq (players : Player → app.Policy) (count : Nat)
    (early : count ≤ 4) :
    beforeAliceOriginalJoint players count =
      bindPairLaw
        (app.runRounds (family (seedOfBits fun _ => false)) players count initialExecution)
        (fun _ => seedPrior) := by
  unfold beforeAliceOriginalJoint
  simp_rw [run_before_alice_seed players count early _ (seedOfBits fun _ => false)]
  unfold bindPairLaw
  exact PMF.bind_comm ..

abbrev BobSeedRest := {address : PhaseSeedAddress graph // address ≠ originalAddress bob} → Bool

def bobSeedRest (seed : Seeds) : BobSeedRest := fun address => seed.2 address

def joinBobSeed (bit : Bool) (rest : BobSeedRest) : Seeds :=
  ((), (Equiv.piSplitAt (originalAddress bob) (fun _ : PhaseSeedAddress graph => Bool)).symm
    (bit, rest))

def bobSeedRestLaw : PMF BobSeedRest :=
  independentProduct fun address : {address : PhaseSeedAddress graph //
    address ≠ originalAddress bob} => seedLaws address

theorem joinBobSeed_read (bit : Bool) (rest : BobSeedRest) :
    (seedBits (joinBobSeed bit rest) bob, bobSeedRest (joinBobSeed bit rest)) = (bit, rest) := by
  change (Equiv.piSplitAt (originalAddress bob) (fun _ : PhaseSeedAddress graph => Bool))
    ((Equiv.piSplitAt (originalAddress bob) (fun _ : PhaseSeedAddress graph => Bool)).symm
      (bit, rest)) = (bit, rest)
  exact Equiv.apply_symm_apply _ _

theorem joinBobSeed_bit (bit : Bool) (rest : BobSeedRest) :
    seedBits (joinBobSeed bit rest) bob = bit := congrArg Prod.fst (joinBobSeed_read bit rest)

theorem joinBobSeed_rest (bit : Bool) (rest : BobSeedRest) :
    bobSeedRest (joinBobSeed bit rest) = rest := congrArg Prod.snd (joinBobSeed_read bit rest)

theorem joinBobSeed_alice (bit : Bool) (rest : BobSeedRest) :
    seedBits (joinBobSeed bit rest) alice = seedBits (joinBobSeed false rest) alice := by
  have first := congrFun (joinBobSeed_rest bit rest)
    (⟨originalAddress alice, originalAddress_ne⟩ : {address // address ≠ originalAddress bob})
  have second := congrFun (joinBobSeed_rest false rest)
    (⟨originalAddress alice, originalAddress_ne⟩ : {address // address ≠ originalAddress bob})
  exact first.trans second.symm

theorem seedPrior_split_bob : seedPrior =
    (PMF.uniformOfFintype Bool).bind fun bit => bobSeedRestLaw.map (joinBobSeed bit) := by
  unfold seedPrior
  rw [independentProduct_splitAt seedLaws (originalAddress bob)]
  simp only [seedLaws_original, PMF.map_bind, PMF.map_comp, Function.comp_def]
  rfl

theorem family_before_bob_congr (first second : Seeds)
    (same : seedBits first alice = seedBits second alice)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) (early : past.length < 12) :
    family first past view = family second past view := by
  unfold family choose
  by_cases original : view.application.attempt = originalAttempt
  · simp only [ite_eq_left original]
    generalize cursor : past.length = position at early ⊢
    interval_cases position <;>
      simp only [originalCommand, show first.2 (originalAddress alice) =
        second.2 (originalAddress alice) from same]
  · simp only [ite_eq_right original]

/-- The whole physical prefix, including all earlier Alice outcomes and every
raw response, is independent of Bob's still unused original coordinate. -/
theorem run_before_bob_seed (players : Player → app.Policy) (count : Nat) (early : count ≤ 12)
    (bit : Bool) (rest : BobSeedRest) :
    app.runRounds (family (joinBobSeed bit rest)) players count initialExecution =
      app.runRounds (family (joinBobSeed false rest)) players count initialExecution := by
  apply app.runRounds_eq_of_scheduler_agreement
  intro past view _ upper
  exact family_before_bob_congr _ _ (joinBobSeed_alice bit rest) past view (by
    change past.length < 0 + count at upper
    omega)

def beforeBobOriginalJoint (players : Player → app.Policy) (count : Nat) :
    PMF (Bool × (app.Execution × BobSeedRest)) :=
  seedPrior.bind fun seed =>
    (app.runRounds (family seed) players count initialExecution).map fun execution =>
      (seedBits seed bob, execution, bobSeedRest seed)

def beforeBobRemainderLaw (players : Player → app.Policy) (count : Nat) :
    PMF (app.Execution × BobSeedRest) :=
  bobSeedRestLaw.bind fun rest =>
    (app.runRounds (family (joinBobSeed false rest)) players count initialExecution).map
      fun execution => (execution, rest)

/-- This factors the initialized joint, retaining the complete updated hidden
prefix and every other original address coordinate, rather than replacing it. -/
theorem beforeBobOriginalJoint_eq (players : Player → app.Policy) (count : Nat)
    (early : count ≤ 12) :
    beforeBobOriginalJoint players count =
      bindPairLaw (PMF.uniformOfFintype Bool) (fun _ => beforeBobRemainderLaw players count) := by
  unfold beforeBobOriginalJoint
  rw [seedPrior_split_bob]
  simp only [PMF.bind_bind, PMF.bind_map]
  apply bind_congr_on_support
  intro bit _
  unfold beforeBobRemainderLaw
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply bind_congr_on_support
  intro rest _
  rw [run_before_bob_seed players count early]
  congr 1
  funext execution
  rw [joinBobSeed_bit, joinBobSeed_rest]

theorem beforeBobOriginalJoint_physical (players : Player → app.Policy) (count : Nat) :
    (beforeBobOriginalJoint players count).map (fun outcome => outcome.2.1) =
      app.runRounds scheduler players count initialExecution := by
  unfold beforeBobOriginalJoint
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  change (seedPrior.bind fun seed =>
    (app.runRounds (family seed) players count initialExecution).map id) = _
  simp only [PMF.map_id]
  exact original_realize players count initialState

theorem beforeBob_seed_of_entire_remainder (players : Player → app.Policy) (count : Nat)
    (early : count ≤ 12) (observed : app.Execution × BobSeedRest)
    (present : observed ∈ ((beforeBobOriginalJoint players count).map Prod.snd).support) :
    (fiberPosterior (beforeBobOriginalJoint players count) Prod.snd observed).map Prod.fst =
      PMF.uniformOfFintype Bool := by
  have transported := map_fiberPosterior_readout (beforeBobOriginalJoint players count)
    Prod.swap Prod.fst observed present
  have projected := congrArg (fun law : PMF ((app.Execution × BobSeedRest) × Bool) =>
    law.map Prod.snd) transported
  rw [PMF.map_comp] at projected
  change (fiberPosterior (beforeBobOriginalJoint players count) Prod.snd observed).map Prod.fst =
    (fiberPosterior ((beforeBobOriginalJoint players count).map Prod.swap)
      Prod.fst observed).map Prod.snd at projected
  rw [projected, beforeBobOriginalJoint_eq players count early,
    bindPairLaw_const_map_swap]
  exact fiberPosterior_snd_bindPairLaw_const _ _ _

def firstLatePosition (owner : Player) : Nat := if owner = alice then 4 else 12

def markerOwner (owner : Player) : Player := if owner = alice then bob else alice

private theorem pendingCommand_actor_none (identifier : MessageId Player)
    (view : app.EnvironmentView) :
    (pendingCommand identifier view).actor? app = none := by
  unfold pendingCommand
  split <;> rfl

private theorem earlyCommand_actor_none (owner : Player)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) :
    (earlyCommand owner past view).actor? app = none := by
  unfold earlyCommand
  split
  · rfl
  · split
    · rfl
    · exact pendingCommand_actor_none _ _

private theorem lateCommand_actor_none (owner : Player) (bit : Bool) (clock : Nat)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) :
    (lateCommand owner bit clock past view).actor? app = none := by
  unfold lateCommand
  split
  · split
    · rfl
    · exact pendingCommand_actor_none _ _
  · rfl

theorem original_activation_positions (seed : Seeds) (position : Nat)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) (owner : Player)
    (bounded : position < 22)
    (selected : originalCommand seed position past view = .activate owner) :
    position = 0 ∨ position = 1 ∨ position = 4 ∨ position = 6 ∨ position = 9 ∨
      position = 12 ∨ position = 14 ∨ position = 17 := by
  interval_cases position <;> first
  | omega
  | have actor := congrArg (ReactiveApplication.Command.actor? app) selected
    simp only [originalCommand] at actor
    first
    | rw [earlyCommand_actor_none] at actor
      cases actor
    | rw [lateCommand_actor_none] at actor
      cases actor
    | cases actor

/-- A real original first-late activation has its exact scheduled index.
The seed changes within-clock placement, not the observed activation clock. -/
theorem original_first_late_activation_index (seed : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seed)).Trace (some current))
    (owner : Player)
    (original : current.execution.application.attempt = originalAttempt)
    (clock : current.execution.application.current.native.clock = lateClock owner false)
    (selected : (ReactiveApplication.Command.activate owner : app.Command) ∈
      (family seed current.execution.environmentRecall
        (current.execution.observeEnvironment app)).support) :
    current.execution.environmentRecall.length =
      firstLatePosition owner + if seedBits seed owner then 2 else 0 := by
  rw [family_apply, choose_original _ _ _ original] at selected
  have chosen : originalCommand seed current.execution.environmentRecall.length
      current.execution.environmentRecall (current.execution.observeEnvironment app) =
        .activate owner := ((PMF.mem_support_pure_iff _ _).mp selected).symm
  have bounded : current.execution.environmentRecall.length < 22 := by
    by_contra later
    rw [originalCommand_bound _ _ _ _ (by omega)] at chosen
    cases chosen
  have positions := original_activation_positions seed _ _ _ owner bounded chosen
  have elapsed : originalClock current.execution.environmentRecall.length =
      lateClock owner false := (original_clock_index seed current trace original).symm.trans clock
  cases bit : seedBits seed owner <;> unfold seedBits at bit <;> fin_cases owner <;>
    rcases positions with position | position | position | position | position | position |
      position | position
  all_goals
    rw [position] at chosen elapsed ⊢
    norm_num [originalClock, originalClockFrom, originalTick, lateClock] at elapsed
  all_goals
    first
    | solve | norm_num [firstLatePosition]
    | first
      | change seed.2 (originalAddress alice) = _ at bit
      | change seed.2 (originalAddress bob) = _ at bit
      simp only [originalCommand, pollCommand] at chosen
      rw [bit] at chosen
      cases chosen

/-- A genuine full first-late input has the scheduled command count, including
its own activation. This applies to every raw history in the information fiber. -/
theorem original_first_late_input_index (seed : Seeds) (current : app.Control)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace (some current))
    (owner : Player) (active : current.actor = some owner)
    (original : current.execution.application.attempt = originalAttempt)
    (clock : current.execution.application.current.native.clock = lateClock owner false) :
    current.execution.environmentRecall.length =
      firstLatePosition owner + if seedBits seed owner then 3 else 1 := by
  obtain ⟨_accounted, supported⟩ := rawMenu.roundSupported_uniform initial horizon
    (family seed) trace
  rw [active] at supported
  obtain ⟨count, before, command, position, reached, selected, actor, moved⟩ := supported
  have commandEq : command = (ReactiveApplication.Command.activate owner : app.Command) := by
    cases command <;> simp only [ReactiveApplication.Command.actor?, Option.some.injEq] at actor
    · exact congrArg ReactiveApplication.Command.activate actor
    all_goals cases actor
  subst command
  rw [completeActivation_law] at moved
  have executionEq := (PMF.mem_support_pure_iff _ _).mp moved
  have originalBefore : before.application.attempt = originalAttempt := by
    rw [executionEq] at original
    exact original
  have clockBefore : before.application.current.native.clock = lateClock owner false := by
    rw [executionEq] at clock
    exact clock
  obtain ⟨beforeTrace⟩ := rawMenu.trace_roundsFrom initial horizon (family seed)
    rawMenu.uniformResponses (by
      intro who past view action member
      exact (rawMenu.uniformResponses_support who past view action).mp member)
    count (by omega) before reached
  have beforeIndex := original_first_late_activation_index seed
    (⟨horizon - count, none, before⟩ : app.Control)
    (rawMenu.toRawTrace initial horizon (family seed) beforeTrace) owner
    originalBefore clockBefore selected
  have afterCount : current.execution.environmentRecall.length =
      before.environmentRecall.length + 1 := by
    rw [executionEq]
    change (before.environmentRecall ++ [_]).length = _
    simp only [List.length_append, List.length_singleton]
  rw [afterCount, beforeIndex]
  split_ifs <;> omega

/-- Every recorded response at the first late clock comes from that exact
scheduled input, even when the packet was retained through a later retry. -/
theorem original_first_late_recorded_response (seed : Seeds) (current : app.Control)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace (some current))
    (owner : Player) (entry : app.PlayerEntry)
    (recorded : entry ∈ current.execution.recall owner)
    (original : entry.beforeView.application.2.attempt = originalAttempt)
    (clock : entry.beforeView.application.2.native.clock = lateClock owner false) :
    ∃ (before : app.Control)
      (prior : (rawMenu.protocol initial horizon (family seed)).Trace (some before)),
      TracePrefix prior trace ∧ before.actor = some owner ∧
      entry.beforeView = before.execution.observe app owner ∧
      before.execution.application.attempt = originalAttempt ∧
      before.execution.application.current.native.clock = lateClock owner false ∧
      before.execution.environmentRecall.length =
        firstLatePosition owner + if seedBits seed owner then 3 else 1 := by
  obtain ⟨before, prior, retained, active, observed, _allowed, _rest⟩ :=
    rawMenu.recorded_response_prefix initial horizon (family seed) current trace owner entry
      recorded
  have beforeOriginal : before.execution.application.attempt = originalAttempt := by
    rw [observed] at original
    exact original
  have beforeClock : before.execution.application.current.native.clock =
      lateClock owner false := by
    rw [observed] at clock
    exact clock
  exact ⟨before, prior, retained, active, observed, beforeOriginal, beforeClock,
    original_first_late_input_index seed before prior owner active beforeOriginal beforeClock⟩

/-- Every retained first-clock original emission has a genuine callback at
the scheduled first polling position, including after the attempt has retired. -/
theorem original_first_late_emission (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player) (message : Message Player (CommitAttemptPacket graph))
    (emitted : (lateClock owner false, message) ∈
      (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
        execution.environmentRecall (execution.observeEnvironment app)).emissions) :
    ∃ (entry : app.PlayerEntry) (before : app.Control)
      (prior : (rawMenu.protocol initial horizon (family seed)).Trace (some before)),
      entry ∈ execution.recall owner ∧ entry.emitted = some message ∧
      TracePrefix prior trace ∧ before.actor = some owner ∧
      entry.beforeView = before.execution.observe app owner ∧
      before.execution.application.attempt = originalAttempt ∧
      before.execution.application.current.native.clock = lateClock owner false ∧
      before.execution.environmentRecall.length =
        firstLatePosition owner + if seedBits seed owner then 3 else 1 := by
  classical
  obtain ⟨_accounted, supported⟩ := rawMenu.roundSupported_uniform initial horizon
    (family seed) trace
  change execution ∈ (app.roundsFrom initial (family seed) rawMenu.uniformResponses
    execution.environmentRecall.length).support at supported
  rw [ReactiveApplication.roundsFrom, initial_eq_pure, PMF.pure_bind] at supported
  have word := PhaseSeedScheduler.runRounds_wordRecall runtime leaks (family seed)
    rawMenu.uniformResponses execution.environmentRecall.length initialExecution execution
    (PhaseSeedScheduler.initial_wordRecall runtime leaks initialState) supported
  rw [PhaseSeedScheduler.localInput_word, word,
    PhaseSeedScheduler.ownerWord] at emitted
  obtain ⟨pair, recalled, contained⟩ := List.mem_flatMap.mp emitted
  obtain ⟨entry, requested, pairEq⟩ := List.mem_map.mp recalled
  obtain ⟨recorded, requested⟩ := List.mem_filter.mp requested
  subst pair
  obtain ⟨actual, actualMember, pairEq⟩ := List.mem_map.mp contained
  obtain ⟨actualMember, _packet⟩ := List.mem_filter.mp actualMember
  have actualEq : actual = message := congrArg Prod.snd pairEq
  subst actual
  have envelope : entry.emitted = some message := by
    cases emittedEq : entry.emitted with
    | none =>
        simp only [emittedEq, Option.toList_none, List.not_mem_nil] at actualMember
    | some value =>
        have equal : message = value := by
          simpa only [emittedEq, Option.toList_some, List.mem_singleton] using actualMember
        exact congrArg some equal.symm
  have elapsed := congrArg Prod.fst pairEq
  obtain ⟨before, prior, retained, active, observed, _allowed, _rest⟩ :=
    rawMenu.recorded_response_prefix initial horizon (family seed)
      ⟨remaining, none, execution⟩ trace owner entry recorded
  have request : before.execution.application.SeedRequest owner (originalCoordinate owner) := by
    rw [observed] at requested
    exact (before.execution.application.requests_publicView
      (raw_native_valid (family seed) before
        (rawMenu.toRawTrace initial horizon (family seed) prior)) owner
      (originalCoordinate owner)).mp (of_decide_eq_true requested)
  have original : before.execution.application.attempt = originalAttempt := request.1.symm
  have binding : bindingEvent owner = aliceBinding ∨ bindingEvent owner = bobBinding := by
    fin_cases owner
    · exact Or.inl rfl
    · exact Or.inr rfl
  have timer := original_timer (family seed) before
    (rawMenu.toRawTrace initial horizon (family seed) prior) original (bindingEvent owner)
      binding request.2.2.1.1
  have clock : before.execution.application.current.native.clock = lateClock owner false := by
    rw [observed] at elapsed
    change before.execution.application.current.native.clock -
      (before.execution.application.current.native.activatedAt (bindingEvent owner)).getD
        before.execution.application.current.native.clock = lateClock owner false at elapsed
    simpa only [timer, Option.getD_some, Nat.sub_zero] using elapsed
  exact ⟨entry, before, prior, recorded, envelope, retained, active, observed, original, clock,
    original_first_late_input_index seed before prior owner active original clock⟩

theorem family_first_late_command (seed : Seeds) (owner : Player)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (original : view.application.attempt = originalAttempt)
    (position : past.length = firstLatePosition owner) :
    family seed past view =
      PMF.pure (pollCommand owner (seedBits seed owner) false view) := by
  rw [family_apply, choose_original _ _ _ original, position]
  fin_cases owner <;> rfl

theorem family_middle_late_command (seed : Seeds) (owner : Player)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (original : view.application.attempt = originalAttempt)
    (position : past.length = firstLatePosition owner + 1) :
    family seed past view = PMF.pure (earlyCommand (markerOwner owner) past view) := by
  rw [family_apply, choose_original _ _ _ original, position]
  fin_cases owner <;> rfl

theorem family_last_late_poll (seed : Seeds) (owner : Player)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (original : view.application.attempt = originalAttempt)
    (position : past.length = firstLatePosition owner + 2) :
    family seed past view = PMF.pure (pollCommand owner (seedBits seed owner) true view) := by
  rw [family_apply, choose_original _ _ _ original, position]
  fin_cases owner <;> rfl

/-- The literal state obtained by two actual identity commands. -/
def pollDelay (execution : app.Execution) : app.Execution :=
  let first : app.Execution := { execution with environmentRecall :=
    execution.environmentRecall ++ [⟨execution.observeEnvironment app, .wait⟩] }
  { first with environmentRecall :=
    first.environmentRecall ++ [⟨first.observeEnvironment app, .wait⟩] }

theorem pollDelay_length (execution : app.Execution) :
    (pollDelay execution).environmentRecall.length = execution.environmentRecall.length + 2 := by
  simp only [pollDelay, List.length_append, List.length_singleton]

theorem nohelper_delay (seed : Seeds) (players : Player → app.Policy) (owner : Player)
    (execution : app.Execution)
    (original : execution.application.attempt = originalAttempt)
    (position : execution.environmentRecall.length = firstLatePosition owner)
    (noHelper : earlyCommand (markerOwner owner) execution.environmentRecall
      (execution.observeEnvironment app) = .wait)
    (bit : seedBits seed owner = true) :
    app.runRounds (family seed) players 2 execution = PMF.pure (pollDelay execution) := by
  let first : app.Execution := { execution with environmentRecall :=
    execution.environmentRecall ++ [⟨execution.observeEnvironment app, .wait⟩] }
  have firstLength : first.environmentRecall.length = firstLatePosition owner + 1 := by
    simp only [first, List.length_append, List.length_singleton, position]
  have firstOriginal : first.application.attempt = originalAttempt := original
  have lower : 2 < execution.environmentRecall.length := by
    rw [position]
    fin_cases owner <;> decide
  have middle : earlyCommand (markerOwner owner) first.environmentRecall
      (first.observeEnvironment app) = .wait := by
    unfold earlyCommand
    change (match (execution.environmentRecall ++ [_])[2]? with
      | none => _
      | some entry => _) = (ReactiveApplication.Command.wait : app.Command)
    rw [List.getElem?_append_left lower]
    exact noHelper
  have firstCommand : family seed execution.environmentRecall
      (execution.observeEnvironment app) = PMF.pure .wait := by
    rw [family_first_late_command seed owner _ _ original position]
    simp only [bit, pollCommand]
    rfl
  have middleCommand : family seed first.environmentRecall (first.observeEnvironment app) =
      PMF.pure .wait := by
    rw [family_middle_late_command seed owner _ _ firstOriginal firstLength, middle]
  have firstWait : execution.environmentStep app .wait = PMF.pure first := by
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
    rfl
  have secondWait : first.environmentStep app .wait = PMF.pure (pollDelay execution) := by
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
    rfl
  have firstRound : app.round (family seed) players execution = PMF.pure first := by
    simp only [ReactiveApplication.round, firstCommand, PMF.pure_bind,
      ReactiveApplication.dispatch, firstWait, ReactiveApplication.Command.actor?,
      ReactiveApplication.resume]
  have secondRound : app.round (family seed) players first =
      PMF.pure (pollDelay execution) := by
    simp only [ReactiveApplication.round, middleCommand, PMF.pure_bind,
      ReactiveApplication.dispatch, secondWait, ReactiveApplication.Command.actor?,
      ReactiveApplication.resume]
  simp only [ReactiveApplication.runRounds, firstRound, secondRound, PMF.pure_bind]

/-- The first late callback reads the same complete native input at either
actual polling position when the fixed middle early-packet command is silent. -/
theorem nohelper_poll_input (seed : Seeds) (players : Player → app.Policy) (owner : Player)
    (execution : app.Execution)
    (original : execution.application.attempt = originalAttempt)
    (position : execution.environmentRecall.length = firstLatePosition owner)
    (requested : ready owner (bindingEvent owner) (execution.observeEnvironment app) = true)
    (noHelper : earlyCommand (markerOwner owner) execution.environmentRecall
      (execution.observeEnvironment app) = .wait) :
    let nextInput := fun before : app.Execution =>
      (family seed before.environmentRecall (before.observeEnvironment app)).bind fun command =>
        (before.environmentStep app command).map fun active =>
          app.observe owner (some ⟨0, command.actor? app, active⟩)
    (if seedBits seed owner then
      (app.runRounds (family seed) players 2 execution).bind nextInput
    else nextInput execution) =
      (execution.environmentStep app (.activate owner)).map fun active =>
        some (active.recall owner, active.observe app owner) := by
  dsimp only
  cases bit : seedBits seed owner with
  | false =>
      have command : family seed execution.environmentRecall
          (execution.observeEnvironment app) = PMF.pure (.activate owner) := by
        rw [family_first_late_command seed owner _ _ original position]
        simp only [bit, pollCommand, ite_true, activateReady, requested]
      simp only [Bool.false_eq_true, ite_false, command, PMF.pure_bind,
        ReactiveApplication.observe, ReactiveApplication.Command.actor?, ite_true]
  | true =>
      have delayedLength : (pollDelay execution).environmentRecall.length =
          firstLatePosition owner + 2 := by rw [pollDelay_length, position]
      have command : family seed (pollDelay execution).environmentRecall
          ((pollDelay execution).observeEnvironment app) = PMF.pure (.activate owner) := by
        rw [family_last_late_poll seed owner _ _ original delayedLength]
        simp only [bit, pollCommand, ite_true, activateReady]
        change PMF.pure ((if ready owner (bindingEvent owner)
          (execution.observeEnvironment app) then .activate owner else .wait) : app.Command) = _
        rw [requested]
        rfl
      simp only [ite_true,
        nohelper_delay seed players owner execution original position noHelper bit,
        PMF.pure_bind, command]
      rw [completeActivation_law, completeActivation_law]
      simp only [PMF.pure_map, ReactiveApplication.observe,
        ReactiveApplication.Command.actor?, ite_true]
      rfl

/-- The actual initialized continuation uses one common response law at the
first late callback; only its hidden waiting prefix and remaining fuel differ. -/
theorem nohelper_first_response_rounds (seed : Seeds) (players : Player → app.Policy)
    (owner : Player) (extra : Nat) (execution : app.Execution)
    (original : execution.application.attempt = originalAttempt)
    (position : execution.environmentRecall.length = firstLatePosition owner)
    (requested : ready owner (bindingEvent owner) (execution.observeEnvironment app) = true)
    (noHelper : earlyCommand (markerOwner owner) execution.environmentRecall
      (execution.observeEnvironment app) = .wait) :
    app.runRounds (family seed) players (extra + 3) execution =
      (players owner ((completeActivation execution owner).recall owner)
        ((completeActivation execution owner).observe app owner)).bind fun response =>
          app.runRounds (family seed) players
            (if seedBits seed owner then extra else extra + 2)
            ((completeActivation
              (if seedBits seed owner then pollDelay execution else execution) owner).respond
                app owner response) := by
  cases bit : seedBits seed owner with
  | false =>
      have command : family seed execution.environmentRecall
          (execution.observeEnvironment app) = PMF.pure (.activate owner) := by
        rw [family_first_late_command seed owner _ _ original position]
        simp only [bit, pollCommand, ite_true, activateReady, requested]
      rw [show extra + 3 = (extra + 2) + 1 by omega, ReactiveApplication.runRounds]
      simp only [ReactiveApplication.round, command, PMF.pure_bind,
        ReactiveApplication.dispatch, completeActivation_law, PMF.pure_bind,
        ReactiveApplication.Command.actor?, ReactiveApplication.resume,
        ReactiveApplication.invoke, PMF.bind_map, Function.comp_def, Bool.false_eq_true, ite_false]
  | true =>
      have delayedLength : (pollDelay execution).environmentRecall.length =
          firstLatePosition owner + 2 := by rw [pollDelay_length, position]
      have command : family seed (pollDelay execution).environmentRecall
          ((pollDelay execution).observeEnvironment app) = PMF.pure (.activate owner) := by
        rw [family_last_late_poll seed owner _ _ original delayedLength]
        simp only [bit, pollCommand, ite_true, activateReady]
        change PMF.pure ((if ready owner (bindingEvent owner)
          (execution.observeEnvironment app) then .activate owner else .wait) : app.Command) = _
        rw [requested]
        rfl
      rw [show extra + 3 = 2 + (extra + 1) by omega, app.runRounds_add,
        nohelper_delay seed players owner execution original position noHelper bit,
        PMF.pure_bind, ReactiveApplication.runRounds]
      simp only [ReactiveApplication.round, command, PMF.pure_bind,
        ReactiveApplication.dispatch, completeActivation_law, PMF.pure_bind,
        ReactiveApplication.Command.actor?, ReactiveApplication.resume,
        ReactiveApplication.invoke, PMF.bind_map, Function.comp_def, ite_true]
      rfl

end Vegas.Examples.CommitSeedSignalling
