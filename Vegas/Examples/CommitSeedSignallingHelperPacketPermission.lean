/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingHelperInitialRecall
import Vegas.Examples.CommitSeedSignallingTimingIncentives
import Interaction.ReactiveRecordedResponseAfter
import Interaction.ReactiveEmissionOrder

/-! # Observable helper envelopes determine actual initial response permissions -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob)

private theorem bob_original_record_first (current : app.Control)
    (trace : rawProtocol.Trace (some current))
    (entry : app.PlayerEntry) (recorded : entry ∈ current.execution.recall bob)
    (original : entry.beforeView.application.2.attempt = originalAttempt)
    (clock : entry.beforeView.application.1.publicView.clock = 0) :
    ∃ later, current.execution.recall bob = entry :: later := by
  obtain ⟨before, prior, _kept, acting, viewed, _allowed, later, recalled⟩ :=
    rawMenu.recorded_response_prefix initial horizon scheduler current trace bob entry recorded
  have originalBefore : before.execution.application.attempt = originalAttempt := by
    rw [viewed] at original
    exact original
  have clockBefore : before.execution.application.current.native.clock = 0 := by
    rw [viewed] at clock
    exact clock
  obtain (⟨impossible, _⟩ | ⟨_owner, first, state⟩) := original_zero_clock_decision before bob
    (rawMenu.toRawTrace initial horizon scheduler prior) acting originalBefore clockBefore
  · exact ((by decide : bob ≠ alice) impossible).elim
  · have empty : before.execution.recall bob = [] := by
      rw [state]
      exact bobFirst_recall first
    rw [empty, List.nil_append] at recalled
    exact ⟨later, recalled⟩

/-- A remembered initial Bob response retains its complete actual materialization,
including private preparations and evidence aliases. -/
theorem bob_original_record_materialization (current : app.Control)
    (trace : rawProtocol.Trace (some current))
    (entry : app.PlayerEntry) (recorded : entry ∈ current.execution.recall bob)
    (original : entry.beforeView.application.2.attempt = originalAttempt)
    (clock : entry.beforeView.application.1.publicView.clock = 0) :
    ∃ first : app.Action,
      entry.beforeView = (bobFirst first).observe app bob ∧
      entry.action ∈ rawMenu.actions bob [] ((bobFirst first).observe app bob) ∧
      entry.emitted = entry.action.transmission.map (fun material =>
        PhaseCount.localEnvelope runtime leaks bob [] ((bobFirst first).observe app bob)
          material) ∧
      originalResponseEntry aliceFirst alice first ∈ current.execution.recall alice := by
  obtain ⟨later, recalled⟩ := bob_original_record_first current trace entry recorded original clock
  obtain ⟨remaining, execution, prior, postTrace, kept, empty, viewed, allowed, _before, _length⟩ :=
    rawMenu.recorded_response_after initial horizon scheduler current trace bob [] entry later
      (by simpa only [List.nil_append] using recalled)
  have originalBefore : execution.application.attempt = originalAttempt := by
    rw [viewed] at original
    exact original
  have clockBefore : execution.application.current.native.clock = 0 := by
    rw [viewed] at clock
    exact clock
  obtain (⟨impossible, _⟩ | ⟨_owner, first, state⟩) := original_zero_clock_decision
    ⟨remaining, some bob, execution⟩ bob (rawMenu.toRawTrace initial horizon scheduler prior)
      rfl originalBefore clockBefore
  · exact ((by decide : bob ≠ alice) impossible).elim
  · have sameExecution : execution = bobFirst first :=
      congrArg ReactiveApplication.Control.execution state
    have retained := app.reaches_recall_prefix initial horizon scheduler
      (rawMenu.reaches_raw initial horizon scheduler kept.reachesWithin)
      ⟨remaining, none, execution.respond app bob entry.action⟩ current rfl rfl bob
    rw [respond_originalResponseEntry, empty, List.nil_append, recalled] at retained
    have actual : originalResponseEntry execution bob entry.action = entry := by
      obtain ⟨_tail, heads, _rest⟩ := List.cons_prefix_iff.mp retained
      exact (List.cons.inj heads).1.symm
    have countRecall := PhaseCount.countRecall_history runtime leaks
      (rawMenu.toRawTrace initial horizon scheduler prior)
    refine ⟨first, viewed.trans (congrArg (fun next : app.Execution => next.observe app bob)
      sameExecution), ?_, ?_, ?_⟩
    · rwa [empty, sameExecution] at allowed
    · rw [← actual]
      change entry.action.transmission.map (fun material => _) = _
      apply congrArg (fun fn => entry.action.transmission.map fn)
      funext material
      have envelope := PhaseCount.localEnvelope_eq_of_recall runtime leaks execution
        countRecall.1 countRecall.2.1 bob material
      rw [empty, sameExecution] at envelope
      rw [sameExecution]
      exact envelope.symm
    · have aliceBefore : originalResponseEntry aliceFirst alice first ∈
          execution.recall alice := by
        rw [sameExecution]
        change originalResponseEntry aliceFirst alice first ∈
          (aliceFirst.respond app alice first).recall alice
        rw [respond_originalResponseEntry, aliceFirst_recall, List.nil_append]
        exact List.mem_singleton_self _
      have alicePost : originalResponseEntry aliceFirst alice first ∈
          (execution.respond app bob entry.action).recall alice :=
        app.respond_recall_mono execution bob alice entry.action aliceBefore
      exact (app.reaches_recall_prefix initial horizon scheduler
        (rawMenu.reaches_raw initial horizon scheduler kept.reachesWithin)
        ⟨remaining, none, execution.respond app bob entry.action⟩ current rfl rfl alice).subset
          alicePost

/-- The signed helper packet seen at an original Alice query is Bob's first
envelope and has its count permission independently of later traffic. -/
theorem observed_helper_packet_permission (seed : Seeds) (current : app.Control)
    (trace : countedProtocol.Trace (some current))
    (fixed : (rawMenu.protocol initial horizon (family seed)).Trace (some current))
    (request : current.execution.application.SeedRequest alice (originalCoordinate alice))
    (early : current.execution.environmentRecall.length ≤ 12)
    (message : Message Player (CommitAttemptPacket graph))
    (input : message ∈ current.execution.network.inputs) (sender : message.sender = bob) :
    message.id = (bob, 0) ∧ PhaseCount.permits [] message = true := by
  obtain ⟨entry, recorded, emitted, original, clock⟩ :=
    bob_packet_before_late_origin seed current fixed request early message input sender
  have mixed := countedInRaw.trace initial horizon scheduler trace
  obtain ⟨later, recalled⟩ := bob_original_record_first current mixed entry recorded original clock
  have raw := countedMenu.toRawTrace initial horizon scheduler trace
  have order := app.emissionOrder_history scheduler initial horizon raw
  have identified := app.emitted_serial_of_recall_split current.execution order bob [] later
    entry (by simpa only [List.nil_append] using recalled) message emitted
  have identity : message.id = (bob, 0) := by
    simpa only [ReactiveApplication.outputs, List.filterMap_nil, List.length_nil] using identified
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
  have verdict := clean.2 message input
  have equal : PhaseCount.permits current.execution.network.inputs message =
      PhaseCount.permits [] message := by
    apply PhaseCount.permits_congr
    intro other
    constructor
    · intro earlier
      have lower := earlier.2.2
      rw [identity] at lower
      exact (Nat.not_lt_zero _ lower).elim
    · intro earlier
      exact (List.not_mem_nil earlier.1).elim
  exact ⟨identity, equal ▸ verdict⟩

/-- The actual raw Bob response is permitted whenever its observed signed
envelope is the permitted helper. The hidden preparation need not match the
preparation of another history which emitted that envelope. -/
theorem bob_original_record_counted_of_helper (current : app.Control)
    (trace : rawProtocol.Trace (some current))
    (entry : app.PlayerEntry) (recorded : entry ∈ current.execution.recall bob)
    (original : entry.beforeView.application.2.attempt = originalAttempt)
    (clock : entry.beforeView.application.1.publicView.clock = 0)
    (message : Message Player (CommitAttemptPacket graph))
    (emitted : entry.emitted = some message)
    (permitted : PhaseCount.permits [] message = true) :
    ∃ first : app.Action,
      entry.beforeView = (bobFirst first).observe app bob ∧
      entry.action ∈ countedMenu.actions bob [] ((bobFirst first).observe app bob) ∧
      originalResponseEntry aliceFirst alice first ∈ current.execution.recall alice := by
  obtain ⟨first, viewed, allowed, materialized, aliceRecorded⟩ :=
    bob_original_record_materialization current trace entry recorded original clock
  refine ⟨first, viewed, (PhaseCount.mem_onePacketActions runtime leaks bounds bob _ _ _).mpr
    ⟨allowed, Or.inr ?_⟩, aliceRecorded⟩
  rw [materialized] at emitted
  obtain ⟨material, transmitted, equal⟩ := Option.map_eq_some_iff.mp emitted
  refine ⟨material, transmitted, ?_⟩
  change PhaseCount.permits [] _ = true
  rwa [equal]

/-- Initial own WAIT and the permitted helper envelope force the actual raw
Bob declaration to be fresh and count-admitted. Neither its preparation nor
its evidence request is borrowed from the counted representative. -/
theorem bob_helper_record_binding_shape (current : app.Control)
    (trace : rawProtocol.Trace (some current))
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ current.execution.recall alice)
    (entry : app.PlayerEntry) (recorded : entry ∈ current.execution.recall bob)
    (original : entry.beforeView.application.2.attempt = originalAttempt)
    (clock : entry.beforeView.application.1.publicView.clock = 0)
    (material : app.Submission) (transmitted : entry.action.transmission = some material)
    (message : Message Player (CommitAttemptPacket graph))
    (emitted : entry.emitted = some message)
    (permitted : PhaseCount.permits [] message = true) :
    entry.beforeView = (bobFirst ⟨none⟩).observe app bob ∧
      ∃ serial preparation evidence,
        material = ⟨⟨.commitment bobBinding (bob, .prepared serial), preparation⟩, evidence⟩ ∧
        serial < bounds.candidateCount ∧
        (bobFirst ⟨none⟩).application.current.native.candidates.lookup
          (bob, .prepared serial) = .fresh := by
  obtain ⟨first, viewed, counted, aliceRecorded⟩ := bob_original_record_counted_of_helper
    current trace entry recorded original clock message emitted permitted
  obtain ⟨later, recalled⟩ := alice_original_zero_clock_record_first current trace
    (originalResponseEntry aliceFirst alice first) aliceRecorded initialState_attempt
      initialState_clock
  obtain ⟨quietLater, quietRecall⟩ := alice_original_zero_clock_record_first current trace
    (originalResponseEntry aliceFirst alice ⟨none⟩) quiet initialState_attempt initialState_clock
  have sameRecord := (List.cons.inj (recalled.symm.trans quietRecall)).1
  have firstQuiet : first = (⟨none⟩ : app.Action) :=
    congrArg ReactiveApplication.PlayerEntry.action sameRecord
  subst first
  have action : entry.action = (⟨some material⟩ : app.Action) := by
    cases action : entry.action with
    | mk transmission =>
        rw [action] at transmitted
        change transmission = some material at transmitted
        cases transmitted
        rfl
  rw [action] at counted
  exact ⟨viewed, bobQuiet_counted_binding_shape material counted⟩

/-- At every raw realization of the same complete Alice input, the observed
helper comes from an actually counted fresh Bob declaration. All target
preparations and evidence requests remain its own literal ones. -/
theorem helper_packet_binding_shape_on_same_input
    (sourceSeed targetSeed : Seeds) (source target : app.Control)
    (sourceTrace : countedProtocol.Trace (some source))
    (sourceFixed : (rawMenu.protocol initial horizon (family sourceSeed)).Trace (some source))
    (targetTrace : rawProtocol.Trace (some target))
    (targetFixed : (rawMenu.protocol initial horizon (family targetSeed)).Trace (some target))
    (sourceActive : source.actor = some alice) (targetActive : target.actor = some alice)
    (request : source.execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : source.execution.application.current.native.clock = 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ source.execution.recall alice)
    (recalled : target.execution.recall alice = source.execution.recall alice)
    (observed : target.execution.observe app alice = source.execution.observe app alice)
    (message : Message Player (CommitAttemptPacket graph)) (sender : message.sender = bob)
    (visible : message ∈ (source.execution.observe app alice).messages.leaked ∨
      message ∈ (source.execution.observe app alice).messages.ledger) :
    ∃ entry ∈ target.execution.recall bob, ∃ material serial preparation evidence,
      entry.action.transmission = some material ∧ entry.emitted = some message ∧
      entry.beforeView = (bobFirst ⟨none⟩).observe app bob ∧
      material = ⟨⟨.commitment bobBinding (bob, .prepared serial), preparation⟩, evidence⟩ ∧
      serial < bounds.candidateCount ∧
      (bobFirst ⟨none⟩).application.current.native.candidates.lookup
        (bob, .prepared serial) = .fresh := by
  have sourceRaw := countedMenu.toRawTrace initial horizon scheduler sourceTrace
  have targetRaw := rawMenu.toRawTrace initial horizon scheduler targetTrace
  have sourceValid := raw_native_valid scheduler source sourceRaw
  have targetValid := raw_native_valid scheduler target targetRaw
  have publicSource := (source.execution.application.requests_publicView sourceValid alice
    (originalCoordinate alice)).mpr request
  have publicTarget : PhaseRuntimeState.requests target.execution.application.publicView alice
      (originalCoordinate alice) := by
    change PhaseRuntimeState.requests (target.execution.observe app alice).application.2 alice _
    rw [observed]
    exact publicSource
  have targetRequest := (target.execution.application.requests_publicView targetValid alice
    (originalCoordinate alice)).mp publicTarget
  have targetClock : target.execution.application.current.native.clock = 2 := by
    change (target.execution.observe app alice).application.2.native.clock = 2
    rw [observed]
    exact clock
  have sourceCount := original_first_late_input_index sourceSeed source sourceFixed alice
    sourceActive request.1.symm clock
  have targetCount := original_first_late_input_index targetSeed target targetFixed alice
    targetActive targetRequest.1.symm targetClock
  change source.execution.environmentRecall.length =
    4 + if seedBits sourceSeed alice then 3 else 1 at sourceCount
  change target.execution.environmentRecall.length =
    4 + if seedBits targetSeed alice then 3 else 1 at targetCount
  have sourceEarly : source.execution.environmentRecall.length ≤ 12 := by
    split_ifs at sourceCount <;> omega
  have targetEarly : target.execution.environmentRecall.length ≤ 12 := by
    split_ifs at targetCount <;> omega
  have sourceRetained := app.retained_envelopes_mem_inputs source.execution
    (app.history_provenance initial horizon scheduler sourceRaw)
    (app.history_inputRecall initial horizon scheduler sourceRaw)
  have sourceInput : message ∈ source.execution.network.inputs := by
    rcases visible with leaked | ledger
    · exact sourceRetained.leaked alice message leaked
    · exact sourceRetained.ledger message ledger
  have permitted := (observed_helper_packet_permission sourceSeed source sourceTrace sourceFixed
    request sourceEarly message sourceInput sender).2
  have targetRetained := app.retained_envelopes_mem_inputs target.execution
    (app.history_provenance initial horizon scheduler targetRaw)
    (app.history_inputRecall initial horizon scheduler targetRaw)
  have targetInput : message ∈ target.execution.network.inputs := by
    have targetVisible : message ∈ (target.execution.observe app alice).messages.leaked ∨
        message ∈ (target.execution.observe app alice).messages.ledger := by
      rw [observed]
      exact visible
    rcases targetVisible with leaked | ledger
    · exact targetRetained.leaked alice message leaked
    · exact targetRetained.ledger message ledger
  obtain ⟨entry, recorded, emitted, original, zero⟩ := bob_packet_before_late_origin targetSeed
    target targetFixed targetRequest targetEarly message targetInput sender
  obtain ⟨_first, _viewed, _allowed, materialized, _aliceRecorded⟩ :=
    bob_original_record_materialization target targetTrace entry recorded original zero
  have materializedSome := emitted
  rw [materialized] at materializedSome
  obtain ⟨material, transmitted, _samePacket⟩ := Option.map_eq_some_iff.mp materializedSome
  have targetQuiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈
      target.execution.recall alice := by
    rw [recalled]
    exact quiet
  obtain ⟨viewed, serial, preparation, evidence, shape, bounded, fresh⟩ :=
    bob_helper_record_binding_shape target targetTrace targetQuiet entry recorded original zero
      material transmitted message emitted permitted
  exact ⟨entry, recorded, material, serial, preparation, evidence, transmitted, emitted, viewed,
    shape, bounded, fresh⟩

end Vegas.Examples.CommitSeedSignalling
