/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingOriginalCalendar
import Vegas.Examples.CommitSeedSignallingProtected
import Vegas.Examples.CommitSeedSignallingHalfSuccess
import Interaction.ReactiveTrafficIdentity

/-! # The helper packet identifies the original Alice service seed -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

private theorem original_before_of_progress (before after : CommitAttemptId)
    (progress : before.generation ≤ after.generation ∧ before.phase ≤ after.phase)
    (original : after = originalAttempt) : before = originalAttempt := by
  rw [original] at progress
  rcases before with ⟨phase, generation⟩
  change generation ≤ 0 ∧ phase ≤ 0 at progress
  have phases : phase = 0 := by omega
  have generations : generation = 0 := by omega
  subst phase
  subst generation
  rfl

private theorem activateReady_not_include (owner : Player) (event : graph.EventId)
    (view : app.EnvironmentView) (identifier : MessageId Player) :
    activateReady owner event view ≠ .include identifier := by
  unfold activateReady
  split <;> intro impossible <;> cases impossible

private theorem pollCommand_not_include (owner : Player) (bit wanted : Bool)
    (view : app.EnvironmentView) (identifier : MessageId Player) :
    pollCommand owner bit wanted view ≠ .include identifier := by
  unfold pollCommand
  split
  · exact activateReady_not_include owner (bindingEvent owner) view identifier
  · intro impossible
    cases impossible

private theorem activateReady_owner (source actor : Player) (event : graph.EventId)
    (view : app.EnvironmentView) (selected : activateReady source event view = .activate actor) :
    source = actor := by
  unfold activateReady at selected
  split at selected
  · exact ReactiveApplication.Command.activate.inj selected
  · cases selected

private theorem pollCommand_owner (source actor : Player) (bit wanted : Bool)
    (view : app.EnvironmentView) (selected :
      pollCommand source bit wanted view = .activate actor) : source = actor := by
  unfold pollCommand at selected
  split at selected
  · exact activateReady_owner source actor (bindingEvent source) view selected
  · cases selected

private theorem original_before_helper_not_include (seed : Seeds) (position : Nat)
    (early : position < 5) (past : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (identifier : MessageId Player) :
    originalCommand seed position past view ≠ .include identifier := by
  interval_cases position
  · exact activateReady_not_include alice aliceBinding view identifier
  · exact activateReady_not_include bob bobBinding view identifier
  · intro impossible; cases impossible
  · intro impossible; cases impossible
  · exact pollCommand_not_include alice _ false view identifier

private theorem no_include_preserves_receipts (execution next : app.Execution)
    (command : app.Command) (notInclude : ∀ identifier, command ≠ .include identifier)
    (moved : next ∈ (execution.environmentStep app command).support) :
    next.receipts = execution.receipts := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      rfl
  | activate owner =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨selected, _possible, rfl⟩ := PMF.support_map .. ▸ supported
      rfl
  | application operation =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨state, _possible, rfl⟩ := PMF.support_map .. ▸ supported
      rfl
  | «include» identifier => exact (notInclude identifier rfl).elim

/-- Before the middle helper command there is no receipt, including rejected
receipts. This holds for arbitrary raw submissions and evidence requests. -/
theorem original_receipts_before_helper (seed : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seed)).Trace (some current))
    (original : current.execution.application.attempt = originalAttempt)
    (early : current.execution.environmentRecall.length ≤ 5) :
    current.execution.receipts = [] := by
  let predicate : app.Execution → Prop := fun execution =>
    execution.application.Ordered ∧
      (execution.application.attempt = originalAttempt →
        execution.environmentRecall.length ≤ 5 → execution.receipts = [])
  have invariant : app.ServiceInvariant (family seed) predicate := by
    constructor
    · intro execution owner action valid
      have ordered := (phaseApplication_seedOrder runtime leaks).respond
        execution owner action valid.1
      refine ⟨ordered, ?_⟩
      intro originalAfter earlyAfter
      have progress := (phaseApplication_namespace_progress runtime leaks).respond
        execution owner action valid.1
      have beforeOriginal := original_before_of_progress _ _ progress originalAfter
      rw [app.respond_environmentRecall] at earlyAfter
      rw [app.respond_receipts]
      exact valid.2 beforeOriginal earlyAfter
    · intro execution next command valid selected moved
      have ordered := (phaseApplication_seedOrder runtime leaks).environmentStep
        execution next command valid.1 moved
      refine ⟨ordered, ?_⟩
      intro originalAfter earlyAfter
      have progress := (phaseApplication_namespace_progress runtime leaks).environmentStep
        execution next command moved valid.1
      have beforeOriginal := original_before_of_progress _ _ progress originalAfter
      have recalled := app.environmentStep_environmentRecall execution next command moved
      have earlier : execution.environmentRecall.length < 5 := by
        rw [recalled, List.length_append, List.length_singleton] at earlyAfter
        omega
      have chosen : command = choose seed execution.environmentRecall
          (execution.observeEnvironment app) :=
        (PMF.mem_support_pure_iff _ _).mp selected
      have noInclude : ∀ identifier, command ≠ .include identifier := by
        intro identifier
        rw [chosen, choose_original seed _ _ beforeOriginal]
        exact original_before_helper_not_include seed _ earlier _ _ identifier
      rw [no_include_preserves_receipts execution next command noInclude moved]
      exact valid.2 beforeOriginal (by omega)
  have started : ∀ state ∈ initial.support,
      predicate (ReactiveApplication.Execution.initial app state) := by
    intro state supported
    rw [initial_eq_pure, PMF.mem_support_pure_iff] at supported
    subst state
    exact ⟨PhaseRuntimeState.initial_ordered plan _, fun _ _ => rfl⟩
  exact (invariant.history initial horizon started trace).2 original early

/-- Every retained Bob response before his late block is the original
clock-zero callback, including silence and arbitrary private preparation. -/
theorem bob_record_before_late_origin (seed : Seeds) (current : app.Control)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace (some current))
    (request : current.execution.application.SeedRequest alice (originalCoordinate alice))
    (early : current.execution.environmentRecall.length ≤ 12)
    (entry : app.PlayerEntry) (recorded : entry ∈ current.execution.recall bob) :
    entry.beforeView.application.2.attempt = originalAttempt ∧
      entry.beforeView.application.1.publicView.clock = 0 := by
  classical
  obtain ⟨before, prior, kept, active, observed, _allowed, _later⟩ :=
    rawMenu.recorded_response_prefix initial horizon (family seed) current trace bob entry recorded
  have beforeRequest := original_binding_request_of_prefix rawMenu seed before current
    prior trace kept alice request
  have original : before.execution.application.attempt = originalAttempt := beforeRequest.1.symm
  have beforeRaw := rawMenu.toRawTrace initial horizon (family seed) prior
  have bound := (tracePrefix_environment_prefix seed before current prior trace kept).length_le
  obtain ⟨past, view, command, recalled, actor⟩ := app.active_environment_entry initial horizon
    (family seed) before beforeRaw bob active
  have commandEq : command = .activate bob := by
    cases command <;> simp_all only [ReactiveApplication.Command.actor?,
      Option.some.injEq, reduceCtorEq]
  subst command
  have entryOriginal := earlier_original_attempt seed before beforeRaw original
    ⟨view, .activate bob⟩ (by
      rw [recalled]
      exact List.mem_append_right _ (List.mem_singleton_self _))
  have consistent := family_commands seed before beforeRaw
  rw [recalled] at consistent
  have chosen := (app.commandConsistent_snoc choose seed past ⟨view, .activate bob⟩).mp
    consistent
  have selected : originalCommand seed past.length past view = .activate bob := by
    rw [choose_original seed past view entryOriginal] at chosen
    exact chosen.2
  have length : before.execution.environmentRecall.length = past.length + 1 := by
    rw [recalled, List.length_append, List.length_singleton]
  have positions := original_activation_positions seed past.length past view bob (by omega)
    selected
  have different : alice ≠ bob := by decide
  have used : past.length = 1 := by
    rcases positions with position | position | position | position | position | position |
      position | position
    · rw [position] at selected
      exact (different (activateReady_owner alice bob aliceBinding view selected)).elim
    · exact position
    · rw [position] at selected
      exact (different (pollCommand_owner alice bob _ false view selected)).elim
    · rw [position] at selected
      exact (different (pollCommand_owner alice bob _ true view selected)).elim
    · rw [position] at selected
      exact (different (activateReady_owner alice bob aliceBinding view selected)).elim
    all_goals omega
  have zero : before.execution.application.current.native.clock = 0 := by
    have clock := original_clock_index seed before beforeRaw original
    rw [length, used] at clock
    exact clock
  constructor
  · rw [observed]
    exact original
  · rw [observed]
    exact zero

/-- Every Bob packet observable before his late block was emitted at his
actual initial callback. Its preparation and application acceptance are arbitrary. -/
theorem bob_packet_before_late_origin (seed : Seeds) (current : app.Control)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace (some current))
    (request : current.execution.application.SeedRequest alice (originalCoordinate alice))
    (early : current.execution.environmentRecall.length ≤ 12)
    (message : Message Player (CommitAttemptPacket graph))
    (input : message ∈ current.execution.network.inputs) (sender : message.sender = bob) :
    ∃ entry ∈ current.execution.recall bob, entry.emitted = some message ∧
      entry.beforeView.application.2.attempt = originalAttempt ∧
      entry.beforeView.application.1.publicView.clock = 0 := by
  classical
  have raw := rawMenu.toRawTrace initial horizon (family seed) trace
  have output : message ∈ app.outputs (current.execution.recall bob) := by
    rw [← app.history_inputRecall initial horizon (family seed) raw bob]
    exact List.mem_filter.mpr ⟨input, by simp only [sender, decide_true]⟩
  obtain ⟨entry, recorded, emitted⟩ := List.mem_filterMap.mp output
  exact ⟨entry, recorded, emitted,
    bob_record_before_late_origin seed current trace request early entry recorded⟩

private theorem observed_packet_input (seed : Seeds) (current : app.Control)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace (some current))
    (observer : Player) (message : Message Player (CommitAttemptPacket graph))
    (visible : message ∈ (current.execution.observe app observer).messages.leaked ∨
      message ∈ (current.execution.observe app observer).messages.ledger) :
    message ∈ current.execution.network.inputs := by
  have raw := rawMenu.toRawTrace initial horizon (family seed) trace
  have retained := app.retained_envelopes_mem_inputs current.execution
    (app.history_provenance initial horizon (family seed) raw)
    (app.history_inputRecall initial horizon (family seed) raw)
  rcases visible with leaked | ledger
  · exact retained.leaked observer message leaked
  · exact retained.ledger message ledger

private theorem receipt_iff_ledger (seed : Seeds) (current : app.Control)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace (some current))
    (message : Message Player (CommitAttemptPacket graph))
    (input : message ∈ current.execution.network.inputs) :
    (∃ accepted, (message.id, accepted) ∈ current.execution.receipts) ↔
      message ∈ current.execution.network.ledger := by
  have raw := rawMenu.toRawTrace initial horizon (family seed) trace
  have identifiers := app.receipt_identifiers_history initial horizon (family seed) current raw
  constructor
  · rintro ⟨accepted, receipt⟩
    have known : message.id ∈ current.execution.network.ledger.map Message.id := by
      rw [← identifiers]
      exact List.mem_map.mpr ⟨(message.id, accepted), receipt, rfl⟩
    obtain ⟨published, ledger, same⟩ := List.mem_map.mp known
    have equal := app.input_envelope_eq_ledger_of_id_eq initial horizon (family seed) current raw
      message published input ledger same.symm
    exact equal.symm ▸ ledger
  · intro ledger
    have known : message.id ∈ current.execution.receipts.map Prod.fst := by
      rw [identifiers]
      exact List.mem_map.mpr ⟨message, ledger, rfl⟩
    obtain ⟨receipt, member, same⟩ := List.mem_map.mp known
    exact ⟨receipt.2, by simpa only [← same, Prod.mk.eta] using member⟩

/-- The full physical input identifies the bit through the original helper
packet's public receipt. A rejected helper packet gives the same timing signal. -/
theorem alice_helper_clock_two_seed (seed : Seeds) (current : app.Control)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace (some current))
    (active : current.actor = some alice)
    (request : current.execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : current.execution.application.current.native.clock = 2)
    (message : Message Player (CommitAttemptPacket graph))
    (sender : message.sender = bob) (addressed : message.payload.attempt = originalAttempt)
    (visible : message ∈ (current.execution.observe app alice).messages.leaked ∨
      message ∈ (current.execution.observe app alice).messages.ledger) :
    seedBits seed alice = true ↔
      ∃ accepted, (message.id, accepted) ∈ (current.execution.observe app alice).receipts := by
  have raw := rawMenu.toRawTrace initial horizon (family seed) trace
  have original : current.execution.application.attempt = originalAttempt := request.1.symm
  have firstClock : current.execution.application.current.native.clock = lateClock alice false :=
    clock
  have count := original_first_late_input_index seed current trace alice active original firstClock
  change current.execution.environmentRecall.length =
    4 + if seedBits seed alice then 3 else 1 at count
  have input := observed_packet_input seed current trace alice message visible
  obtain ⟨entry, recorded, emitted, entryOriginal, zero⟩ :=
    bob_packet_before_late_origin seed current trace request (by split_ifs at count <;> omega)
      message input sender
  cases bit : seedBits seed alice with
  | false =>
      have empty := original_receipts_before_helper seed current raw original (by
        rw [bit] at count
        simp only [Bool.false_eq_true, ite_false] at count
        omega)
      change false = true ↔ ∃ accepted, (message.id, accepted) ∈ current.execution.receipts
      rw [empty]
      simp only [Bool.false_eq_true, List.not_mem_nil, exists_false]
  | true =>
      have after : 5 < current.execution.environmentRecall.length := by
        rw [bit] at count
        simp only [ite_true] at count
        omega
      have receipt := original_early_submission_receipt seed current raw bob entry recorded
        message emitted sender addressed zero original after
      exact ⟨fun _ => receipt, fun _ => rfl⟩

/-- The included-versus-pending distinction is observable in the actual
ledger, independently of the helper packet's successful or failed receipt bit. -/
theorem alice_helper_clock_two_ledger (seed : Seeds) (current : app.Control)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace (some current))
    (active : current.actor = some alice)
    (request : current.execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : current.execution.application.current.native.clock = 2)
    (message : Message Player (CommitAttemptPacket graph))
    (sender : message.sender = bob) (addressed : message.payload.attempt = originalAttempt)
    (visible : message ∈ (current.execution.observe app alice).messages.leaked ∨
      message ∈ (current.execution.observe app alice).messages.ledger) :
    seedBits seed alice = true ↔
      message ∈ (current.execution.observe app alice).messages.ledger :=
  (alice_helper_clock_two_seed seed current trace active request clock message sender addressed
    visible).trans (receipt_iff_ledger seed current trace message
      (observed_packet_input seed current trace alice message visible))

private theorem middle_clock_of_prefix (past : List Nat)
    (clocks : past ++ [3] <+: [0, 2, 3]) : 2 ∈ past := by
  cases past with
  | nil =>
      have impossible : 3 = 0 := (List.cons_prefix_cons.mp clocks).1
      omega
  | cons first rest =>
      have tail := (List.cons_prefix_cons.mp clocks).2
      cases rest with
      | nil =>
          have impossible : 3 = 2 := (List.cons_prefix_cons.mp tail).1
          omega
      | cons second later =>
          have same : second = 2 := (List.cons_prefix_cons.mp tail).1
          exact List.mem_cons_of_mem first (List.mem_cons.mpr (Or.inl same.symm))

/-- A genuine still-unsent clock-three binding callback has a real remembered
clock-two callback. The record is recovered from the actual local clock word. -/
theorem alice_clock_three_remembers_two (seed : Seeds) (current : app.Control)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace (some current))
    (active : current.actor = some alice)
    (request : current.execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : current.execution.application.current.native.clock = 3) :
    ∃ entry ∈ current.execution.recall alice,
      entry.beforeView.application.2.attempt = originalAttempt ∧
      entry.beforeView.application.2.native.clock = 2 := by
  classical
  have raw := rawMenu.toRawTrace initial horizon (family seed) trace
  have original : current.execution.application.attempt = originalAttempt := request.1.symm
  have timer := original_timer (family seed) current raw original aliceBinding (Or.inl rfl)
    request.2.2.1.1
  have calendar := original_service_clocks_prefix rawMenu seed current trace alice active request
  change ((PhaseSeedScheduler.ownerWord runtime leaks (originalCoordinate alice) alice
      (current.execution.recall alice)).map Prod.fst ++
    [current.execution.application.current.native.clock -
      (current.execution.application.current.native.activatedAt aliceBinding).getD
        current.execution.application.current.native.clock]) <+: [0, 2, 3] at calendar
  rw [timer, clock, Option.getD_some, Nat.sub_zero] at calendar
  have middle := middle_clock_of_prefix _ calendar
  obtain ⟨pair, member, elapsed⟩ := List.mem_map.mp middle
  unfold PhaseSeedScheduler.ownerWord at member
  obtain ⟨entry, filtered, equal⟩ := List.mem_map.mp member
  obtain ⟨recorded, _queried⟩ := List.mem_filter.mp filtered
  obtain ⟨before, prior, kept, _acting, observed, _allowed, _later⟩ :=
    rawMenu.recorded_response_prefix initial horizon (family seed) current trace alice entry
      recorded
  have beforeRequest := original_binding_request_of_prefix rawMenu seed before current
    prior trace kept alice request
  have beforeOriginal : before.execution.application.attempt = originalAttempt :=
    beforeRequest.1.symm
  have beforeTimer := original_timer (family seed) before
    (rawMenu.toRawTrace initial horizon (family seed) prior) beforeOriginal aliceBinding
      (Or.inl rfl) beforeRequest.2.2.1.1
  have entryTimer : entry.beforeView.application.2.native.activatedAt aliceBinding = some 0 := by
    rw [observed]
    exact beforeTimer
  have elapsedEntry := (congrArg Prod.fst equal).trans elapsed
  change entry.beforeView.application.2.native.clock -
    (entry.beforeView.application.2.native.activatedAt aliceBinding).getD
      entry.beforeView.application.2.native.clock = 2 at elapsedEntry
  rw [entryTimer, Option.getD_some, Nat.sub_zero] at elapsedEntry
  refine ⟨entry, recorded, ?_, elapsedEntry⟩
  rw [observed]
  exact beforeOriginal

/-- Recall retains the exact helper observation made before Alice's clock-two
response. Its seed readout remains valid at clock three and through later raw histories. -/
theorem alice_recalled_helper_seed (seed : Seeds) (current : app.Control)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace (some current))
    (request : current.execution.application.SeedRequest alice (originalCoordinate alice))
    (entry : app.PlayerEntry) (recorded : entry ∈ current.execution.recall alice)
    (clock : entry.beforeView.application.2.native.clock = 2)
    (message : Message Player (CommitAttemptPacket graph))
    (sender : message.sender = bob) (addressed : message.payload.attempt = originalAttempt)
    (visible : message ∈ entry.beforeView.messages.leaked ∨
      message ∈ entry.beforeView.messages.ledger) :
    seedBits seed alice = true ↔ ∃ accepted,
      (message.id, accepted) ∈ entry.beforeView.receipts := by
  obtain ⟨before, prior, kept, active, observed, _allowed, _later⟩ :=
    rawMenu.recorded_response_prefix initial horizon (family seed) current trace alice entry
      recorded
  have beforeRequest := original_binding_request_of_prefix rawMenu seed before current
    prior trace kept alice request
  rw [observed] at clock visible ⊢
  exact alice_helper_clock_two_seed seed before prior active beforeRequest clock message sender
    addressed visible

/-- This is pointwise information-fiber knowledge, including histories with
zero assessed probability. No equilibrium strategy or posterior is used. -/
theorem alice_helper_clock_two_seed_eq_of_view (leftSeed rightSeed : Seeds)
    (left right : app.Control)
    (leftTrace : (rawMenu.protocol initial horizon (family leftSeed)).Trace (some left))
    (rightTrace : (rawMenu.protocol initial horizon (family rightSeed)).Trace (some right))
    (leftActive : left.actor = some alice) (rightActive : right.actor = some alice)
    (leftRequest : left.execution.application.SeedRequest alice (originalCoordinate alice))
    (rightRequest : right.execution.application.SeedRequest alice (originalCoordinate alice))
    (leftClock : left.execution.application.current.native.clock = 2)
    (rightClock : right.execution.application.current.native.clock = 2)
    (sameView : left.execution.observe app alice = right.execution.observe app alice)
    (message : Message Player (CommitAttemptPacket graph))
    (sender : message.sender = bob) (addressed : message.payload.attempt = originalAttempt)
    (visible : message ∈ (left.execution.observe app alice).messages.leaked ∨
      message ∈ (left.execution.observe app alice).messages.ledger) :
    seedBits leftSeed alice = seedBits rightSeed alice := by
  have leftRead := alice_helper_clock_two_seed leftSeed left leftTrace leftActive leftRequest
    leftClock message sender addressed visible
  have rightRead := alice_helper_clock_two_seed rightSeed right rightTrace rightActive rightRequest
    rightClock message sender addressed (sameView ▸ visible)
  rw [sameView] at leftRead
  have equivalent := leftRead.trans rightRead.symm
  cases leftBit : seedBits leftSeed alice <;> cases rightBit : seedBits rightSeed alice
  · rfl
  · rw [leftBit, rightBit] at equivalent
    have impossible := equivalent.mpr rfl
    cases impossible
  · rw [leftBit, rightBit] at equivalent
    have impossible := equivalent.mp rfl
    cases impossible
  · rfl

/-- An identical remembered clock-two observation gives identical seed knowledge
at the later callback. No equality of the hidden environment transcripts is assumed. -/
theorem alice_recalled_helper_seed_eq_of_recall (leftSeed rightSeed : Seeds)
    (left right : app.Control)
    (leftTrace : (rawMenu.protocol initial horizon (family leftSeed)).Trace (some left))
    (rightTrace : (rawMenu.protocol initial horizon (family rightSeed)).Trace (some right))
    (leftRequest : left.execution.application.SeedRequest alice (originalCoordinate alice))
    (rightRequest : right.execution.application.SeedRequest alice (originalCoordinate alice))
    (sameRecall : left.execution.recall alice = right.execution.recall alice)
    (entry : app.PlayerEntry) (recorded : entry ∈ left.execution.recall alice)
    (clock : entry.beforeView.application.2.native.clock = 2)
    (message : Message Player (CommitAttemptPacket graph))
    (sender : message.sender = bob) (addressed : message.payload.attempt = originalAttempt)
    (visible : message ∈ entry.beforeView.messages.leaked ∨
      message ∈ entry.beforeView.messages.ledger) :
    seedBits leftSeed alice = seedBits rightSeed alice := by
  have leftRead := alice_recalled_helper_seed leftSeed left leftTrace leftRequest entry recorded
    clock message sender addressed visible
  have rightRead := alice_recalled_helper_seed rightSeed right rightTrace rightRequest entry
    (sameRecall ▸ recorded) clock message sender addressed visible
  have equivalent := leftRead.trans rightRead.symm
  cases leftBit : seedBits leftSeed alice <;> cases rightBit : seedBits rightSeed alice
  · rfl
  · rw [leftBit, rightBit] at equivalent
    have impossible := equivalent.mpr rfl
    cases impossible
  · rw [leftBit, rightBit] at equivalent
    have impossible := equivalent.mp rfl
    cases impossible
  · rfl

end Vegas.Examples.CommitSeedSignalling
