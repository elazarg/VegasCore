/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.OddsEvensService
import Interaction.ReactivePendingProcessing
import Vegas.Examples.OddsEvensServiceCapacity
import Vegas.Examples.OddsEvensServiceClock
import Interaction.ReactiveRecallInvariant
import Interaction.ReactiveAnchoredTrace
import Interaction.ReactiveReceiptIdentity
import Interaction.ReactivePublication
import Interaction.ReactiveMonitoring

/-! # Actual queue processing in the forced-exit service -/

noncomputable section

namespace Vegas.Examples.OddsEvensService

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Math.Probability

private theorem old_response_mem_before (inputs : compiled.Inputs)
    (players : OddsEvens.Player → app.Policy) (count : Nat) (before after : app.Execution)
    (valid : before.application.Invariant inputs)
    (reached : after ∈ ((app).runRounds scheduler players count before).support)
    (owner : OddsEvens.Player) (entry : app.PlayerEntry)
    (recorded : entry ∈ after.logs owner)
    (old : entry.beforeView.application.publicView.clock <
      before.application.clock) : entry ∈ before.logs owner := by
  let predicate := fun execution : (app).Execution =>
    execution.application.Invariant inputs ∧
      before.application.clock ≤ execution.application.clock ∧
      ∀ who remembered, remembered ∈ execution.logs who →
        remembered ∈ before.logs who ∨ before.application.clock ≤
          remembered.beforeView.application.publicView.clock
  have invariant : (app).PolicyInvariant players predicate := {
    respond := by
      intro execution actor action prior _
      have progress := reactive_respond_progress timeouts leaks inputs execution actor action
        prior.1
      have monotone : execution.application.clock ≤
          (execution.respond app actor action).application.clock := by
        rw [progress.clock]
        omega
      refine ⟨progress.invariant, prior.2.1.trans monotone, ?_⟩
      intro who remembered member
      rcases (app).respond_entry_origin execution actor who action remembered member with
        earlier | fresh
      · exact prior.2.2 who remembered earlier
      · right
        rw [fresh.2]
        exact prior.2.1
    environment := by
      intro execution next command prior moved
      have progress := reactive_environment_progress timeouts leaks inputs execution next command
        prior.1 moved
      have monotone : execution.application.clock ≤ next.application.clock := by
        rw [progress.clock]
        omega
      refine ⟨progress.invariant, prior.2.1.trans monotone, ?_⟩
      intro who remembered member
      rw [(app).environmentStep_recall execution next command moved] at member
      exact prior.2.2 who remembered member }
  have cut := invariant.runRounds scheduler count before after
    ⟨valid, le_rfl, fun _ _ member => Or.inl member⟩ reached
  exact (cut.2.2 owner entry recorded).resolve_right (Nat.not_le_of_lt old)


/-- During a processing segment no player is activated, even under arbitrary
raw response policies. The resulting execution is the deterministic batch. -/
theorem processing_segment_law (players : OddsEvens.Player → app.Policy)
    (cycle slot count : Nat) (execution : app.Execution)
    (inside : slot + count ≤ packetBudget)
    (cursor : execution.environmentRecall.length = cycle * width + slot) :
    app.runRounds scheduler players count execution =
      PMF.pure (app.processPendingBatch count execution) := by
  induction count generalizing slot execution with
  | zero => rfl
  | succ count ih =>
      have small : slot < packetBudget := by omega
      have selected : scheduler execution.environmentRecall (execution.observeEnvironment app) =
          PMF.pure (app.pendingHeadCommand (execution.observeEnvironment app)) := by
        simp only [scheduler, cursor, processing_command cycle slot _ small]
      rw [ReactiveApplication.runRounds, ReactiveApplication.round, selected, PMF.pure_bind,
        app.processPendingHead_dispatch, PMF.pure_bind]
      have nextCursor : (app.processPendingHead execution).environmentRecall.length =
          cycle * width + (slot + 1) := by
        rw [app.processPendingHead_environmentLength, cursor]
        omega
      exact ih (slot + 1) (app.processPendingHead execution) (by omega) nextCursor

/-- A bounded processing segment receipts every envelope present at its start,
including rejected calls, without altering any player's recall. -/
theorem processing_segment (players : OddsEvens.Player → app.Policy)
    (cycle slot : Nat) (execution : app.Execution)
    (inside : slot + execution.network.pending.length ≤ packetBudget)
    (cursor : execution.environmentRecall.length = cycle * width + slot)
    (next : app.Execution)
    (reached : next ∈ (app.runRounds scheduler players execution.network.pending.length
      execution).support) :
    next.network.pending = [] ∧
      next.network.ledger = execution.network.ledger ++ execution.network.pending ∧
      next.logs = execution.logs ∧
      next.environmentRecall.length = execution.environmentRecall.length +
        execution.network.pending.length ∧
      ∀ message ∈ execution.network.pending,
        ∃ accepted, (message.id, accepted) ∈ next.receipts := by
  rw [processing_segment_law players cycle slot _ execution inside cursor,
    PMF.mem_support_pure_iff] at reached
  subst next
  refine ⟨?_, ?_, app.processPendingBatch_recall _ _,
    app.processPendingBatch_environmentLength _ _, ?_⟩
  · rw [app.processPendingBatch_pending, List.drop_length]
  · rw [app.processPendingBatch_ledger, List.take_length]
  · intro message present
    apply app.processPendingBatch_receipt
    rwa [List.take_length]

/-- A complete processing block receipts all earlier submissions, including
packets whose application call is rejected. -/
theorem processing_covers_inputs (remaining cycle : Nat) (before after : app.Execution)
    (trace : (app.protocol initial horizon scheduler).Trace (some ⟨remaining, none, before⟩))
    (cursor : before.environmentRecall.length = cycle * width)
    (players : OddsEvens.Player → app.Policy)
    (reached : after ∈ (app.runRounds scheduler players packetBudget before).support)
    (message : Message OddsEvens.Player app.Payload) (submitted : message ∈ before.network.inputs) :
    ∃ accepted, (message.id, accepted) ∈ after.receipts := by
  have capacity := pending_le_budget ⟨remaining, none, before⟩ trace
  rw [processing_segment_law players cycle 0 packetBudget before (by omega) (by omega),
    PMF.mem_support_pure_iff] at reached
  subst after
  have retained := app.pendingOrPublished_history scheduler initial horizon trace
  rcases retained.inputs message submitted with pending | published
  · apply app.processPendingBatch_receipt
    rwa [List.take_of_length_le capacity]
  · have identifiers := app.receipt_identifiers_history initial horizon scheduler _ trace
    have recorded : message.id ∈ before.receipts.map Prod.fst := by
      rw [identifiers]
      exact List.mem_map.mpr ⟨message, published, rfl⟩
    obtain ⟨receipt, member, equal⟩ := List.mem_map.mp recorded
    refine ⟨receipt.2, app.processPendingBatch_receipts_mono _ _ ?_⟩
    simpa only [← equal, Prod.mk.eta] using member

/-- A submitted envelope is receipted by the next complete processing block,
and that receipt persists through arbitrary subsequent raw play. -/
theorem submitted_receipt_after_block (remaining cycle count : Nat)
    (before after : app.Execution)
    (trace : (app.protocol initial horizon scheduler).Trace (some ⟨remaining, none, before⟩))
    (cursor : before.environmentRecall.length = cycle * width)
    (players : OddsEvens.Player → app.Policy) (room : packetBudget ≤ count)
    (reached : after ∈ (app.runRounds scheduler players count before).support)
    (owner : OddsEvens.Player) (entry : app.PlayerEntry)
    (recorded : entry ∈ before.logs owner)
    (message : Message OddsEvens.Player app.Payload) (emitted : entry.emitted = some message) :
    ∃ accepted, (message.id, accepted) ∈ after.receipts := by
  have inputRecall := app.history_inputRecall initial horizon scheduler trace
  have submitted : message ∈ before.network.inputs := by
    have remembered : message ∈ app.outputs (before.logs owner) :=
      List.mem_filterMap.mpr ⟨entry, recorded, emitted⟩
    rw [← inputRecall owner] at remembered
    exact (List.mem_filter.mp remembered).1
  have restSplit : packetBudget + (count - packetBudget) = count := by omega
  have restLaw := app.runRounds_add scheduler players packetBudget (count - packetBudget) before
  rw [restSplit] at restLaw
  rw [restLaw] at reached
  obtain ⟨afterBlock, processed, continued⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨accepted, receipted⟩ := processing_covers_inputs _ cycle before afterBlock trace
    cursor players processed message submitted
  exact ⟨accepted, (app.receipt_policyInvariant players (message.id, accepted)).runRounds scheduler
    (count - packetBudget) afterBlock after receipted continued⟩

/-- An old recalled response predates a processing boundary, and its packet
therefore has a receipt after the full block following that boundary. -/
theorem receipt_after_boundary (inputs : compiled.Inputs)
    (initialMember : ((State.initial inputs) : app.State) ∈ initial.support)
    (players : OddsEvens.Player → app.Policy) (cycle count : Nat)
    (cycleBound : cycle * width ≤ horizon) (room : packetBudget ≤ count)
    (before execution : app.Execution)
    (prefixReached : before ∈ (app.runRounds scheduler players (cycle * width)
      (ReactiveApplication.Execution.initial app (State.initial inputs))).support)
    (suffixReached : execution ∈ (app.runRounds scheduler players count before).support)
    (owner : OddsEvens.Player) (entry : app.PlayerEntry)
    (recorded : entry ∈ execution.logs owner)
    (old : entry.beforeView.application.publicView.clock < cycle)
    (message : Message OddsEvens.Player app.Payload) (emitted : entry.emitted = some message) :
    ∃ accepted, (message.id, accepted) ∈ execution.receipts := by
  let start := ReactiveApplication.Execution.initial app ((State.initial inputs) : app.State)
  have initialAligned : ClockAligned inputs 0 start :=
    ⟨State.initial_invariant _, by
      simp [start, ReactiveApplication.Execution.initial, State.initial]⟩
  have beforeAligned := (clock_aligned_invariant inputs 0).runRounds players (cycle * width)
    start before initialAligned prefixReached
  have beforeCursor : before.environmentRecall.length = cycle * width := by
    simpa only [start, ReactiveApplication.Execution.initial, List.length_nil, Nat.zero_add] using
      app.runRounds_environmentRecall_length scheduler players (cycle * width) start before
        prefixReached
  have beforeClock : before.application.clock = cycle := by
    rw [beforeAligned.clock, beforeCursor, Nat.zero_add]
    exact (cursor_arithmetic cycle 0 (by decide)).1
  have priorEntry := old_response_mem_before inputs players
    count before execution beforeAligned.valid suffixReached owner entry
      recorded (by rw [beforeClock]; exact old)
  have prefixRounds : before ∈
      (app.roundsFrom initial scheduler players (cycle * width)).support := by
    rw [ReactiveApplication.roundsFrom, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨_, initialMember, prefixReached⟩
  obtain ⟨beforeTrace⟩ := app.raw_trace_roundsFrom initial horizon scheduler players (cycle * width)
    cycleBound before prefixRounds
  exact submitted_receipt_after_block _ cycle count before execution beforeTrace
    beforeCursor players room suffixReached owner entry priorEntry message emitted

private theorem processing_cut_indices (sent used : Nat) (bounded : used ≤ horizon)
    (elapsed : sent + 2 < used / width) :
    let cut := (sent + 1) * width
    cut + (used - cut) = used ∧ cut ≤ horizon ∧ packetBudget ≤ used - cut := by
  change let cut := (sent + 1) * 71
    cut + (used - cut) = used ∧ cut ≤ 2272 ∧ 64 ≤ used - cut
  change used ≤ 2272 at bounded
  change sent + 2 < used / 71 at elapsed
  omega

/-- A run starting from a supported initialized state receipts every old
emission. Clock accounting places a complete processing block between them. -/
theorem initialized_run_receipt (inputs : compiled.Inputs)
    (initialMember : ((State.initial inputs) : app.State) ∈ initial.support)
    (players : OddsEvens.Player → app.Policy) (used : Nat) (bounded : used ≤ horizon)
    (execution : app.Execution)
    (reached : execution ∈ (app.runRounds scheduler players used
      (ReactiveApplication.Execution.initial app (State.initial inputs))).support)
    (clock : execution.application.clock = used / width)
    (owner : OddsEvens.Player) (entry : app.PlayerEntry) (recorded : entry ∈ execution.logs owner)
    (message : Message OddsEvens.Player app.Payload) (emitted : entry.emitted = some message)
    (elapsed : entry.beforeView.application.publicView.clock + 2 <
      execution.application.clock) :
    ∃ accepted, (message.id, accepted) ∈ execution.receipts := by
  let start := ReactiveApplication.Execution.initial app ((State.initial inputs) : app.State)
  let cycle := entry.beforeView.application.publicView.clock + 1
  have indices := processing_cut_indices entry.beforeView.application.publicView.clock used
    bounded (by rwa [← clock])
  have splitCount : cycle * width + (used - cycle * width) = used := indices.1
  have splitLaw := app.runRounds_add scheduler players (cycle * width)
    (used - cycle * width) start
  rw [splitCount] at splitLaw
  rw [splitLaw] at reached
  obtain ⟨before, prefixReached, suffixReached⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  exact receipt_after_boundary inputs initialMember players cycle (used - cycle * width)
    indices.2.1 indices.2.2 before execution prefixReached suffixReached owner entry recorded
    (Nat.lt_succ_self _) message emitted

/-- Every sufficiently old raw emission has already received an actual ledger
receipt. The claim includes off-path traffic and histories after exclusion. -/
theorem idle_emission_receipt (remaining : Nat) (execution : app.Execution)
    (trace : (app.protocol initial horizon scheduler).Trace (some ⟨remaining, none, execution⟩))
    (owner : OddsEvens.Player) (entry : app.PlayerEntry) (recorded : entry ∈ execution.logs owner)
    (message : Message OddsEvens.Player app.Payload) (emitted : entry.emitted = some message)
    (elapsed : entry.beforeView.application.publicView.clock + 2 <
      execution.application.clock) :
    ∃ accepted, (message.id, accepted) ∈ execution.receipts := by
  let fallback : OddsEvens.Player → app.Policy := fun _ => app.silentPolicy
  let players := app.anchoredPolicy execution fallback
  let used := horizon - remaining
  obtain ⟨bounded, supported⟩ := app.mem_roundsFrom_anchoredPolicy_of_trace initial horizon
    scheduler fallback trace
  change execution ∈ (initial.bind fun state => app.runRounds scheduler players used
    (ReactiveApplication.Execution.initial app state)).support at supported
  obtain ⟨state, initialized, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  have initialMember := initialized
  rw [initial, Vegas.initialLaw, serviceInitialLaw, PMF.support_map] at initialized
  obtain ⟨input, _inputSupported, rfl⟩ := initialized
  let inputs := fixture.eventInputs input
  let start := ReactiveApplication.Execution.initial app ((State.initial inputs) : app.State)
  have recalledEq : execution.environmentRecall.length = used := by
    simpa only [start, ReactiveApplication.Execution.initial, List.length_nil, Nat.zero_add]
      using app.runRounds_environmentRecall_length scheduler players used start execution reached
  have clock : execution.application.clock = used / width := by
    rw [clock_history ⟨remaining, none, execution⟩ trace, recalledEq]
  exact initialized_run_receipt inputs initialMember players used (Nat.sub_le _ _) execution
    reached clock owner entry recorded message emitted elapsed

/-- Responding silently to an active callback does not change its receipts or
clock, so the idle receipt bound also covers active raw controls. -/
theorem emission_receipt (current : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some current))
    (owner : OddsEvens.Player) (entry : app.PlayerEntry)
    (recorded : entry ∈ current.execution.logs owner)
    (message : Message OddsEvens.Player app.Payload) (emitted : entry.emitted = some message)
    (elapsed : entry.beforeView.application.publicView.clock + 2 <
      current.execution.application.clock) :
    ∃ accepted, (message.id, accepted) ∈ current.execution.receipts := by
  rcases current with ⟨remaining, actor, execution⟩
  cases actor with
  | none =>
      exact idle_emission_receipt remaining execution trace owner entry recorded message emitted
        elapsed
  | some actor =>
      obtain ⟨quietTrace⟩ := app.raw_trace_respond initial horizon scheduler remaining execution
        actor ⟨none⟩ trace
      have quietRecorded := app.respond_recall_mono execution actor owner ⟨none⟩ recorded
      obtain ⟨accepted, received⟩ := idle_emission_receipt remaining
        (execution.respond app actor ⟨none⟩) quietTrace owner entry quietRecorded message
          emitted elapsed
      exact ⟨accepted, by simpa only [app.respond_receipts] using received⟩

/-- The concrete forced-exit service supplies protected inclusion on every raw
history; the bound does not require successful application acceptance. -/
theorem protectedInclusion :
    ProtectedInclusion timeouts leaks initial horizon scheduler (fun _ => 2) := by
  intro current trace event owner _acting earlier later entry message recalled emitted _sender
    _event _ready _sole _unfinished elapsed
  have member : entry ∈ current.execution.logs owner := by
    rw [recalled]
    exact List.mem_append_right _ List.mem_cons_self
  exact emission_receipt current trace owner entry member message emitted elapsed

end Vegas.Examples.OddsEvensService
