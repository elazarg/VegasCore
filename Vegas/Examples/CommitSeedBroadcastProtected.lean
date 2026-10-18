/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastInitialPacketOrigins
import Vegas.Examples.CommitSeedBroadcastOriginalZeroSnapshot
import Vegas.Examples.CommitSeedBroadcastRecordedReceipt
import Vegas.Pending.PhaseAttemptCheckpoint
import Interaction.ReactivePublication
import Interaction.ReactiveReceiptIdentity

/-! # Protected physical inclusion for arbitrary raw responses -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

def earlyPosition (seeds : Seeds) (owner : Player) : Nat :=
  8 + (seeds.1.symm owner).val

private theorem earlyPosition_bounds (seeds : Seeds) (owner : Player) :
    8 ≤ earlyPosition seeds owner ∧ earlyPosition seeds owner ≤ 10 := by
  have bounded := (seeds.1.symm owner).isLt
  unfold earlyPosition
  omega

private theorem original_early_command (seeds : Seeds) (owner : Player)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) :
    originalCommand seeds (earlyPosition seeds owner) past view = earlyCommand owner past view := by
  unfold earlyPosition
  generalize turnEq : seeds.1.symm owner = turn
  have named : seeds.1 turn = owner := by
    rw [← turnEq]
    exact seeds.1.apply_symm_apply owner
  fin_cases turn <;>
    simpa only [originalCommand, Fin.reduceFinMk, Nat.reduceAdd] using
      congrArg (fun who => earlyCommand who past view) named

private theorem raw_snapshot_unique_owner (seeds : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (app.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩)) (past : 4 ≤ execution.environmentRecall.length)
    (snapshot : app.EnvironmentEntry) (selected : execution.environmentRecall[3]? = some snapshot)
    (owner : Player) (first second : Message Player (CommitAttemptPacket graph))
    (firstInput : first ∈ snapshot.beforeView.network.inputs)
    (secondInput : second ∈ snapshot.beforeView.network.inputs)
    (firstOwner : first.sender = owner) (secondOwner : second.sender = owner) : first = second := by
  let fallback : Player → app.Policy := fun _ => app.silentPolicy
  let players := ReactiveApplication.anchoredPolicy execution fallback
  have actual := ReactiveApplication.mem_roundsFrom_anchoredPolicy_of_trace initial horizon
    (family seeds) fallback trace
  have reached : execution ∈ (app.runRounds (family seeds) players (horizon - remaining)
      initialExecution).support := by
    simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind,
      initialExecution] using actual.2
  have accounted := app.raw_trace_horizon initial horizon (family seeds) trace
  change execution.environmentRecall.length + remaining = horizon at accounted
  let extra := execution.environmentRecall.length - 4
  have count : horizon - remaining = 4 + extra := by dsimp [extra]; omega
  rw [count] at reached
  exact first_snapshot_unique_owner seeds players extra execution reached snapshot selected owner
    first second firstInput secondInput firstOwner secondOwner

private theorem pending_selected_receipt (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (message : Message Player (CommitAttemptPacket graph))
    (input : message ∈ current.execution.network.inputs) (next : app.Execution)
    (reached : next ∈ (current.execution.environmentStep app
      (pendingCommand message.id (current.execution.observeEnvironment app))).support) :
    ∃ accepted, (message.id, accepted) ∈ next.receipts := by
  have retained := app.pendingOrPublished_history (family seeds) initial horizon trace
  rcases retained.inputs message input with pending | published
  · have any : current.execution.network.pending.any (fun packet => packet.id = message.id) =
        true := List.any_eq_true.mpr ⟨message, pending, by simp⟩
    have selected : pendingCommand message.id (current.execution.observeEnvironment app) =
        .include message.id := by
      unfold pendingCommand
      exact ite_eq_left any
    rw [selected] at reached
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
    cases (PMF.mem_support_pure_iff _ _).mp reached
    cases lookup : current.execution.network.lookup message.id with
    | none =>
        have absent := List.find?_eq_none.mp lookup message pending
        exact (absent (by simp)).elim
    | some packet =>
        unfold ReactiveApplication.Execution.includePending
        simp only [MessageNetwork.includePending, lookup]
        exact ⟨_, List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩
  · have identifiers := app.receipt_identifiers_history initial horizon (family seeds) current trace
    have receiptId : message.id ∈ current.execution.receipts.map Prod.fst := by
      rw [identifiers]
      exact List.mem_map.mpr ⟨message, published, rfl⟩
    obtain ⟨receipt, member, same⟩ := List.mem_map.mp receiptId
    refine ⟨receipt.2, ?_⟩
    have caught := (app.environmentStep_receipts_prefix current.execution next _ reached).subset
      member
    simpa only [← same, Prod.mk.eta] using caught

private def EarlyAccounted (seeds : Seeds) : app.Execution → Prop := fun execution =>
  ∀ owner entry, entry ∈ execution.recall owner → ∀ message, entry.emitted = some message →
    message.sender = owner → message.payload.attempt = originalAttempt →
    entry.beforeView.application.1.publicView.clock = 0 →
    execution.application.attempt = originalAttempt →
    earlyPosition seeds owner < execution.environmentRecall.length →
    ∃ accepted, (message.id, accepted) ∈ execution.receipts

private theorem early_accounted_history (seeds : Seeds) :
    ∀ {state} (_trace : (app.protocol initial horizon (family seeds)).Trace state),
      state.elim True (fun current => EarlyAccounted seeds current.execution) := by
  intro state trace
  induction trace with
  | start => trivial
  | @extend source target prior joint legal reached ih =>
      have targetTrace := prior.extend joint legal reached
      change target ∈ (app.transition initial horizon (family seeds) source joint).support
        at reached
      cases source with
      | none =>
          obtain ⟨state, _supported, rfl⟩ := PMF.support_map .. ▸ reached
          intro owner entry member
          exact (List.not_mem_nil member).elim
      | some current =>
          rcases current with ⟨remaining, active, execution⟩
          cases active with
          | some actor =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              generalize actionEq : (joint actor).getD (⟨none⟩ : app.Action) = action
              intro owner entry member message emitted authored addressed zero original later
              have sameAttempt : (execution.respond app actor action).application.attempt =
                  execution.application.attempt := by
                rcases action with ⟨transmission⟩
                cases transmission <;> rfl
              have originalBefore : execution.application.attempt = originalAttempt :=
                sameAttempt.symm.trans original
              rw [app.respond_environmentRecall] at later
              by_cases old : entry ∈ execution.recall owner
              · obtain ⟨accepted, receipt⟩ := ih owner entry old message emitted authored addressed
                  zero originalBefore later
                exact ⟨accepted, (app.respond_receipts execution actor action).symm ▸ receipt⟩
              · have sameOwner : owner = actor := by
                  by_contra different
                  rw [app.respond_recall_other execution actor owner different action] at member
                  exact old member
                clear authored
                subst owner
                rcases action with ⟨transmission⟩
                cases transmission with
                | none =>
                    simp only [ReactiveApplication.Execution.respond, ↓reduceIte, List.mem_append,
                      List.mem_singleton] at member
                    rcases member with before | rfl
                    · exact (old before).elim
                    · cases emitted
                | some submission =>
                    simp only [ReactiveApplication.Execution.respond, MessageNetwork.submit,
                      ↓reduceIte, List.mem_append, List.mem_singleton] at member
                    rcases member with before | rfl
                    · exact (old before).elim
                    · have index := original_zero_clock_index seeds
                        ⟨remaining, some actor, execution⟩ prior originalBefore zero
                      have lower := (earlyPosition_bounds seeds actor).1
                      omega
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, selected, moved⟩ := Set.mem_iUnion₂.mp
                    (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  intro owner entry member message emitted authored addressed zero original later
                  change next.application.attempt = originalAttempt at original
                  change earlyPosition seeds owner < next.environmentRecall.length at later
                  rw [app.environmentStep_recall execution next command supported] at member
                  have geometry := raw_phase_geometry (family seeds)
                    ⟨remaining + 1, none, execution⟩ prior
                  have namespaces := phaseApplication_namespace_progress runtime leaks
                  have bounds := namespaces.environmentStep execution next command supported
                    geometry.1.adjacent
                  have originalBefore : execution.application.attempt = originalAttempt := by
                    rw [original] at bounds
                    generalize identifierEq : execution.application.attempt = identifier at bounds ⊢
                    rcases identifier with ⟨phase, generation⟩
                    change generation ≤ 0 ∧ phase ≤ 0 at bounds
                    have phaseEq : phase = 0 := by omega
                    have generationEq : generation = 0 := by omega
                    subst phase
                    subst generation
                    rfl
                  have entries := app.environmentStep_environmentRecall execution next command
                    supported
                  by_cases earlier : earlyPosition seeds owner < execution.environmentRecall.length
                  · obtain ⟨accepted, receipt⟩ := ih owner entry member message emitted authored
                      addressed zero originalBefore earlier
                    exact ⟨accepted,
                      (app.environmentStep_receipts_prefix execution next command supported).subset
                        receipt⟩
                  · have position : execution.environmentRecall.length =
                        earlyPosition seeds owner := by
                      rw [entries, List.length_append, List.length_singleton] at later
                      omega
                    have past : 4 ≤ execution.environmentRecall.length := by
                      have lower := (earlyPosition_bounds seeds owner).1
                      omega
                    have stamped := phase_recalled_emission_attempt runtime leaks initial horizon
                      (family seeds) prior owner entry member message emitted
                    obtain ⟨snapshot, snapshotEq, packetInput⟩ := raw_clock_zero_packet_in_snapshot
                      seeds ⟨remaining + 1, none, execution⟩ prior owner entry member message
                        emitted
                      (stamped.symm.trans addressed) zero past
                    let predicate := fun packet : Message Player (CommitAttemptPacket graph) =>
                      decide (packet.sender = owner ∧ packet.payload.attempt = originalAttempt)
                    have findEq : snapshot.beforeView.network.inputs.find? predicate =
                        some message := by
                      cases found : snapshot.beforeView.network.inputs.find? predicate with
                      | none =>
                          have absent := List.find?_eq_none.mp found message packetInput
                          exact (absent (by simp only [predicate, authored, addressed,
                            and_self, decide_true])).elim
                      | some packet =>
                          have input := List.mem_of_find?_eq_some found
                          have predicateResult : predicate packet = true := List.find?_some found
                          change decide (packet.sender = owner ∧
                            packet.payload.attempt = originalAttempt) = true at predicateResult
                          have metadata := of_decide_eq_true predicateResult
                          have equal := raw_snapshot_unique_owner seeds (remaining + 1) execution
                            prior past snapshot snapshotEq owner packet message input packetInput
                            metadata.1 authored
                          exact congrArg some equal
                    have chosen : command = earlyCommand owner execution.environmentRecall
                        (execution.observeEnvironment app) := by
                      have actual : command = originalCommand seeds
                          execution.environmentRecall.length
                          execution.environmentRecall (execution.observeEnvironment app) := by
                        exact ((PMF.mem_support_pure_iff _ _).mp selected).trans
                          (choose_original seeds _ _ originalBefore)
                      rw [position] at actual
                      exact actual.trans (original_early_command seeds owner _ _)
                    have selector : earlyCommand owner execution.environmentRecall
                        (execution.observeEnvironment app) =
                        pendingCommand message.id (execution.observeEnvironment app) := by
                      unfold earlyCommand
                      rw [snapshotEq]
                      change (match snapshot.beforeView.network.inputs.find? predicate with
                        | none => (.wait : app.Command)
                        | some packet => pendingCommand packet.id
                            (execution.observeEnvironment app)) = _
                      rw [findEq]
                    have own : message ∈ app.outputs (execution.recall owner) :=
                      List.mem_filterMap.mpr ⟨entry, member, emitted⟩
                    have recalled := app.history_inputRecall initial horizon (family seeds) prior
                    rw [← recalled owner] at own
                    exact pending_selected_receipt seeds ⟨remaining + 1, none, execution⟩ prior
                      message (List.mem_filter.mp own).1 next ((chosen.trans selector) ▸ supported)

/-- The original early packet is physically receipted after its exact marker
turn, provided the original full namespace is still live. -/
theorem original_early_submission_receipt (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (owner : Player) (entry : app.PlayerEntry) (member : entry ∈ current.execution.recall owner)
    (message : Message Player (CommitAttemptPacket graph)) (emitted : entry.emitted = some message)
    (authored : message.sender = owner) (addressed : message.payload.attempt = originalAttempt)
    (zero : entry.beforeView.application.1.publicView.clock = 0)
    (original : current.execution.application.attempt = originalAttempt)
    (late : earlyPosition seeds owner < current.execution.environmentRecall.length) :
    ∃ accepted, (message.id, accepted) ∈ current.execution.receipts :=
  early_accounted_history seeds trace owner entry member message emitted authored addressed zero
    original late

private theorem snapshot_receipt_idle (seeds : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (app.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (original : execution.application.attempt = originalAttempt)
    (past : 11 ≤ execution.environmentRecall.length)
    (snapshot : app.EnvironmentEntry) (selected : execution.environmentRecall[3]? = some snapshot)
    (owner : Player) (message : Message Player (CommitAttemptPacket graph))
    (input : message ∈ snapshot.beforeView.network.inputs) (authored : message.sender = owner)
    (addressed : message.payload.attempt = originalAttempt) :
    ∃ accepted, (message.id, accepted) ∈ execution.receipts := by
  obtain ⟨entry, member, _material, _transmitted, emitted, _attempt, zero⟩ :=
    snapshot_packet_original_clock_zero seeds remaining execution trace snapshot selected owner
      message input authored
  have upper := (earlyPosition_bounds seeds owner).2
  have passed : earlyPosition seeds owner < execution.environmentRecall.length := by omega
  exact original_early_submission_receipt seeds ⟨remaining, none, execution⟩ trace owner entry
    member message emitted authored addressed zero original passed

/-- Every original packet in the immutable initial snapshot receives a physical
receipt by the end of the middle block while its full namespace remains live.
This allows arbitrary raw content and either native admission result. -/
theorem original_snapshot_submission_receipt (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (original : current.execution.application.attempt = originalAttempt)
    (past : 11 ≤ current.execution.environmentRecall.length)
    (snapshot : app.EnvironmentEntry)
    (selected : current.execution.environmentRecall[3]? = some snapshot)
    (owner : Player) (message : Message Player (CommitAttemptPacket graph))
    (input : message ∈ snapshot.beforeView.network.inputs) (authored : message.sender = owner)
    (addressed : message.payload.attempt = originalAttempt) :
    ∃ accepted, (message.id, accepted) ∈ current.execution.receipts := by
  rcases current with ⟨remaining, active, execution⟩
  cases active with
  | none =>
      exact snapshot_receipt_idle seeds remaining execution trace original past snapshot selected
        owner message input authored addressed
  | some actor =>
      obtain ⟨afterTrace⟩ := app.raw_trace_respond initial horizon (family seeds) remaining
        execution actor ⟨none⟩ trace
      have received := snapshot_receipt_idle seeds remaining
        (execution.respond app actor ⟨none⟩) afterTrace original
        (by simpa only [app.respond_environmentRecall] using past) snapshot
        (by simpa only [app.respond_environmentRecall] using selected) owner message input authored
        addressed
      simpa only [app.respond_receipts] using received

/-- The concrete service satisfies protected inclusion on every raw history.
Neither a counted response nor native acceptance is assumed. -/
theorem family_protected_inclusion (seeds : Seeds) :
    PhaseService.ProtectedInclusion runtime leaks initial horizon (family seeds) (fun _ => 5) := by
  intro current trace coordinate owner _actor earlier later entry message recalled emitted authored
    addressed _event _ready _sole sameAttempt _unfinished late
  have member : entry ∈ current.execution.recall owner := by rw [recalled]; simp
  by_cases tail : entry.beforeView.application.2.attempt ≠ originalAttempt
  · exact tail_protected_submission_receipt seeds current trace owner entry member message emitted
      tail late
  · have originalEntry : entry.beforeView.application.2.attempt = originalAttempt := by
      simpa only [ne_eq, not_not] using tail
    have stamped := phase_recalled_emission_attempt runtime leaks initial horizon (family seeds)
      trace owner entry member message emitted
    have originalPacket := stamped.trans originalEntry
    have original : current.execution.application.attempt = originalAttempt :=
      sameAttempt.trans (addressed.symm.trans originalPacket)
    have zero := original_protected_send_clock_zero seeds current trace original entry late
    have markerPast : earlyPosition seeds owner < current.execution.environmentRecall.length := by
      by_contra before
      have upper := (earlyPosition_bounds seeds owner).2
      have count : current.execution.environmentRecall.length ≤ 10 := by omega
      have clock : current.execution.application.current.native.clock ≤ 2 := by
        rw [original_clock_index seeds current trace original]
        generalize position : current.execution.environmentRecall.length = index at count ⊢
        interval_cases index <;> decide
      change entry.beforeView.application.1.publicView.clock + 5 <
        current.execution.application.current.native.clock at late
      omega
    exact original_early_submission_receipt seeds current trace owner entry member message emitted
      authored originalPacket zero original markerPast

end Vegas.Examples.CommitSeedBroadcast
