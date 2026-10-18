/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastProtected
import Vegas.Examples.CommitSeedBroadcastFirstLateProvenance
import Vegas.Pending.PhaseAttemptCheckpoint
import Interaction.ReactiveTrafficIdentity
import Interaction.ReactiveReceiptIdentity

/-! # The complete middle ledger identifies the original public packet word -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private theorem early_include_packet (owner : Player) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) (identifier : MessageId Player)
    (included : earlyCommand owner past view = .include identifier) :
    ∃ snapshot, past[3]? = some snapshot ∧
      ∃ message ∈ snapshot.beforeView.network.inputs, message.id = identifier := by
  unfold earlyCommand at included
  cases selected : past[3]? with
  | none => rw [selected] at included; cases included
  | some snapshot =>
      rw [selected] at included
      change (match snapshot.beforeView.network.inputs.find?
          (fun message : Message Player (CommitAttemptPacket graph) =>
            decide (message.sender = owner ∧ message.payload.attempt = originalAttempt)) with
        | none => ReactiveApplication.Command.wait
        | some message => pendingCommand message.id view) = .include identifier at included
      cases found : snapshot.beforeView.network.inputs.find?
          (fun message : Message Player (CommitAttemptPacket graph) =>
            decide (message.sender = owner ∧ message.payload.attempt = originalAttempt)) with
      | none => rw [found] at included; cases included
      | some message =>
          rw [found] at included
          change pendingCommand message.id view = .include identifier at included
          cases pending : view.network.pending.any (fun packet => packet.id = message.id) with
          | false =>
              simp only [pendingCommand, pending, Bool.false_eq_true, ite_false] at included
              cases included
          | true =>
              simp only [pendingCommand, pending, ite_true] at included
              exact ⟨snapshot, rfl, message, List.mem_of_find?_eq_some found,
                ReactiveApplication.Command.include.inj included⟩

private theorem activateReady_not_include (owner : Player) (event : graph.EventId)
    (view : app.EnvironmentView) (identifier : MessageId Player) :
    activateReady owner event view ≠ .include identifier := by
  unfold activateReady
  split <;> intro impossible <;> cases impossible

private theorem pollCommand_not_include (owner : Player) (good wanted : Bool)
    (view : app.EnvironmentView) (identifier : MessageId Player) :
    pollCommand owner good wanted view ≠ .include identifier := by
  unfold pollCommand
  split
  · exact activateReady_not_include owner (bindingEvent owner) view identifier
  · intro impossible; cases impossible

private theorem original_include_before_late (seed : Seeds) (position : Nat)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (identifier : MessageId Player) (beforeLate : position < 14)
    (included : originalCommand seed position past view = .include identifier) :
    8 ≤ position ∧ ∃ snapshot, past[3]? = some snapshot ∧
      ∃ message ∈ snapshot.beforeView.network.inputs, message.id = identifier := by
  interval_cases position
  · exact (activateReady_not_include alice (bindingEvent alice) view identifier included).elim
  · exact (activateReady_not_include bob (bindingEvent bob) view identifier included).elim
  · exact (activateReady_not_include carol (bindingEvent carol) view identifier included).elim
  · cases included
  · cases included
  · exact (pollCommand_not_include _ _ _ view identifier included).elim
  · exact (pollCommand_not_include _ _ _ view identifier included).elim
  · exact (pollCommand_not_include _ _ _ view identifier included).elim
  · exact ⟨by omega, early_include_packet _ past view identifier included⟩
  · exact ⟨by omega, early_include_packet _ past view identifier included⟩
  · exact ⟨by omega, early_include_packet _ past view identifier included⟩
  · exact (pollCommand_not_include _ _ _ view identifier included).elim
  · exact (pollCommand_not_include _ _ _ view identifier included).elim
  · exact (pollCommand_not_include _ _ _ view identifier included).elim

private def EarlyLedgerAccounted : app.ProtocolState → Prop
  | none => True
  | some current =>
      current.execution.application.attempt = originalAttempt →
      current.execution.environmentRecall.length ≤ 14 →
      ∀ message ∈ current.execution.network.ledger,
        8 < current.execution.environmentRecall.length ∧
        ∃ snapshot, current.execution.environmentRecall[3]? = some snapshot ∧
          message ∈ snapshot.beforeView.network.inputs

private theorem early_ledger_history (seed : Seeds) :
    ∀ {state} (_trace : (app.protocol initial horizon (family seed)).Trace state),
      EarlyLedgerAccounted state := by
  intro state trace
  induction trace with
  | start => trivial
  | @extend source target prior joint legal reached ih =>
      change target ∈ (app.transition initial horizon (family seed) source joint).support
        at reached
      cases source with
      | none =>
          obtain ⟨state, _supported, rfl⟩ := PMF.support_map .. ▸ reached
          intro _original _bounded message member
          exact (List.not_mem_nil member).elim
      | some current =>
          rcases current with ⟨remaining, active, execution⟩
          cases active with
          | some actor =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              generalize actionEq : (joint actor).getD (⟨none⟩ : app.Action) = action
              intro original bounded message member
              have attemptEq : (execution.respond app actor action).application.attempt =
                  execution.application.attempt := by
                rcases action with ⟨transmission⟩
                cases transmission <;> rfl
              have ledgerEq : (execution.respond app actor action).network.ledger =
                  execution.network.ledger := by
                rcases action with ⟨transmission⟩
                cases transmission <;> rfl
              rw [ledgerEq] at member
              have oldOriginal : execution.application.attempt = originalAttempt :=
                attemptEq.symm.trans original
              rw [app.respond_environmentRecall] at bounded ⊢
              exact ih oldOriginal bounded message member
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, selected, moved⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  intro original bounded message member
                  change next.application.attempt = originalAttempt at original
                  change next.environmentRecall.length ≤ 14 at bounded
                  have entries := app.environmentStep_environmentRecall execution next command
                    supported
                  have geometry := raw_phase_geometry (family seed)
                    ⟨remaining + 1, none, execution⟩ prior
                  have namespaceBound :=
                    (phaseApplication_namespace_progress runtime leaks).environmentStep
                      execution next command supported geometry.1.adjacent
                  have oldOriginal : execution.application.attempt = originalAttempt := by
                    rw [original] at namespaceBound
                    generalize address : execution.application.attempt = identifier
                      at namespaceBound ⊢
                    rcases identifier with ⟨phase, generation⟩
                    change generation ≤ 0 ∧ phase ≤ 0 at namespaceBound
                    have phaseEq : phase = 0 := by omega
                    have generationEq : generation = 0 := by omega
                    subst phase
                    subst generation
                    rfl
                  have beforeLate : execution.environmentRecall.length < 14 := by
                    rw [entries, List.length_append, List.length_singleton] at bounded
                    omega
                  have retainSnapshot (snapshot : app.EnvironmentEntry)
                      (selected : execution.environmentRecall[3]? = some snapshot) :
                      next.environmentRecall[3]? = some snapshot := by
                    have inside : 3 < execution.environmentRecall.length := by
                      by_contra outside
                      rw [List.getElem?_eq_none (by omega)] at selected
                      cases selected
                    rw [entries, List.getElem?_append_left inside]
                    exact selected
                  have retainOld (old : message ∈ execution.network.ledger) :
                      8 < next.environmentRecall.length ∧
                      ∃ snapshot, next.environmentRecall[3]? = some snapshot ∧
                        message ∈ snapshot.beforeView.network.inputs := by
                    obtain ⟨passed, snapshot, found, input⟩ :=
                      ih oldOriginal (Nat.le_of_lt beforeLate) message old
                    change 8 < execution.environmentRecall.length at passed
                    refine ⟨?_, snapshot, retainSnapshot snapshot found, input⟩
                    rw [entries, List.length_append, List.length_singleton]
                    omega
                  cases command with
                  | «include» identifier =>
                      have chosen : originalCommand seed execution.environmentRecall.length
                          execution.environmentRecall (execution.observeEnvironment app) =
                            .include identifier :=
                        (((PMF.mem_support_pure_iff _ _).mp selected).trans
                          (choose_original seed _ _ oldOriginal)).symm
                      obtain ⟨middle, snapshot, found, initialMessage, initialInput,
                        identifierEq⟩ :=
                        original_include_before_late seed execution.environmentRecall.length
                          execution.environmentRecall (execution.observeEnvironment app)
                            identifier beforeLate chosen
                      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
                        at supported
                      cases (PMF.mem_support_pure_iff _ _).mp supported
                      cases lookup : execution.network.lookup identifier with
                      | none =>
                          have unchanged :
                              (execution.includePending app identifier).network.ledger =
                              execution.network.ledger := by
                            simp only [ReactiveApplication.Execution.includePending,
                              MessageNetwork.includePending, lookup]
                          exact retainOld (unchanged ▸ member)
                      | some packet =>
                          have ledgerEq : (execution.includePending app identifier).network.ledger =
                              execution.network.ledger ++ [packet] := by
                            simp only [ReactiveApplication.Execution.includePending,
                              MessageNetwork.includePending, lookup]
                          rw [ledgerEq, List.mem_append, List.mem_singleton] at member
                          rcases member with old | equal
                          · exact retainOld old
                          · subst message
                            obtain ⟨entry, recorded, _material, _transmitted, emitted,
                              _attempt, _zero⟩ := snapshot_packet_original_clock_zero seed
                                (remaining + 1) execution prior snapshot found initialMessage.sender
                                  initialMessage initialInput rfl
                            have initialCurrent : initialMessage ∈ execution.network.inputs := by
                              have remembered := app.history_inputRecall initial horizon
                                (family seed) prior
                              have output : initialMessage ∈
                                  app.outputs (execution.recall initialMessage.sender) :=
                                List.mem_filterMap.mpr ⟨entry, recorded, emitted⟩
                              rw [← remembered initialMessage.sender] at output
                              exact (List.mem_filter.mp output).1
                            have packetPending : packet ∈ execution.network.pending :=
                              List.mem_of_find?_eq_some lookup
                            have packetCurrent : packet ∈ execution.network.inputs :=
                              (app.retained_envelopes_mem_inputs execution
                                (app.history_provenance initial horizon (family seed) prior)
                                (app.history_inputRecall initial horizon
                                  (family seed) prior)).pending
                                  packet packetPending
                            have lookupId := List.find?_some lookup
                            change decide (packet.id = identifier) = true at lookupId
                            have same := app.input_identifier_injective_history initial horizon
                              (family seed) ⟨remaining + 1, none, execution⟩ prior packet
                                initialMessage packetCurrent initialCurrent
                                  ((of_decide_eq_true lookupId).trans identifierEq.symm)
                            refine ⟨?_, snapshot, retainSnapshot snapshot found,
                              same.symm ▸ initialInput⟩
                            rw [entries, List.length_append, List.length_singleton]
                            omega
                  | wait =>
                      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
                        at supported
                      cases (PMF.mem_support_pure_iff _ _).mp supported
                      exact retainOld member
                  | activate actor =>
                      rw [completeActivation_law] at supported
                      cases (PMF.mem_support_pure_iff _ _).mp supported
                      exact retainOld member
                  | application operation =>
                      simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp]
                        at supported
                      obtain ⟨updated, _chosen, rfl⟩ := PMF.support_map .. ▸ supported
                      exact retainOld member

/-- Before any late inclusion, every ledger envelope is one of the immutable
initial packets. This statement permits arbitrary raw preparations and aliases. -/
theorem original_pre_late_ledger_subset (seed : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seed)).Trace (some current))
    (original : current.execution.application.attempt = originalAttempt)
    (beforeLate : current.execution.environmentRecall.length ≤ 14)
    (snapshot : app.EnvironmentEntry)
    (selected : current.execution.environmentRecall[3]? = some snapshot) :
    current.execution.network.ledger ⊆ snapshot.beforeView.network.inputs := by
  intro message member
  obtain ⟨_passed, actual, found, input⟩ :=
    early_ledger_history seed trace original beforeLate message member
  have equal := Option.some.inj (found.symm.trans selected)
  exact equal ▸ input

/-- A good first-late callback precedes every physical inclusion, independently
of all raw response contents. Its complete receipt word is therefore empty. -/
theorem original_good_firstLate_receipts_empty (seed : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seed)).Trace (some current))
    (owner : Player) (active : current.actor = some owner)
    (original : current.execution.application.attempt = originalAttempt)
    (clock : current.execution.application.current.native.clock = 2)
    (good : seed.2 owner = true) : current.execution.receipts = [] := by
  have placement :=
    original_first_late_input_placement seed current trace owner active original clock
  have beforeMiddle : current.execution.environmentRecall.length ≤ 8 := by
    rcases placement with early | late
    · exact early.2.1
    · rw [good] at late
      cases late.2.2
  have ledgerEmpty : current.execution.network.ledger = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro message member
    have passed := (early_ledger_history seed trace original
      (by omega : current.execution.environmentRecall.length ≤ 14) message member).1
    omega
  have identifiers := app.receipt_identifiers_history initial horizon (family seed) current trace
  rw [ledgerEmpty, List.map_nil] at identifiers
  exact List.map_eq_nil_iff.mp identifiers

private theorem snapshot_packet_readback_idle (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (app.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (snapshot : app.EnvironmentEntry) (selected : execution.environmentRecall[3]? = some snapshot)
    (message : Message Player (CommitAttemptPacket graph))
    (input : message ∈ snapshot.beforeView.network.inputs) :
    message ∈ execution.network.inputs ∧ message.payload.attempt = originalAttempt := by
  obtain ⟨entry, recalled, _material, _transmitted, emitted, original, _zero⟩ :=
    snapshot_packet_original_clock_zero seed remaining execution trace snapshot selected
      message.sender message input rfl
  have remembered := app.history_inputRecall initial horizon (family seed) trace
  have output : message ∈ app.outputs (execution.recall message.sender) :=
    List.mem_filterMap.mpr ⟨entry, recalled, emitted⟩
  rw [← remembered message.sender] at output
  refine ⟨(List.mem_filter.mp output).1, ?_⟩
  exact (phase_recalled_emission_attempt runtime leaks initial horizon (family seed) trace
    message.sender entry recalled message emitted).trans original

private theorem snapshot_packet_readback (seed : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seed)).Trace (some current))
    (snapshot : app.EnvironmentEntry)
    (selected : current.execution.environmentRecall[3]? = some snapshot)
    (message : Message Player (CommitAttemptPacket graph))
    (input : message ∈ snapshot.beforeView.network.inputs) :
    message ∈ current.execution.network.inputs ∧ message.payload.attempt = originalAttempt := by
  rcases current with ⟨remaining, actor, execution⟩
  cases actor with
  | none =>
      exact snapshot_packet_readback_idle seed remaining execution trace
        snapshot selected message input
  | some owner =>
      obtain ⟨responded⟩ := app.raw_trace_respond initial horizon (family seed) remaining
        execution owner ⟨none⟩ trace
      have found : (execution.respond app owner ⟨none⟩).environmentRecall[3]? = some snapshot := by
        simpa only [app.respond_environmentRecall] using selected
      exact snapshot_packet_readback_idle seed remaining (execution.respond app owner ⟨none⟩)
        responded snapshot found message input

/-- At a bad first-late callback the complete middle ledger contains exactly
the original public packets. Either accepting or rejecting receipts count here. -/
theorem original_middle_ledger_membership (seed : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seed)).Trace (some current))
    (original : current.execution.application.attempt = originalAttempt)
    (middlePassed : 11 ≤ current.execution.environmentRecall.length)
    (beforeLate : current.execution.environmentRecall.length ≤ 14)
    (snapshot : app.EnvironmentEntry)
    (selected : current.execution.environmentRecall[3]? = some snapshot)
    (message : Message Player (CommitAttemptPacket graph)) :
    message ∈ current.execution.network.ledger ↔ message ∈ snapshot.beforeView.network.inputs := by
  constructor
  · intro member
    exact original_pre_late_ledger_subset seed current trace original beforeLate snapshot selected
      member
  · intro input
    obtain ⟨currentInput, addressed⟩ :=
      snapshot_packet_readback seed current trace snapshot selected message input
    obtain ⟨accepted, received⟩ := original_snapshot_submission_receipt seed current trace
      original middlePassed snapshot selected message.sender message input rfl addressed
    have identifiers := app.receipt_identifiers_history initial horizon (family seed) current trace
    have publishedId : message.id ∈ current.execution.network.ledger.map Message.id := by
      rw [← identifiers]
      exact List.mem_map.mpr ⟨(message.id, accepted), received, rfl⟩
    obtain ⟨published, publishedMember, sameId⟩ := List.mem_map.mp publishedId
    have same := app.input_envelope_eq_ledger_of_id_eq initial horizon (family seed) current trace
      message published currentInput publishedMember sameId.symm
    rw [same]
    exact publishedMember

open Classical in
/-- This finite packet set is observable from the full bad-clock-two view.
The fixed initial owner order reconstructs the public initial envelope word. -/
theorem bad_firstLate_ledger_packets (seed : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seed)).Trace (some current))
    (owner : Player) (active : current.actor = some owner)
    (original : current.execution.application.attempt = originalAttempt)
    (clock : current.execution.application.current.native.clock = 2)
    (bad : seed.2 owner = false) (snapshot : app.EnvironmentEntry)
    (selected : current.execution.environmentRecall[3]? = some snapshot) :
    current.execution.network.ledger.toFinset = snapshot.beforeView.network.inputs.toFinset := by
  classical
  have placement :=
    original_first_late_input_placement seed current trace owner active original clock
  have bounds : 12 ≤ current.execution.environmentRecall.length ∧
      current.execution.environmentRecall.length ≤ 14 := by
    rcases placement with early | late
    · rw [bad] at early
      cases early.2.2
    · exact ⟨late.1, late.2.1⟩
  apply Finset.ext
  intro message
  simpa only [List.mem_toFinset] using original_middle_ledger_membership seed current trace
    original (by omega) bounds.2 snapshot selected message

end Vegas.Examples.CommitSeedBroadcast
