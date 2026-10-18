/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOriginalReceiptProvenance

/-! # Actual accepting original packets and their selected emission clocks -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

theorem localInput_sender (coordinate : CommitAttemptEvent graph) (owner : Player)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) (clock : Nat)
    (message : Message Player (CommitAttemptPacket graph))
    (member : (clock, message) ∈
      (PhaseSeedScheduler.localInput runtime leaks coordinate owner past view).emissions) :
    message.sender = owner := by
  unfold PhaseSeedScheduler.localInput at member
  obtain ⟨pair, _pairMember, member⟩ := List.mem_flatMap.mp member
  obtain ⟨packet, packetMember, pairEq⟩ := List.mem_map.mp member
  have same : packet = message := congrArg Prod.snd pairEq
  subst packet
  have own := (List.mem_filter.mp packetMember).2
  have metadata : message.sender = owner ∧ message.payload.attempt = coordinate.attempt ∧
      message.payload.packet.call.event? graph = some coordinate.event :=
    of_decide_eq_true own
  exact metadata.1

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
  · exact activateReady_not_include _ _ _ _
  · intro impossible
    cases impossible

theorem original_include_cases (seeds : Seeds) (position : Nat)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (identifier : MessageId Player)
    (selected : originalCommand seeds position past view = .include identifier) :
    (∃ source, earlyCommand source past view = .include identifier) ∨
      (∃ source clock, lateCommand source (seeds.2 source) clock past view =
        .include identifier) := by
  by_cases bounded : position < 30
  · interval_cases position
    · exact (activateReady_not_include alice _ _ _ selected).elim
    · exact (activateReady_not_include bob _ _ _ selected).elim
    · exact (activateReady_not_include carol _ _ _ selected).elim
    · change (.application .advanceClock : app.Command) = .include identifier at selected
      cases selected
    · change (.application .advanceClock : app.Command) = .include identifier at selected
      cases selected
    · exact (pollCommand_not_include (seeds.1 0) _ true _ _ selected).elim
    · exact (pollCommand_not_include (seeds.1 1) _ true _ _ selected).elim
    · exact (pollCommand_not_include (seeds.1 2) _ true _ _ selected).elim
    · exact Or.inl ⟨seeds.1 0, selected⟩
    · exact Or.inl ⟨seeds.1 1, selected⟩
    · exact Or.inl ⟨seeds.1 2, selected⟩
    · exact (pollCommand_not_include (seeds.1 0) _ false _ _ selected).elim
    · exact (pollCommand_not_include (seeds.1 1) _ false _ _ selected).elim
    · exact (pollCommand_not_include (seeds.1 2) _ false _ _ selected).elim
    · exact Or.inr ⟨seeds.1 0, 2, selected⟩
    · exact Or.inr ⟨seeds.1 1, 2, selected⟩
    · exact Or.inr ⟨seeds.1 2, 2, selected⟩
    · change (.application .advanceClock : app.Command) = .include identifier at selected
      cases selected
    · exact (activateReady_not_include (seeds.1 0) _ _ _ selected).elim
    · exact (activateReady_not_include (seeds.1 1) _ _ _ selected).elim
    · exact (activateReady_not_include (seeds.1 2) _ _ _ selected).elim
    · exact Or.inr ⟨seeds.1 0, 3, selected⟩
    · exact Or.inr ⟨seeds.1 1, 3, selected⟩
    · exact Or.inr ⟨seeds.1 2, 3, selected⟩
    · change (.application .advanceClock : app.Command) = .include identifier at selected
      cases selected
    · change (.application .advanceClock : app.Command) = .include identifier at selected
      cases selected
    · change (.application .advanceClock : app.Command) = .include identifier at selected
      cases selected
    · change (.application (.expire (bindingEvent alice)) : app.Command) =
          .include identifier at selected
      cases selected
    · change (.application (.expire (bindingEvent bob)) : app.Command) =
          .include identifier at selected
      cases selected
    · change (.application (.expire (bindingEvent carol)) : app.Command) =
          .include identifier at selected
      cases selected
  · have distant : originalCommand seeds position past view = .wait := by
      unfold originalCommand
      split <;> first | rfl | omega
    rw [distant] at selected
    cases selected

/-- An accepting original binding comes either from the actual early snapshot
or from its own seed-selected late emission. Both alternatives retain the
same complete physical continuation and its original scheduler seed. -/
theorem original_binding_accepted_emission (seeds : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (rawMenu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player)
    (accepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate owner)
      owner execution) :
    (∃ entry message, execution.environmentRecall[3]? = some entry ∧
      message ∈ entry.beforeView.network.inputs ∧ message.sender = owner ∧
        message.payload.attempt = originalAttempt) ∨
    (∃ (prior : app.Execution) (used : Nat)
      (message : Message Player (CommitAttemptPacket graph)),
      Nonempty ((app.protocol initial horizon (family seeds)).Trace
        (some ⟨horizon - used, none, prior⟩)) ∧
      prior.environmentRecall.length = used ∧
      prior.application.attempt = originalAttempt ∧
      prior.environmentRecall <+: execution.environmentRecall ∧
      (lateClock (seeds.2 owner), message) ∈
        (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
          execution.environmentRecall (execution.observeEnvironment app)).emissions) := by
  obtain ⟨prior, _native, used, priorTrace, count, original, envPrefix, _words, emittedPrefix,
    packet, _input, sender, _attempt, _event, _lookup, _handled, selected, _continuation⟩ :=
      original_binding_accepted_boundary rawMenu seeds remaining execution trace owner accepted
  rcases original_include_cases seeds used prior.environmentRecall
      (prior.observeEnvironment app) packet.id selected with early | late
  · obtain ⟨source, chosen⟩ := early
    obtain ⟨entry, message, snapshot, input, authored, attempt, named⟩ :=
      earlyCommand_inclusion source prior.environmentRecall (prior.observeEnvironment app)
        packet.id chosen
    have sameOwner : source = owner := by
      have sameSender : message.sender = packet.sender := congrArg Prod.fst named
      exact authored.symm.trans (sameSender.trans sender)
    have authoredOwner : message.sender = owner := authored.trans sameOwner
    have snapshotBound : 3 < prior.environmentRecall.length :=
      (List.getElem?_eq_some_iff.mp snapshot).1
    obtain ⟨later, appended⟩ := envPrefix
    have finalSnapshot : execution.environmentRecall[3]? = some entry := by
      rw [← appended, List.getElem?_append_left snapshotBound]
      exact snapshot
    exact Or.inl ⟨entry, message, finalSnapshot, input, authoredOwner, attempt⟩
  · obtain ⟨source, clock, chosen⟩ := late
    obtain ⟨eligible, message, emitted, named⟩ := lateCommand_inclusion source
      (seeds.2 source) clock prior.environmentRecall
        (prior.observeEnvironment app) packet.id chosen
    have authored := localInput_sender (originalCoordinate source) source
      prior.environmentRecall (prior.observeEnvironment app) clock message emitted
    have sameOwner : source = owner := by
      have sameSender : message.sender = packet.sender := congrArg Prod.fst named
      exact authored.symm.trans (sameSender.trans sender)
    rw [sameOwner] at emitted eligible
    have finalEmission := (emittedPrefix (originalCoordinate owner) owner).sublist.subset emitted
    rw [← eligible] at finalEmission
    exact Or.inr ⟨prior, used, message, priorTrace, count, original, envPrefix,
      finalEmission⟩

/-- If the actual early snapshot contains no own packet, every accepting
original binding is caused by an emission at that owner's eligible late clock.
The snapshot condition refers to the real initialized history. -/
theorem original_binding_accepted_late_of_empty_snapshot (seeds : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (rawMenu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player)
    (empty : ∀ entry, execution.environmentRecall[3]? = some entry →
      ∀ message ∈ entry.beforeView.network.inputs, message.sender ≠ owner)
    (accepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate owner)
      owner execution) :
    ∃ message, (lateClock (seeds.2 owner), message) ∈
      (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
        execution.environmentRecall (execution.observeEnvironment app)).emissions := by
  rcases original_binding_accepted_emission seeds remaining execution trace owner accepted with
    early | late
  · obtain ⟨entry, message, snapshot, input, sender, _attempt⟩ := early
    exact (empty entry snapshot message input sender).elim
  · obtain ⟨_prior, _used, message, _trace, _count, _attempt, _prefix, emitted⟩ := late
    exact ⟨message, emitted⟩

end Vegas.Examples.CommitSeedBroadcast
