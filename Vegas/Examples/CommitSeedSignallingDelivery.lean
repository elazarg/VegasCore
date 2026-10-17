/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingPrivacy

/-! # Actual accepting original packets and their selected emission clocks -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

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

theorem original_include_cases (seeds : Seeds) (position : Nat)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (identifier : MessageId Player)
    (selected : originalCommand seeds position past view = .include identifier) :
    (∃ source, ((source = bob ∧ position = 5) ∨ (source = alice ∧ position = 13)) ∧
      earlyCommand source past view = .include identifier) ∨
    (∃ source clock,
      ((source = alice ∧ (position = 7 ∨ position = 10)) ∨
        (source = bob ∧ (position = 15 ∨ position = 18))) ∧
      lateCommand source (seeds.2 (originalAddress source)) clock past view =
        .include identifier) := by
  have positions : position = 5 ∨ position = 7 ∨ position = 10 ∨ position = 13 ∨
      position = 15 ∨ position = 18 := by
    by_cases ended : 22 ≤ position
    · rw [originalCommand_bound seeds position past view ended] at selected
      cases selected
    · interval_cases position <;> simp_all [originalCommand, activateReady, pollCommand]
      all_goals
        repeat' split at selected
      all_goals cases selected
  rcases positions with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨bob, Or.inl ⟨rfl, rfl⟩, selected⟩
  · exact Or.inr ⟨alice, 2, Or.inl ⟨rfl, Or.inl rfl⟩, selected⟩
  · exact Or.inr ⟨alice, 3, Or.inl ⟨rfl, Or.inr rfl⟩, selected⟩
  · exact Or.inl ⟨alice, Or.inr ⟨rfl, rfl⟩, selected⟩
  · exact Or.inr ⟨bob, 4, Or.inr ⟨rfl, Or.inl rfl⟩, selected⟩
  · exact Or.inr ⟨bob, 5, Or.inr ⟨rfl, Or.inr rfl⟩, selected⟩

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
    (∃ entry message, execution.environmentRecall[2]? = some entry ∧
      message ∈ entry.beforeView.network.inputs ∧ message.sender = owner ∧
        message.payload.attempt = originalAttempt) ∨
    (∃ (prior : app.Execution) (used : Nat)
      (message : Message Player (CommitAttemptPacket graph)),
      Nonempty ((app.protocol initial horizon (family seeds)).Trace
        (some ⟨horizon - used, none, prior⟩)) ∧
      prior.environmentRecall.length = used ∧
      prior.application.attempt = originalAttempt ∧
      prior.environmentRecall <+: execution.environmentRecall ∧
      ((owner = alice ∧ (used = 7 ∨ used = 10)) ∨
        (owner = bob ∧ (used = 15 ∨ used = 18))) ∧
      (lateClock owner (seeds.2 (originalAddress owner)), message) ∈
        (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
          execution.environmentRecall (execution.observeEnvironment app)).emissions) := by
  obtain ⟨prior, _native, used, priorTrace, count, original, envPrefix, _words, emittedPrefix,
    packet, _input, sender, _attempt, _event, _lookup, _handled, selected⟩ :=
      original_binding_accepted_boundary seeds remaining execution trace owner accepted
  rcases original_include_cases seeds used prior.environmentRecall
      (prior.observeEnvironment app) packet.id selected with early | late
  · obtain ⟨source, _position, chosen⟩ := early
    obtain ⟨entry, message, snapshot, input, authored, attempt, named⟩ :=
      earlyCommand_inclusion source prior.environmentRecall (prior.observeEnvironment app)
        packet.id chosen
    have sameOwner : source = owner := by
      have sameSender : message.sender = packet.sender := congrArg Prod.fst named
      exact authored.symm.trans (sameSender.trans sender)
    have authoredOwner : message.sender = owner := authored.trans sameOwner
    have snapshotBound : 2 < prior.environmentRecall.length :=
      (List.getElem?_eq_some_iff.mp snapshot).1
    obtain ⟨later, appended⟩ := envPrefix
    have finalSnapshot : execution.environmentRecall[2]? = some entry := by
      rw [← appended, List.getElem?_append_left snapshotBound]
      exact snapshot
    exact Or.inl ⟨entry, message, finalSnapshot, input, authoredOwner, attempt⟩
  · obtain ⟨source, clock, position, chosen⟩ := late
    obtain ⟨eligible, message, emitted, named⟩ := lateCommand_inclusion source
      (seeds.2 (originalAddress source)) clock prior.environmentRecall
        (prior.observeEnvironment app) packet.id chosen
    have authored := localInput_sender (originalCoordinate source) source
      prior.environmentRecall (prior.observeEnvironment app) clock message emitted
    have sameOwner : source = owner := by
      have sameSender : message.sender = packet.sender := congrArg Prod.fst named
      exact authored.symm.trans (sameSender.trans sender)
    rw [sameOwner] at emitted eligible position
    have finalEmission := (emittedPrefix (originalCoordinate owner) owner).sublist.subset emitted
    rw [← eligible] at finalEmission
    exact Or.inr ⟨prior, used, message, priorTrace, count, original, envPrefix, position,
      finalEmission⟩

/-- If the actual early snapshot contains no own packet, every accepting
original binding is caused by an emission at that owner's eligible late clock.
The snapshot condition refers to the real initialized history. -/
theorem original_binding_accepted_late_of_empty_snapshot (seeds : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (rawMenu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player)
    (empty : ∀ entry, execution.environmentRecall[2]? = some entry →
      ∀ message ∈ entry.beforeView.network.inputs, message.sender ≠ owner)
    (accepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate owner)
      owner execution) :
    ∃ message, (lateClock owner (seeds.2 (originalAddress owner)), message) ∈
      (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
        execution.environmentRecall (execution.observeEnvironment app)).emissions := by
  rcases original_binding_accepted_emission seeds remaining execution trace owner accepted with
    early | late
  · obtain ⟨entry, message, snapshot, input, sender, _attempt⟩ := early
    exact (empty entry snapshot message input sender).elim
  · obtain ⟨_prior, _used, message, _trace, _count, _attempt, _prefix, _position, emitted⟩ := late
    exact ⟨message, emitted⟩

end Vegas.Examples.CommitSeedSignalling
