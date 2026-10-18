/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseApplication
import Interaction.ReactiveTrafficState

/-! # Submitted opening proposals at physical source addresses

The proposal readout ignores delivery, application acceptance, certificate
aliases and packet identifiers. It keeps the physical attempt, source event and
typed wire value of every submitted opening. Arbitrary raw traffic can contain
conflicting proposals, so this readout is a finite set rather than a partial
function. Uniqueness is a separate property of counted histories.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- The semantic payload of an opening, without sender aliases or receipt data. -/
abbrev Proposal (graph : Vegas.EventGraph Player L) := CommitAttemptEvent graph × Raw L

/-- Decode the public opening claim before deciding whether it is accepted. -/
def packetProposal? (packet : CommitAttemptPacket graph) : Option (Proposal graph) :=
  match packet.packet.call with
  | .opening event _candidate raw => some (⟨packet.attempt, event⟩, raw)
  | .commitment .. | .malformed .. => none

omit [DecidableEq Player] in
@[simp] theorem packetProposal?_opening (attempt : CommitAttemptId)
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (evidence : Option (OpeningFact graph)) (token : Option (ReadinessToken graph)) :
    packetProposal? (⟨attempt, ⟨.opening event candidate raw, evidence, token⟩⟩ :
      CommitAttemptPacket graph) = some (⟨attempt, event⟩, raw) := rfl

omit [DecidableEq Player] in
@[simp] theorem packetProposal?_commitment (attempt : CommitAttemptId)
    (event : graph.EventId) (candidate : Handle graph)
    (evidence : Option (OpeningFact graph)) (token : Option (ReadinessToken graph)) :
    packetProposal? (⟨attempt, ⟨.commitment event candidate, evidence, token⟩⟩ :
      CommitAttemptPacket graph) = none := rfl

omit [DecidableEq Player] in
theorem opening_of_packetProposal (packet : CommitAttemptPacket graph)
    (coordinate : CommitAttemptEvent graph) (raw : Raw L)
    (proposed : packetProposal? packet = some (coordinate, raw)) :
    packet.attempt = coordinate.attempt ∧
      ∃ candidate, packet.packet.call = .opening coordinate.event candidate raw := by
  cases call : packet.packet.call with
  | commitment event candidate =>
      simp only [packetProposal?, call] at proposed
      cases proposed
  | malformed value =>
      simp only [packetProposal?, call] at proposed
      cases proposed
  | opening event candidate value =>
      have equal : (⟨packet.attempt, event⟩, value) = (coordinate, raw) :=
        Option.some.inj (by simpa only [packetProposal?, call] using proposed)
      have address := congrArg Prod.fst equal
      have valueEq : value = raw := congrArg Prod.snd equal
      have eventEq : event = coordinate.event := congrArg CommitAttemptEvent.event address
      refine ⟨congrArg CommitAttemptEvent.attempt address, candidate, ?_⟩
      rw [eventEq, valueEq]

/-- All submitted opening claims, independent of their order and multiplicity. -/
def archive (messages : List (Message Player (CommitAttemptPacket graph))) :
    Finset (Proposal graph) :=
  (messages.filterMap fun message => packetProposal? message.payload).toFinset

theorem mem_archive (messages : List (Message Player (CommitAttemptPacket graph)))
    (proposal : Proposal graph) :
    proposal ∈ archive messages ↔
      ∃ message ∈ messages, packetProposal? message.payload = some proposal := by
  simp only [archive, List.mem_toFinset, List.mem_filterMap]

@[simp] theorem archive_nil : archive ([] : List (Message Player (CommitAttemptPacket graph))) =
    ∅ := rfl

@[simp] theorem archive_append (first second : List (Message Player (CommitAttemptPacket graph))) :
    archive (first ++ second) = archive first ∪ archive second := by
  simp only [archive, List.filterMap_append, List.toFinset_append]

/-- Equality of submitted envelope sets suffices; list order is irrelevant. -/
theorem archive_congr (first second : List (Message Player (CommitAttemptPacket graph)))
    (same : ∀ message, message ∈ first ↔ message ∈ second) :
    archive first = archive second := by
  ext proposal
  simp only [mem_archive]
  exact exists_congr fun message => and_congr (same message) Iff.rfl

theorem archive_mono {first second : List (Message Player (CommitAttemptPacket graph))}
    (included : first ⊆ second) : archive first ⊆ archive second := by
  intro proposal member
  obtain ⟨message, present, proposed⟩ := (mem_archive first proposal).mp member
  exact (mem_archive second proposal).mpr ⟨message, included present, proposed⟩

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Scheduler commands do not remove submitted proposals, including on rejection,
expiry, phase retirement or rollback. -/
theorem archive_environmentStep (execution next : (app).Execution) (command : (app).Command)
    (reached : next ∈ (execution.environmentStep (app) command).support) :
    archive next.network.inputs = archive execution.network.inputs := by
  rw [(app).environmentStep_inputs execution next command reached]

end Vegas.EventGraphRuntime.PhaseProposal
