/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalObservation
import Vegas.Pending.PhaseCountUniqueness
import Vegas.Pending.PhaseCountMenu
import Vegas.Pending.ReactiveCountedSurvivor

/-! # Unique proposals on counted physical histories

Count permission fixes the event owner and allows only its first signed packet
at a physical address. The actual raw identifier invariant then gives one
complete opening envelope, hence one proposal, at each address. Receipt and
application acceptance play no role.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
theorem event_of_packetProposal (packet : CommitAttemptPacket graph)
    (coordinate : CommitAttemptEvent graph) (raw : Raw L)
    (proposed : packetProposal? packet = some (coordinate, raw)) :
    PhaseCount.event? packet = some coordinate := by
  obtain ⟨attempt, candidate, call⟩ := opening_of_packetProposal packet coordinate raw proposed
  simp only [PhaseCount.event?, call, Payload.event?, Option.map_some]
  rw [attempt]

/-- Authentic counted traffic cannot contain two different opening envelopes
at the same physical source address. -/
theorem opening_envelope_unique
    (traffic : List (Message Player (CommitAttemptPacket graph)))
    (first second : Message Player (CommitAttemptPacket graph))
    (firstAllowed : PhaseCount.Permits traffic first)
    (secondAllowed : PhaseCount.Permits traffic second)
    (firstInput : first ∈ traffic) (secondInput : second ∈ traffic)
    (identified : ∀ left ∈ traffic, ∀ right ∈ traffic, left.id = right.id → left = right)
    (coordinate : CommitAttemptEvent graph) (firstValue secondValue : Raw L)
    (firstProposal : packetProposal? first.payload = some (coordinate, firstValue))
    (secondProposal : packetProposal? second.payload = some (coordinate, secondValue)) :
    first = second := by
  obtain ⟨_, firstCandidate, firstCall⟩ :=
    opening_of_packetProposal first.payload coordinate firstValue firstProposal
  obtain ⟨_, secondCandidate, secondCall⟩ :=
    opening_of_packetProposal second.payload coordinate secondValue secondProposal
  have firstOwner := countCallCorrect_owned_event
    (EarlierOwnPacket (traffic.map PhaseCount.nativeMessage) (PhaseCount.nativeMessage first))
    (PhaseCount.nativeMessage first) firstAllowed.2.1 (by
      change first.payload.packet.call.event? graph = some coordinate.event
      rw [firstCall]; rfl)
  have secondOwner := countCallCorrect_owned_event
    (EarlierOwnPacket (traffic.map PhaseCount.nativeMessage) (PhaseCount.nativeMessage second))
    (PhaseCount.nativeMessage second) secondAllowed.2.1 (by
      change second.payload.packet.call.event? graph = some coordinate.event
      rw [secondCall]; rfl)
  exact PhaseCount.Permits.eq_of_same_event firstAllowed secondAllowed firstInput secondInput
    identified (Option.some.inj (firstOwner.symm.trans secondOwner))
    ((event_of_packetProposal first.payload coordinate firstValue firstProposal).trans
      (event_of_packetProposal second.payload coordinate secondValue secondProposal).symm)

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- On an actual counted history the submitted archive is a partial function
from physical coordinates to typed wire values. -/
theorem archive_coordinate_unique [Fintype Player] (bounds : MessageBounds graph)
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler)
    (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      initial horizon scheduler).Trace (some control))
    (coordinate : CommitAttemptEvent graph) (firstValue secondValue : Raw L)
    (first : (coordinate, firstValue) ∈ archive control.execution.network.inputs)
    (second : (coordinate, secondValue) ∈ archive control.execution.network.inputs) :
    firstValue = secondValue := by
  obtain ⟨firstMessage, firstInput, firstProposal⟩ := (mem_archive _ _).mp first
  obtain ⟨secondMessage, secondInput, secondProposal⟩ := (mem_archive _ _).mp second
  have rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    initial horizon scheduler trace
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
  have same := opening_envelope_unique control.execution.network.inputs firstMessage secondMessage
    ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 firstMessage firstInput))
    ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 secondMessage secondInput))
    firstInput secondInput (fun left leftInput right rightInput identified =>
      (app).input_identifier_injective_history initial horizon scheduler control rawTrace
        left right leftInput rightInput identified)
    coordinate firstValue secondValue firstProposal secondProposal
  rw [same, secondProposal] at firstProposal
  exact congrArg Prod.snd (Option.some.inj firstProposal.symm)

/-- The locally reconstructed archive has the same uniqueness on counted inputs. -/
theorem observedArchive_coordinate_unique [Fintype Player] (bounds : MessageBounds graph)
    (complete : leaks = MessageNetwork.completePendingObservation)
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler)
    (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      initial horizon scheduler).Trace (some control))
    (who : Player) (active : control.actor = some who)
    (coordinate : CommitAttemptEvent graph) (firstValue secondValue : Raw L)
    (first : (coordinate, firstValue) ∈ observedArchive runtime leaks
      (control.execution.recall who) (control.execution.observe (app) who))
    (second : (coordinate, secondValue) ∈ observedArchive runtime leaks
      (control.execution.recall who) (control.execution.observe (app) who)) :
    firstValue = secondValue := by
  have reconstructed := observedArchive_eq_submitted runtime leaks complete initial horizon
    scheduler control ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
      initial horizon scheduler trace) who active
  rw [reconstructed] at first second
  exact archive_coordinate_unique runtime leaks bounds initial horizon scheduler control trace
    coordinate firstValue secondValue first second

end Vegas.EventGraphRuntime.PhaseProposal
