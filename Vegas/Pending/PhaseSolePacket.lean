/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNativeProjection
import Vegas.Pending.ReactiveServiceConditions

/-! # The sole original owner identifier on actual clear counted histories -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseNativeProjection

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph)

local notation "P" => phaseApplication runtime leaks
local notation "N" => runtime.reactiveApplication (nativeLeaks leaks plan)

/-- Clear actual count-clean histories have one original owner identifier for
any static event. Physical freshness is still tested per attempt-event, and
exact address recovery supplies the no-retry specialization. -/
theorem output_identifiers_eq_of_clear (bounds : MessageBounds graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler) {current}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅) (owner : Player)
    (first second : Message Player (WitnessedPacket graph))
    (firstOwn : first ∈ (N).outputs ((execution runtime leaks plan current.execution).recall owner))
    (secondOwn : second ∈ (N).outputs
      ((execution runtime leaks plan current.execution).recall owner))
    (sameSender : first.sender = second.sender) (event : graph.EventId)
    (firstNamed : first.payload.call.event? graph = some event)
    (secondNamed : second.payload.call.event? graph = some event) : first.id = second.id := by
  change first ∈ (N).outputs ((current.execution.recall owner).map
    (playerEntry runtime leaks plan)) at firstOwn
  change second ∈ (N).outputs ((current.execution.recall owner).map
    (playerEntry runtime leaks plan)) at secondOwn
  rw [outputs runtime leaks plan] at firstOwn secondOwn
  obtain ⟨original, originalOwn, rfl⟩ := List.mem_map.mp firstOwn
  obtain ⟨other, otherOwn, rfl⟩ := List.mem_map.mp secondOwn
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history _
    horizon (fun state _supported => PhaseCount.countClean_initial runtime leaks state) trace
  rw [← clean.1.1 owner] at originalOwn otherOwn
  have originalInput := (List.mem_filter.mp originalOwn).1
  have otherInput := (List.mem_filter.mp otherOwn).1
  have originalFirst := ((PhaseCount.permits_eq_true_iff _ _).mp
    (clean.2 original originalInput)).2.2.1
  have otherFirst := ((PhaseCount.permits_eq_true_iff _ _).mp
    (clean.2 other otherInput)).2.2.1
  have originalStamp := PhaseCount.stamp_nativeMessage_of_clear runtime leaks plan bounds inputs
    horizon scheduler trace clear original originalInput
  have otherStamp := PhaseCount.stamp_nativeMessage_of_clear runtime leaks plan bounds inputs
    horizon scheduler trace clear other otherInput
  change original.payload.packet.call.event? graph = some event at firstNamed
  change other.payload.packet.call.event? graph = some event at secondNamed
  change original.sender = other.sender at sameSender
  change original.id = other.id
  have sameAttempt : original.payload.attempt = other.payload.attempt := by
    rw [← originalStamp, ← otherStamp]
    simp only [RuntimePhasePlan.stampPacket, firstNamed, secondNamed]
  have sameEvent : PhaseCount.event? original.payload = PhaseCount.event? other.payload := by
    simp only [PhaseCount.event?, firstNamed, secondNamed, Option.map_some, sameAttempt]
  by_contra different
  have differentSerial : original.id.2 ≠ other.id.2 := by
    intro same
    exact different (Prod.ext sameSender same)
  rcases lt_or_gt_of_ne differentSerial with before | after
  · exact otherFirst original ⟨originalInput, sameSender, before⟩ sameEvent
  · exact originalFirst other ⟨otherInput, sameSender.symm, after⟩ sameEvent.symm

/-- Every actual recalled native packet has the original sole-identifier
premise of protected inclusion. No prescribed policy is needed. -/
theorem recall_sole_of_clear (bounds : MessageBounds graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler) {current}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅) (owner : Player)
    (earlier later : List (N).PlayerEntry) (entry : (N).PlayerEntry)
    (message : Message Player (WitnessedPacket graph))
    (split : (execution runtime leaks plan current.execution).recall owner =
      earlier ++ entry :: later)
    (emitted : entry.emitted = some message) (event : graph.EventId)
    (named : message.payload.call.event? graph = some event) :
    ∀ other ∈ earlier ++ later, ¬ EmitsOtherFor runtime (nativeLeaks leaks plan) other event
      message.id := by
  intro other member another
  obtain ⟨otherMessage, otherEmitted, sender, otherNamed, different⟩ := another
  have firstMember : entry ∈ (execution runtime leaks plan current.execution).recall owner := by
    rw [split]
    exact List.mem_append_right _ List.mem_cons_self
  have otherMember : other ∈ (execution runtime leaks plan current.execution).recall owner := by
    rw [split]
    rcases List.mem_append.mp member with earlierMember | laterMember
    · exact List.mem_append_left _ earlierMember
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ laterMember)
  apply different
  exact output_identifiers_eq_of_clear runtime leaks plan bounds inputs horizon scheduler trace
    clear owner otherMessage message (List.mem_filterMap.mpr ⟨other, otherMember, otherEmitted⟩)
    (List.mem_filterMap.mpr ⟨entry, firstMember, emitted⟩) sender event otherNamed named

end Vegas.EventGraphRuntime.PhaseNativeProjection
