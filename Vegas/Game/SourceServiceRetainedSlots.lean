/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceConformantResponse

/-! # Canonical slots on every retained service history

Every first retained commitment uses its owner's counted prepared slot. The
count advances whenever a binding completes, including expiry without a
commitment. Used slots therefore remain below the count, except the count slot
while the owner's submitted binding is unfinished. No density assumption is
made about slots skipped after a miss.

These invariants apply to every legal canonical-menu history under an
arbitrary scheduler. They require neither a prescribed source profile nor
protected inclusion, and do not assert that retained histories avoid misses
or terminal audit charges.
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}
  (bounds : MessageBounds (serviceGraph setup mode))

/-- A retained response keeps every used prepared slot below the public
count, except the count slot of a submitted unfinished binding. -/
theorem retainedCanonicalSlots_respond {horizon remaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {middle : (serviceApplication setup mode deadline leaks).Execution} {who : Player}
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some ⟨remaining, some who, middle⟩))
    {response : (serviceApplication setup mode deadline leaks).Action}
    (member : response ∈ bounds.clearActions (serviceRuntime setup mode deadline) leaks who
      (middle.recall who) (middle.observe (serviceApplication setup mode deadline leaks) who))
    (atTurn : OwnSubmissionsAtTurn setup leaks middle who)
    (valid : CanonicalSlotsUsed setup leaks middle who) :
    CanonicalSlotsUsed setup leaks
        (middle.respond (serviceApplication setup mode deadline leaks) who response)
      who := by
  let app := serviceApplication setup mode deadline leaks
  have appEq := (serviceRuntime setup mode deadline).reactive_respond_application leaks middle
      who response
  obtain ⟨emitted, recalled, _⟩ := respond_recall_self setup leaks middle who response
  have recordedMono : ∀ event,
      (serviceRuntime setup mode deadline).eventRecorded leaks (middle.recall who) event = true →
        (serviceRuntime setup mode deadline).eventRecorded leaks
        ((middle.respond app who response).recall who)
          event = true := by
    intro event recorded
    rw [recalled]
    unfold EventGraphRuntime.eventRecorded at recorded ⊢
    rw [List.any_append, recorded, Bool.true_or]
  intro serial used
  rw [(serviceRuntime setup mode deadline).submittedCandidateSlots_respond leaks middle who
          response] at used
  rw [appEq.2]
  rcases List.mem_append.mp used with old | new
  · rcases valid serial old with lower | ⟨equal, other, payload, layout, unfinished, recorded⟩
    · exact Or.inl lower
    · refine Or.inr ⟨equal, other, payload, layout, ?_, recordedMono other recorded⟩
      rw [appEq.1]
      exact unfinished
  · have slot : (serviceRuntime setup mode deadline).responseCandidateSlot leaks response = some
        serial := Option.mem_toList.mp new
    obtain ⟨material, submits⟩ : ∃ material, response.transmission = some material := by
      unfold EventGraphRuntime.responseCandidateSlot at slot
      split at slot
      · exact ⟨_, ‹_›⟩
      · cases slot
    rcases bounds.clearActions_cases (serviceRuntime setup mode deadline) leaks who _ _ response
        member with member | ⟨_, conformant⟩
    swap
    · obtain ⟨event, submitted, _, _, ready, _, slots⟩ :=
        conformantResponse_turn trace who response conformant
      obtain ⟨equal, payload, layout⟩ := slots serial slot
      refine Or.inr ⟨equal, event, payload, layout, ?_, ?_⟩
      · rw [appEq.1]
        exact ready.1
      · rw [recalled]
        unfold EventGraphRuntime.eventRecorded
        rw [List.any_append]
        simp only [List.any_cons, List.any_nil, Bool.or_false]
        rw [submitted]
        simp
    obtain ⟨event, action, turn, owned, _, _, unrecorded, _, rfl⟩ :=
      bounds.canonicalActions_submission (serviceRuntime setup mode deadline) leaks who _ _ response
          member material submits
    have fresh := canonicalSlot_fresh_of_used trace who atTurn valid event turn unrecorded
    have canonical := canonicalFreshSlot_canonical who (middle.observe app who).application fresh
    obtain ⟨selected, ⟨payload, layout⟩, named⟩ := canonicalServiceDecision_candidateSlot who
      (middle.recall who) (middle.observe app who) event owned action serial slot
    rw [canonical] at selected
    cases Option.some.inj selected
    have ready := (middle.application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ who event turn).1
    refine Or.inr ⟨rfl, event, payload, layout, ?_, ?_⟩
    · rw [appEq.1]
      exact ready.1
    · rw [recalled]
      unfold EventGraphRuntime.eventRecorded
      rw [List.any_append]
      simp only [List.any_cons, List.any_nil, Bool.or_false]
      rw [named]
      simp

/-- Recording a retained response preserves the fact that each submission was
made at its owner's own ready turn. -/
theorem retainedOwnSubmissionsAtTurn_respond
    (middle : (serviceApplication setup mode deadline leaks).Execution) (who : Player)
    (response : (serviceApplication setup mode deadline leaks).Action)
    (member : response ∈ bounds.clearActions (serviceRuntime setup mode deadline) leaks who
      (middle.recall who) (middle.observe (serviceApplication setup mode deadline leaks) who))
    (atTurn : OwnSubmissionsAtTurn setup leaks middle who) :
    OwnSubmissionsAtTurn setup leaks
      (middle.respond (serviceApplication setup mode deadline leaks) who response) who := by
  obtain ⟨_, recalled, _⟩ := respond_recall_self setup leaks middle who response
  intro entry present event submitted
  rw [recalled] at present
  rcases List.mem_append.mp present with old | new
  · exact atTurn entry old event submitted
  · rw [List.mem_singleton] at new
    subst new
    rcases bounds.clearActions_cases (serviceRuntime setup mode deadline) leaks who _ _ response
        member with member | ⟨_, conformant⟩
    · exact (bounds.canonical_submitted_event (serviceRuntime setup mode deadline) leaks who _ _
            response member event submitted).1
    · obtain ⟨material, sent, _, fresh⟩ := conformant
      obtain ⟨named, addressed, ready, owned⟩ :=
        (serviceRuntime setup mode deadline).freshServiceEnvelope_owned _ _ fresh
      change material.call.packet.event? (serviceGraph setup mode) = some named at addressed
      have same : named = event := by
        simp only [EventGraphRuntime.submittedEvent?, sent, addressed,
          Option.some.injEq] at submitted
        exact submitted
      subst named
      change (serviceGraph setup mode).actor? event = some who at owned
      exact serviceOwnTurn?_of_ready setup middle.application
        ((middle.application.publicView_eventReady event).mp ready) owned

omit [Fintype Player] in
/-- **The counted slot supplies an unrecorded own decision.** On every legal
history where the owner's submissions were made at its own turns and its used
prepared slots stay canonical, the counted slot at an unrecorded own turn is
fresh, below the candidate count, and selected by the canonical decision. -/
theorem canonicalSlot_resources_of_used {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (capacity : (serviceGraph setup mode).order.eventCount ≤ bounds.candidateCount)
    {control : (serviceApplication setup mode deadline leaks).Control}
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some control))
    (who : Player) (atTurn : OwnSubmissionsAtTurn setup leaks control.execution who)
    (valid : CanonicalSlotsUsed setup leaks control.execution who)
    (event : (serviceGraph setup mode).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (unrecorded : (serviceRuntime setup mode deadline).eventRecorded leaks
        (control.execution.recall who) event = false) :
    control.execution.application.publicView.bindingCount who < bounds.candidateCount ∧
      control.execution.application.candidates.lookup
        (who, .prepared (control.execution.application.publicView.bindingCount who)) = .fresh ∧
      canonicalFreshSlot who
        (control.execution.observe (serviceApplication setup mode deadline leaks) who).application =
          some (control.execution.application.publicView.bindingCount who) := by
  classical
  have fresh := canonicalSlot_fresh_of_used trace who atTurn valid event turn unrecorded
  refine ⟨?_, fresh, canonicalFreshSlot_canonical who _ fresh⟩
  let history := control.execution.application.config.history.map EventGraph.Completion.event
  have ready := (control.execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ who event turn).1
  have absent : event ∉ history := fun present => ready.1
    ((control.execution.application.config.history_exact event).mp present)
  have distinct : (event :: history).Nodup :=
    List.nodup_cons.mpr ⟨absent, control.execution.application.config.history_nodup⟩
  have lengthBound := distinct.length_le_card
  change history.countP _ < bounds.candidateCount
  apply lt_of_le_of_lt List.countP_le_length
  simp only [List.length_cons, Fintype.card_fin] at lengthBound
  omega

end Vegas
