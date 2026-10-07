/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCanonicalSlots
import Vegas.Pending.ReactiveCanonicalMenu

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
    (member : response ∈ bounds.canonicalActions (serviceRuntime setup mode deadline) leaks who
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
    (member : response ∈ bounds.canonicalActions (serviceRuntime setup mode deadline) leaks who
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
    exact (bounds.canonical_submitted_event (serviceRuntime setup mode deadline) leaks who _ _
            response member event submitted).1

/-- One arbitrary scheduler round preserves the owner's canonical-slot and
submission-turn invariants whenever its response policy uses retained actions. -/
theorem retainedCanonicalSlots_round {horizon remaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {players : Player → (serviceApplication setup mode deadline leaks).Policy} {who : Player}
    (covered : ∀ past view response, response ∈ (players who past view).support →
      response ∈ bounds.canonicalActions (serviceRuntime setup mode deadline) leaks who past view)
    {execution next : (serviceApplication setup mode deadline leaks).Execution}
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some ⟨remaining + 1, none, execution⟩))
    (atTurn : OwnSubmissionsAtTurn setup leaks execution who)
    (valid : CanonicalSlotsUsed setup leaks execution who)
    (reached : next ∈
        ((serviceApplication setup mode deadline leaks).round scheduler players
        execution).support) :
    OwnSubmissionsAtTurn setup leaks next who ∧ CanonicalSlotsUsed setup leaks next who := by
  let app := serviceApplication setup mode deadline leaks
  obtain ⟨command, selected, middle, moved, cases⟩ := round_cases setup leaks reached
  have recallEq := app.environmentStep_recall execution middle command moved
  have atMiddle : OwnSubmissionsAtTurn setup leaks middle who := by
    unfold OwnSubmissionsAtTurn
    rw [recallEq]
    exact atTurn
  have validMiddle := canonicalSlotsUsed_environment moved who valid
  rcases cases with ⟨_, rfl⟩ | ⟨responder, active, response, chosen, rfl⟩
  · exact ⟨atMiddle, validMiddle⟩
  · obtain ⟨middleTrace⟩ := app.raw_trace_environment (serviceInitialLaw setup mode) horizon
        scheduler remaining execution middle command trace selected moved
    rw [active] at middleTrace
    by_cases same : responder = who
    · subst responder
      have member := covered _ _ response chosen
      exact ⟨retainedOwnSubmissionsAtTurn_respond bounds middle who response member atMiddle,
        retainedCanonicalSlots_respond bounds middleTrace member atMiddle validMiddle⟩
    · have different : who ≠ responder := fun equal => same equal.symm
      refine ⟨?_, canonicalSlotsUsed_respond_other middle different response validMiddle⟩
      unfold OwnSubmissionsAtTurn
      rw [app.respond_recall_other middle responder who different response]
      exact atMiddle

/-- Retained-policy rounds preserve the canonical-slot and submission-turn
invariants under every scheduler, allowing bindings to complete by expiry. -/
theorem retainedCanonicalSlots_roundsFrom
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy) (who : Player)
    (covered : ∀ past view response, response ∈ (players who past view).support → response ∈
        bounds.canonicalActions (serviceRuntime setup mode deadline) leaks who past view)
    (count : Nat) (execution : (serviceApplication setup mode deadline leaks).Execution)
    (reached : execution ∈
        ((serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
        scheduler players count).support) : OwnSubmissionsAtTurn setup leaks execution who ∧
      CanonicalSlotsUsed setup leaks execution who := by
  let app := serviceApplication setup mode deadline leaks
  induction count generalizing execution with
  | zero =>
      obtain ⟨state, _, supported⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      cases (PMF.mem_support_pure_iff _ _).mp supported
      refine ⟨fun entry member => ?_, fun serial used => ?_⟩
      · cases member
      · cases used
  | succ count ih =>
      rw [app.roundsFrom_succ (serviceInitialLaw setup mode) scheduler players count] at reached
      obtain ⟨prior, priorMem, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨atTurn, valid⟩ := ih prior priorMem
      obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode) (count + 1)
          scheduler players count (Nat.le_succ count) prior priorMem
      rw [show count + 1 - count = 0 + 1 by omega] at trace
      exact retainedCanonicalSlots_round bounds covered trace atTurn valid moved

/-- Every legal canonical-menu history has the owner's submission-turn and
used-slot invariants, including pending activations and off-path histories. -/
theorem retainedCanonicalSlots_history {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace :
        ((bounds.canonicalMenu (serviceRuntime setup mode deadline) leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace (some control)) (who : Player) :
    OwnSubmissionsAtTurn setup leaks control.execution who ∧
      CanonicalSlotsUsed setup leaks control.execution who := by
  let app := serviceApplication setup mode deadline leaks
  let menu := bounds.canonicalMenu (serviceRuntime setup mode deadline) leaks
  have covered : ∀ past view response,
      response ∈ (menu.uniformResponses who past view).support →
        response ∈ bounds.canonicalActions (serviceRuntime setup mode deadline) leaks who past
            view := by
    intro past view response supported
    exact (menu.uniformResponses_support who past view response).mp supported
  have supported := menu.roundSupported_uniform (serviceInitialLaw setup mode) horizon
      scheduler trace
  obtain ⟨remaining, actor, execution⟩ := control
  cases actor with
  | none =>
      exact retainedCanonicalSlots_roundsFrom bounds scheduler menu.uniformResponses who covered
        _ execution supported.2
  | some responder =>
      obtain ⟨_, count, prior, command, _, priorMem, _, _, moved⟩ := supported
      obtain ⟨atTurn, valid⟩ := retainedCanonicalSlots_roundsFrom bounds scheduler
        menu.uniformResponses who covered count prior priorMem
      have recallEq := app.environmentStep_recall prior execution command moved
      refine ⟨?_, canonicalSlotsUsed_environment moved who valid⟩
      unfold OwnSubmissionsAtTurn
      rw [recallEq]
      exact atTurn

/-- Slots at or above the binding count are fresh on every retained history,
except the count slot of an unfinished submitted binding. -/
theorem retainedCanonicalSlotsFresh_history {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace :
        ((bounds.canonicalMenu (serviceRuntime setup mode deadline) leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace (some control)) (who : Player) :
    CanonicalSlotsFresh setup leaks control.execution who := by
  obtain ⟨_, valid⟩ := retainedCanonicalSlots_history bounds control trace who
  have rawTrace := (bounds.canonicalMenu (serviceRuntime setup mode deadline) leaks).toRawTrace
      (serviceInitialLaw setup mode) horizon scheduler trace
  rw [serviceInitialLaw_eq_inputs] at rawTrace
  have candidates : (serviceRuntime setup mode deadline).CandidateRecall leaks control.execution :=
    (serviceRuntime setup mode deadline).candidateRecall_history leaks _ horizon scheduler rawTrace
  intro serial above
  by_cases used : serial ∈
      (serviceRuntime setup mode deadline).submittedCandidateSlots leaks
      (control.execution.recall who)
  · rcases valid serial used with lower | pending
    · omega
    · exact Or.inr pending
  · exact Or.inl (candidates who serial used)

/-- At every retained unrecorded own turn the counted slot is fresh, including
after any number of earlier binding misses. -/
theorem retainedCanonicalSlot_fresh_at_turn {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace :
        ((bounds.canonicalMenu (serviceRuntime setup mode deadline) leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace (some control)) (who : Player)
    (event : (serviceGraph setup mode).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (unrecorded : (serviceRuntime setup mode deadline).eventRecorded leaks
        (control.execution.recall who) event = false) :
    control.execution.application.candidates.lookup
      (who, .prepared (control.execution.application.publicView.bindingCount who)) = .fresh := by
  obtain ⟨atTurn, valid⟩ := retainedCanonicalSlots_history bounds control trace who
  have rawTrace := (bounds.canonicalMenu (serviceRuntime setup mode deadline) leaks).toRawTrace
      (serviceInitialLaw setup mode) horizon scheduler trace
  exact canonicalSlot_fresh_of_used rawTrace who atTurn valid event turn unrecorded

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

/-- One prepared slot per source event supplies every retained unrecorded
canonical decision, despite skipped slots after earlier expiries. -/
theorem retainedCanonicalSlot_resources {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (capacity : (serviceGraph setup mode).order.eventCount ≤ bounds.candidateCount)
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace :
        ((bounds.canonicalMenu (serviceRuntime setup mode deadline) leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace (some control)) (who : Player)
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
  obtain ⟨atTurn, valid⟩ := retainedCanonicalSlots_history bounds control trace who
  exact canonicalSlot_resources_of_used bounds capacity
    ((bounds.canonicalMenu (serviceRuntime setup mode deadline) leaks).toRawTrace
        (serviceInitialLaw setup mode) horizon scheduler trace) who atTurn valid event turn
    unrecorded

end Vegas
