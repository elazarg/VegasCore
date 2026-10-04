/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingSelectedResources
import Vegas.Game.SourceServiceSelectedResponse
import Vegas.Pending.ReactiveDecisionOrigin

/-! # Actual resources at the silent selected-input reference

The reference executes real scheduler rounds and arbitrary foreign responses,
with only the owner silent. At a selected hit its last silent recall entry
recovers the actual before-response execution. Initialized owner submission
and slot invariants persist, and the source configuration has not changed.
The recovered input retains the actual owner submission resources; source
constructor-specific lotteries are proved by their concrete callers.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private theorem owner_silent_resources
    (players : Player → (application setup leaks).Policy) (owner : Player)
    (event : (graph setup).EventId) :
    (application setup leaks).PolicyInvariant
      (Function.update players owner (application setup leaks).silentPolicy)
      (fun current => OwnSubmissionsAtTurn setup leaks current owner ∧
        CanonicalSlotsUsed setup leaks current owner ∧
        (runtime setup).eventRecorded leaks (current.recall owner) event = false) := by
  let app := application setup leaks
  constructor
  · intro current actor response holds chosen
    obtain ⟨atTurn, slots, unrecorded⟩ := holds
    by_cases own : actor = owner
    · subst actor
      rw [Function.update_self] at chosen
      cases app.silentPolicy_cases _ _ response chosen
      obtain ⟨nextTurn, nextSlots⟩ := canonicalSlots_silent_response current owner atTurn slots
      refine ⟨nextTurn, nextSlots, ?_⟩
      exact ((runtime setup).eventRecorded_respond_other leaks current owner owner ⟨none⟩ event
        (fun _ impossible => by cases impossible)).trans unrecorded
    · refine ⟨?_, canonicalSlotsUsed_respond_other current (Ne.symm own) response slots, ?_⟩
      · unfold OwnSubmissionsAtTurn
        rw [app.respond_recall_other current actor owner (Ne.symm own) response]
        exact atTurn
      · rw [app.respond_recall_other current actor owner (Ne.symm own) response]
        exact unrecorded
  · intro current next command holds moved
    obtain ⟨atTurn, slots, unrecorded⟩ := holds
    have recalls := app.environmentStep_recall current next command moved
    refine ⟨?_, canonicalSlotsUsed_environment moved owner slots, ?_⟩
    · unfold OwnSubmissionsAtTurn
      rw [recalls]
      exact atTurn
    · rw [recalls]
      exact unrecorded

/-- Every silent-reference selected hit recovers its actual initialized raw
before-response input. Its source configuration is unchanged, with owner
submission resources and no earlier packet for this event. -/
theorem sourceService_selected_reference_resources
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {bound : (graph setup).EventId → Nat}
    (players : Player → (application setup leaks).Policy)
    (turns : Nat) (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (owner : Player)
    (follows : players owner =
      sourceServiceTurnPolicy setup leaks bound turns timing profile owner)
    (event : (graph setup).EventId) (execution : (application setup leaks).Execution)
    (slot : Fin (turns + 1))
    (boundary : CompletionBoundary setup leaks scheduler players event.val execution)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (stopped : (application setup leaks).Execution)
    (reached : stopped ∈ ((application setup leaks).runUntilHorizon scheduler
      (Function.update players owner (application setup leaks).silentPolicy)
      (fun final => event ∈ final.application.config.cut.completed ∨
        sourceServiceSelectedInput? setup leaks owner event slot.val
          (final.recall owner) ≠ none) horizon execution).support)
    (hit : sourceServiceSelectedInput? setup leaks owner event slot.val
      (stopped.recall owner) ≠ none) :
    let app := application setup leaks
    ∃ before : app.Execution,
    { stopped with
      «recall» := Function.update stopped.recall owner (stopped.recall owner).dropLast } =
      before ∧
    Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨horizon - before.environmentRecall.length, some owner, before⟩)) ∧
    before.application.config = execution.application.config ∧
    stopped = before.respond app owner ⟨none⟩ ∧
    before.application.publicView.ownTurn? owner = some event ∧
    sourceServiceTurn setup leaks owner event (before.recall owner)
      (before.observe app owner) = some slot.val ∧
    sourceServiceSelectedInput? setup leaks owner event slot.val (before.recall owner) =
      none ∧
    OwnSubmissionsAtTurn setup leaks before owner ∧
    CanonicalSlotsUsed setup leaks before owner ∧
    (runtime setup).eventRecorded leaks (before.recall owner) event = false ∧
    before.network.Satisfies (fun message => message.sender = owner →
      message.payload.call.event? (graph setup) ≠ some event) ∧
    sourceServiceSelectedInput? setup leaks owner event slot.val (stopped.recall owner) =
      some (before.recall owner, before.observe app owner) := by
  classical
  let app := application setup leaks
  let silentPlayers := Function.update players owner app.silentPolicy
  let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed ∨
    sourceServiceSelectedInput? setup leaks owner event slot.val (final.recall owner) ≠
      none
  have ready := (ready_iff_rank setup execution.application.config event.val boundary.ordered
    event).mpr rfl
  have absent := sourceServiceSelectedInput?_of_untouched owner event slot.val execution
    (boundary.untouched event rfl)
  obtain ⟨used, before, middle, response, within, actual, configEq, beforeAbsent, chosen, moved,
    current, responseChosen, result, readout⟩ := sourceServiceSelectedInput_origin scheduler
      silentPlayers owner event slot.val (horizon - execution.environmentRecall.length)
        execution ready absent stopped hit reached
  change response ∈ (silentPlayers owner (middle.recall owner)
    (middle.observe app owner)).support at responseChosen
  dsimp only [silentPlayers] at responseChosen
  rw [Function.update_self] at responseChosen
  cases app.silentPolicy_cases _ _ response responseChosen
  have initial := canonicalSlots_roundsFrom scheduler players owner timing profile follows
    _ execution boundary.supported
  have initialUnrecorded : (runtime setup).eventRecorded leaks (execution.recall owner)
      event = false := by
    apply Bool.eq_false_iff.mpr
    intro recorded
    obtain ⟨entry, member, submitted⟩ :=
      ((runtime setup).eventRecorded_iff leaks _ event).mp recorded
    have turn := initial.1 entry member event submitted
    exact boundary.untouched event rfl owner entry member
      (PublicView.ownTurn?_spec _ owner event turn).1
  have resources := (owner_silent_resources players owner event).runRounds scheduler used
    execution before ⟨initial.1, initial.2, initialUnrecorded⟩ actual
  have recalls := app.environmentStep_recall before middle (.activate owner) moved
  have middleAbsent : sourceServiceSelectedInput? setup leaks owner event slot.val
      (middle.recall owner) = none := by rw [recalls]; exact beforeAbsent
  have atTurn : OwnSubmissionsAtTurn setup leaks middle owner := by
    unfold OwnSubmissionsAtTurn
    rw [recalls]
    exact resources.1
  have slots := canonicalSlotsUsed_environment moved owner resources.2.1
  have unrecorded : (runtime setup).eventRecorded leaks (middle.recall owner) event = false :=
    by rw [recalls]; exact resources.2.2
  obtain ⟨startTrace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
    _ bounded execution boundary.supported
  have beforeLength := app.runRounds_environmentRecall_length scheduler silentPlayers used
    execution before actual
  obtain ⟨beforeTrace⟩ := app.raw_trace_runRounds (initialLaw setup) horizon scheduler
    silentPlayers (horizon - execution.environmentRecall.length - used) used execution before
      (by simpa only [Nat.sub_add_cancel (Nat.le_of_lt within)] using startTrace) actual
  have middleLength : middle.environmentRecall.length = before.environmentRecall.length + 1 := by
    rw [(app.activation_visible before middle owner moved).2, List.length_append,
      List.length_singleton]
  obtain ⟨raw⟩ := app.raw_trace_environment (initialLaw setup) horizon scheduler
    (horizon - middle.environmentRecall.length) before middle (.activate owner)
    (by
      have left : horizon - execution.environmentRecall.length - used =
          horizon - middle.environmentRecall.length + 1 := by omega
      rwa [left] at beforeTrace) chosen moved
  have turn : middle.application.publicView.ownTurn? owner = some event := by
    unfold sourceServiceTurn at current
    split at current
    · assumption
    · cases current
  have facts := legalFacts setup leaks horizon scheduler _ raw
  have noPacket := sourceService_unrecorded_event_packets setup leaks middle owner event
    facts.provenance unrecorded
  have same : middle.application.config = execution.application.config :=
    (congrArg State.config
      (activation_application setup leaks before middle owner moved)).trans configEq
  refine ⟨middle, ?_, ⟨raw⟩, same, result, turn, current, middleAbsent, atTurn, slots, unrecorded,
    noPacket, readout⟩
  · rw [result]
    exact sourceService_silent_response_dropLast owner middle

/-- If the actual silent reference completes before its selected input, it
has emitted no owner packet for the event and records a real public miss.
The event may be any strategic decision. -/
theorem sourceService_selected_reference_no_input
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (players : Player → (application setup leaks).Policy)
    (turns : Nat) (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (owner : Player)
    (follows : players owner =
      sourceServiceTurnPolicy setup leaks bound turns timing profile owner)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some owner)
    (execution : (application setup leaks).Execution) (slot : Fin (turns + 1))
    (boundary : CompletionBoundary setup leaks scheduler players event.val execution)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (stopped : (application setup leaks).Execution)
    (reached : stopped ∈ ((application setup leaks).runUntilHorizon scheduler
      (Function.update players owner (application setup leaks).silentPolicy)
      (fun final => event ∈ final.application.config.cut.completed ∨
        sourceServiceSelectedInput? setup leaks owner event slot.val
          (final.recall owner) ≠ none) horizon execution).support)
    (absent : sourceServiceSelectedInput? setup leaks owner event slot.val
      (stopped.recall owner) = none) :
    event ∈ stopped.application.config.cut.completed ∧
      event ∈ stopped.application.missedEvents ∧
      (runtime setup).eventRecorded leaks (stopped.recall owner) event = false ∧
      stopped.network.Satisfies (fun message => message.sender = owner →
        message.payload.call.event? (graph setup) ≠ some event) := by
  classical
  let app := application setup leaks
  let silentPlayers := Function.update players owner app.silentPolicy
  let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed ∨
    sourceServiceSelectedInput? setup leaks owner event slot.val (final.recall owner) ≠ none
  have initial := canonicalSlots_roundsFrom scheduler players owner timing profile follows
    _ execution boundary.supported
  have unrecorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = false := by
    apply Bool.eq_false_iff.mpr
    intro recorded
    obtain ⟨entry, member, submitted⟩ :=
      ((runtime setup).eventRecorded_iff leaks _ event).mp recorded
    have turn := initial.1 entry member event submitted
    exact boundary.untouched event rfl owner entry member
      (PublicView.ownTurn?_spec _ owner event turn).1
  obtain ⟨startTrace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
    _ bounded execution boundary.supported
  obtain ⟨used, budget, rounds, length⟩ := app.runUntil_runRounds scheduler silentPlayers stop
    (horizon - execution.environmentRecall.length) execution stopped reached
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds (initialLaw setup) horizon scheduler silentPlayers
    (horizon - execution.environmentRecall.length - used) used execution stopped
    (by simpa only [Nat.sub_add_cancel budget] using startTrace) rounds
  have left : horizon - stopped.environmentRecall.length =
      horizon - execution.environmentRecall.length - used := by omega
  have completed : event ∈ stopped.application.config.cut.completed := by
    rcases app.runUntilHorizon_stopped scheduler silentPlayers stop horizon
      (horizon - execution.environmentRecall.length) execution stopped (by omega) reached with
      halted | spent
    · exact halted.resolve_right (fun present => present absent)
    · rw [← left, spent, Nat.sub_self] at finalTrace
      have complete := contract.completes ⟨0, none, stopped⟩ finalTrace (by
        change 0 = 0 ∧ _
        exact ⟨rfl, rfl⟩)
      rw [complete]
      exact Finset.mem_univ _
  have resources := (owner_silent_resources players owner event).runRounds scheduler used
    execution stopped ⟨initial.1, initial.2, unrecorded⟩ rounds
  have facts := legalFacts setup leaks horizon scheduler _ finalTrace
  have noPacket := sourceService_unrecorded_event_packets setup leaks stopped owner event
    facts.provenance resources.2.2
  have marked : event ∈ stopped.application.missedEvents := by
    by_contra clear
    have inputTrace := finalTrace
    rw [initialLaw_eq_inputs] at inputTrace
    have origin := completedDecisionRecall_history (runtime setup) leaks
      (setup.initialLaw.map setup.eventInputs) horizon scheduler inputTrace
    obtain ⟨message, output, authored, named, _receipt⟩ := origin event owner owned completed clear
    rw [← facts.inputs owner] at output
    exact noPacket.inputs message (List.mem_filter.mp output).1 authored named
  exact ⟨completed, marked, resources.2.2, noPacket⟩

end Vegas
