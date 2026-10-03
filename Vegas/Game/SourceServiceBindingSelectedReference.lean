/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingSelectedResources
import Vegas.Game.SourceServiceBindingSelectedResponse

/-! # Actual resources at the silent selected-input reference

The reference executes real scheduler rounds and arbitrary foreign responses,
with only the owner silent. At a selected hit its last silent recall entry
recovers the actual before-response execution. Initialized owner submission
and slot invariants persist, and the source configuration has not changed.
The canonical lottery is therefore the original aligned commitment kernel
at protected inputs, and actual silence at closed inputs.
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

/-- Every actual silent-reference hit recovers an initialized raw input with
fresh counted candidate and the unchanged aligned source configuration. Its
lottery is derived from the source compiler and actual owner recall. -/
theorem BindingSource.selected_reference_resources
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {bound : (graph setup).EventId → Nat}
    (players : Player → (application setup leaks).Policy)
    (turns : Nat) (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (event : (graph setup).EventId) (execution : (application setup leaks).Execution)
    (site : BindingSource setup profile event execution.application.config)
    (follows : players site.owner =
      sourceServiceTurnPolicy setup leaks bound turns timing profile site.owner)
    (slot : Fin (turns + 1))
    (boundary : CompletionBoundary setup leaks scheduler players event.val execution)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (stopped : (application setup leaks).Execution)
    (reached : stopped ∈ ((application setup leaks).runUntilHorizon scheduler
      (Function.update players site.owner (application setup leaks).silentPolicy)
      (fun final => event ∈ final.application.config.cut.completed ∨
        sourceServiceSelectedInput? setup leaks site.owner event slot.val
          (final.recall site.owner) ≠ none) horizon execution).support)
    (hit : sourceServiceSelectedInput? setup leaks site.owner event slot.val
      (stopped.recall site.owner) ≠ none) :
    let app := application setup leaks
    ∃ before : app.Execution,
    { stopped with
      «recall» := Function.update stopped.recall site.owner (stopped.recall site.owner).dropLast } =
      before ∧
    Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨horizon - before.environmentRecall.length, some site.owner, before⟩)) ∧
    before.application.config = execution.application.config ∧
    stopped = before.respond app site.owner ⟨none⟩ ∧
    before.application.publicView.ownTurn? site.owner = some event ∧
    sourceServiceTurn setup leaks site.owner event (before.recall site.owner)
      (before.observe app site.owner) = some slot.val ∧
    sourceServiceSelectedInput? setup leaks site.owner event slot.val (before.recall site.owner) =
      none ∧
    OwnSubmissionsAtTurn setup leaks before site.owner ∧
    CanonicalSlotsUsed setup leaks before site.owner ∧
    (runtime setup).eventRecorded leaks (before.recall site.owner) event = false ∧
    before.application.candidates.lookup
      (site.owner, .prepared (before.application.publicView.bindingCount site.owner)) = .fresh ∧
    before.network.Satisfies (fun message => message.sender = site.owner →
      message.payload.call.event? (graph setup) ≠ some event) ∧
    sourceServiceSelectedInput? setup leaks site.owner event slot.val (stopped.recall site.owner) =
      some (before.recall site.owner, before.observe app site.owner) ∧
    sourceServiceCanonicalOpportunity setup leaks bound profile site.owner event
      (before.recall site.owner) (before.observe app site.owner) =
        if before.application.publicView.InclusionFitsDeadline (runtime setup) bound event then
          (commitKernel site.residual (site.source.view site.owner)).map fun value =>
            (runtime setup).reactiveBinding leaks site.owner event site.payload value
              (before.application.publicView.bindingCount site.owner)
        else PMF.pure ⟨none⟩ := by
  classical
  let app := application setup leaks
  let silentPlayers := Function.update players site.owner app.silentPolicy
  let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed ∨
    sourceServiceSelectedInput? setup leaks site.owner event slot.val (final.recall site.owner) ≠
      none
  have ready := (ready_iff_rank setup execution.application.config event.val boundary.ordered
    event).mpr rfl
  have absent := sourceServiceSelectedInput?_of_untouched site.owner event slot.val execution
    (boundary.untouched event rfl)
  obtain ⟨used, before, middle, response, within, actual, configEq, beforeAbsent, chosen, moved,
    current, responseChosen, result, readout⟩ := sourceServiceSelectedInput_origin scheduler
      silentPlayers site.owner event slot.val (horizon - execution.environmentRecall.length)
        execution ready absent stopped hit reached
  change response ∈ (silentPlayers site.owner (middle.recall site.owner)
    (middle.observe app site.owner)).support at responseChosen
  dsimp only [silentPlayers] at responseChosen
  rw [Function.update_self] at responseChosen
  cases app.silentPolicy_cases _ _ response responseChosen
  have initial := canonicalSlots_roundsFrom scheduler players site.owner timing profile follows
    _ execution boundary.supported
  have initialUnrecorded : (runtime setup).eventRecorded leaks (execution.recall site.owner)
      event = false := by
    apply Bool.eq_false_iff.mpr
    intro recorded
    obtain ⟨entry, member, submitted⟩ :=
      ((runtime setup).eventRecorded_iff leaks _ event).mp recorded
    have turn := initial.1 entry member event submitted
    exact boundary.untouched event rfl site.owner entry member
      (PublicView.ownTurn?_spec _ site.owner event turn).1
  have resources := (owner_silent_resources players site.owner event).runRounds scheduler used
    execution before ⟨initial.1, initial.2, initialUnrecorded⟩ actual
  have recalls := app.environmentStep_recall before middle (.activate site.owner) moved
  have middleAbsent : sourceServiceSelectedInput? setup leaks site.owner event slot.val
      (middle.recall site.owner) = none := by rw [recalls]; exact beforeAbsent
  have atTurn : OwnSubmissionsAtTurn setup leaks middle site.owner := by
    unfold OwnSubmissionsAtTurn
    rw [recalls]
    exact resources.1
  have slots := canonicalSlotsUsed_environment moved site.owner resources.2.1
  have unrecorded : (runtime setup).eventRecorded leaks (middle.recall site.owner) event = false :=
    by rw [recalls]; exact resources.2.2
  obtain ⟨startTrace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
    _ bounded execution boundary.supported
  have beforeLength := app.runRounds_environmentRecall_length scheduler silentPlayers used
    execution before actual
  obtain ⟨beforeTrace⟩ := app.raw_trace_runRounds (initialLaw setup) horizon scheduler silentPlayers
    (horizon - execution.environmentRecall.length - used) used execution before
      (by simpa only [Nat.sub_add_cancel (Nat.le_of_lt within)] using startTrace) actual
  have middleLength : middle.environmentRecall.length = before.environmentRecall.length + 1 := by
    rw [(app.activation_visible before middle site.owner moved).2, List.length_append,
      List.length_singleton]
  obtain ⟨raw⟩ := app.raw_trace_environment (initialLaw setup) horizon scheduler
    (horizon - middle.environmentRecall.length) before middle (.activate site.owner)
    (by
      have left : horizon - execution.environmentRecall.length - used =
          horizon - middle.environmentRecall.length + 1 := by omega
      rwa [left] at beforeTrace) chosen moved
  have turn : middle.application.publicView.ownTurn? site.owner = some event := by
    unfold sourceServiceTurn at current
    split at current
    · assumption
    · cases current
  have fresh := canonicalSlot_fresh_of_used raw site.owner atTurn slots event turn unrecorded
  have facts := legalFacts setup leaks horizon scheduler _ raw
  have noPacket := sourceService_unrecorded_event_packets setup leaks middle site.owner event
    facts.provenance unrecorded
  have same : middle.application.config = execution.application.config :=
    (congrArg State.config
      (activation_application setup leaks before middle site.owner moved)).trans configEq
  refine ⟨middle, ?_, ⟨raw⟩, same, result, turn, current, middleAbsent, atTurn, slots, unrecorded,
    fresh, noPacket, readout, ?_⟩
  · rw [result]
    exact sourceService_silent_response_dropLast site.owner middle
  · by_cases fits : middle.application.publicView.InclusionFitsDeadline (runtime setup) bound event
    · rw [ite_eq_left fits, sourceServiceCanonicalOpportunity_protected bound profile site.owner
        event (middle.recall site.owner) (middle.observe app site.owner) unrecorded fits,
        sourceServiceCanonicalPolicy_at_event setup leaks profile site.owner middle event turn
          site.owned]
      have compiled : ((compileEventProfile setup.program profile) site.owner event site.owned
          (setup.eventGraph.fromModeObservation .sequential site.owner
            ((graph setup).playerObserve site.owner middle.application.config))) =
          (commitKernel site.residual (site.source.view site.owner)).map
            (fun value => cast
              (congrArg EventGraph.EventField.Action site.outputEq.symm) value) := by
        rw [same]
        exact BindingSource.compiled_choice execution site
      rw [compiled, PMF.map_comp]
      apply map_congr_on_support _
      intro value _supported
      exact (runtime setup).canonicalServiceDecision_binding leaks site.owner
        (middle.recall site.owner) (middle.observe app site.owner) event site.payload site.outputEq
        site.code (nodeView_eq_bind site.outputEq site.code)
        (middle.application.publicView.bindingCount site.owner)
        (canonicalFreshSlot_canonical site.owner (middle.observe app site.owner).application fresh)
        value
    · rw [ite_eq_right fits]
      unfold sourceServiceCanonicalOpportunity
      simp only [unrecorded, Bool.false_eq_true, ↓reduceIte]
      split
      · exact (fits ‹_›).elim
      · rfl

end Vegas
