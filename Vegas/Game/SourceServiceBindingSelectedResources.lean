/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingSelectedInput
import Vegas.Game.SourceServiceBindingResponseFactorization

/-! # Owner-local resources before the selected binding response

Before its selected input, the family's supported owner responses are silent.
The owner's initialized submission-turn and canonical-slot invariants therefore
persist through arbitrary foreign responses and actual environment commands.
At the selected raw input these invariants make the counted candidate fresh;
actual packet provenance rules out an earlier packet for the event.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private theorem family_waits_before_input
    (bound : (graph setup).EventId → Nat) (profile : BehavioralProfile setup.program)
    (owner : Player) (event : (graph setup).EventId) (turns : Nat) (slot : Fin (turns + 1))
    (current : (application setup leaks).Execution) (response : (application setup leaks).Action)
    (supported : response ∈ (sourceServiceTurnFamily setup leaks bound profile owner event turns
      slot (current.recall owner) (current.observe (application setup leaks) owner)).support)
    (after : sourceServiceSelectedInput? setup leaks owner event slot.val
      ((current.respond (application setup leaks) owner response).recall owner) = none) :
    sourceServiceSelectedInput? setup leaks owner event slot.val (current.recall owner) = none ∧
      response = ⟨none⟩ := by
  let app := application setup leaks
  have absent : sourceServiceSelectedInput? setup leaks owner event slot.val
      (current.recall owner) = none := by
    by_contra present
    have retained := sourceServiceSelectedInput?_prefix owner event slot.val _ _
      (app.respond_recall_prefix current owner owner response) _ rfl present
    exact present (retained.symm.trans after)
  have unselected : sourceServiceTurn setup leaks owner event (current.recall owner)
      (current.observe app owner) ≠ some slot.val := by
    intro selected
    rw [sourceServiceSelectedInput?_respond owner event slot.val current absent response,
      ite_eq_left selected] at after
    cases after
  have waits : sourceServiceTurnFamily setup leaks bound profile owner event turns slot
      (current.recall owner) (current.observe app owner) =
      app.silentPolicy (current.recall owner) (current.observe app owner) := by
    apply app.turnScheduledPolicy_unselected
    intro other equal
    cases Option.some.inj equal
    exact unselected
  rw [waits] at supported
  exact ⟨absent, app.silentPolicy_cases _ _ response supported⟩

private theorem slots_silent_response
    (current : (application setup leaks).Execution) (owner : Player)
    (atTurn : OwnSubmissionsAtTurn setup leaks current owner)
    (slots : CanonicalSlotsUsed setup leaks current owner) :
    OwnSubmissionsAtTurn setup leaks (current.respond (application setup leaks) owner ⟨none⟩)
      owner ∧
      CanonicalSlotsUsed setup leaks (current.respond (application setup leaks) owner ⟨none⟩)
        owner := by
  let app := application setup leaks
  let next := current.respond app owner ⟨none⟩
  obtain ⟨emitted, recalled, _⟩ := respond_recall_self setup leaks current owner ⟨none⟩
  have appEq : next.application = current.application := rfl
  have recorded (other : (graph setup).EventId) :
      (runtime setup).eventRecorded leaks (next.recall owner) other =
        (runtime setup).eventRecorded leaks (current.recall owner) other :=
    (runtime setup).eventRecorded_respond_other leaks current owner owner ⟨none⟩ other
      (fun _ impossible => by cases impossible)
  have used : (runtime setup).submittedCandidateSlots leaks (next.recall owner) =
      (runtime setup).submittedCandidateSlots leaks (current.recall owner) := by
    rw [(runtime setup).submittedCandidateSlots_respond leaks current owner ⟨none⟩]
    simp only [responseCandidateSlot, Option.toList_none, List.append_nil]
  constructor
  · intro entry member other submitted
    rw [recalled] at member
    rcases List.mem_append.mp member with old | last
    · exact atTurn entry old other submitted
    · cases List.mem_singleton.mp last
      cases submitted
  · intro serial member
    rw [used] at member
    rw [appEq]
    rcases slots serial member with lower | ⟨equal, event, payload, layout, unfinished, submitted⟩
    · exact Or.inl lower
    · right
      exact ⟨equal, event, payload, layout, appEq ▸ unfinished, (recorded event).symm ▸ submitted⟩

private theorem family_slots_before_input
    (players : Player → (application setup leaks).Policy)
    (bound : (graph setup).EventId → Nat) (profile : BehavioralProfile setup.program)
    (owner : Player) (event : (graph setup).EventId) (turns : Nat) (slot : Fin (turns + 1)) :
    (application setup leaks).PolicyInvariant
      (Function.update players owner
        (sourceServiceTurnFamily setup leaks bound profile owner event turns slot))
      (fun current => sourceServiceSelectedInput? setup leaks owner event slot.val
        (current.recall owner) = none →
          OwnSubmissionsAtTurn setup leaks current owner ∧
            CanonicalSlotsUsed setup leaks current owner) := by
  let app := application setup leaks
  constructor
  · intro current actor response holds supported after
    by_cases same : actor = owner
    · subst actor
      rw [Function.update_self] at supported
      obtain ⟨absent, rfl⟩ := family_waits_before_input bound profile owner event turns slot
        current response supported after
      obtain ⟨atTurn, slots⟩ := holds absent
      exact slots_silent_response current owner atTurn slots
    · rw [app.respond_recall_other current actor owner (Ne.symm same) response] at after
      obtain ⟨atTurn, slots⟩ := holds after
      refine ⟨?_, canonicalSlotsUsed_respond_other current (Ne.symm same) response slots⟩
      unfold OwnSubmissionsAtTurn
      rw [app.respond_recall_other current actor owner (Ne.symm same) response]
      exact atTurn
  · intro current next command holds moved after
    have recalls := app.environmentStep_recall current next command moved
    rw [recalls] at after
    obtain ⟨atTurn, slots⟩ := holds after
    refine ⟨?_, canonicalSlotsUsed_environment moved owner slots⟩
    unfold OwnSubmissionsAtTurn
    rw [recalls]
    exact atTurn

/-- An actual initialized owner prefix keeps its canonical-slot and
submission-turn invariants until the selected input, even when every foreign
policy is raw. Earlier waiting responses require no new global cleanliness. -/
theorem sourceService_binding_family_slots_before_input
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy)
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (owner : Player)
    (follows : players owner = sourceServiceTurnPolicy setup leaks bound turns timing profile owner)
    (event : (graph setup).EventId) (slot : Fin (turns + 1))
    (count : Nat) (execution : (application setup leaks).Execution)
    (initialized : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support)
    (used : Nat) (next : (application setup leaks).Execution)
    (reached : next ∈ ((application setup leaks).runRounds scheduler
      (Function.update players owner
        (sourceServiceTurnFamily setup leaks bound profile owner event turns slot))
      used execution).support)
    (absent : sourceServiceSelectedInput? setup leaks owner event slot.val (next.recall owner) =
      none) :
    OwnSubmissionsAtTurn setup leaks next owner ∧ CanonicalSlotsUsed setup leaks next owner := by
  have initial := canonicalSlots_roundsFrom scheduler players owner timing profile follows count
    execution initialized
  exact (family_slots_before_input players bound profile owner event turns slot).runRounds scheduler
    used execution next (fun _ => initial) reached absent

/-- At an actually reached selected input, earlier family waits leave the
counted owner slot fresh and leave no earlier owner packet for the event.
The original aligned source configuration is unchanged, so the current
opportunity draws from its actual commitment kernel when protected, and is
silent when the gate has closed. Foreign policies remain arbitrary. -/
theorem BindingSource.selected_input_resources
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
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
      (Function.update players site.owner
        (sourceServiceTurnFamily setup leaks bound profile site.owner event turns slot))
      (fun final => event ∈ final.application.config.cut.completed ∨
        sourceServiceSelectedInput? setup leaks site.owner event slot.val
          (final.recall site.owner) ≠ none) horizon execution).support)
    (hit : sourceServiceSelectedInput? setup leaks site.owner event slot.val
      (stopped.recall site.owner) ≠ none) :
    let app := application setup leaks
    ∃ (middle : app.Execution) (response : app.Action),
      Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨horizon - middle.environmentRecall.length, some site.owner, middle⟩)) ∧
      middle.application.config = execution.application.config ∧
      middle.application.publicView.ownTurn? site.owner = some event ∧
      sourceServiceTurn setup leaks site.owner event (middle.recall site.owner)
        (middle.observe app site.owner) = some slot.val ∧
      OwnSubmissionsAtTurn setup leaks middle site.owner ∧
      CanonicalSlotsUsed setup leaks middle site.owner ∧
      (runtime setup).eventRecorded leaks (middle.recall site.owner) event = false ∧
      middle.application.candidates.lookup
        (site.owner, .prepared (middle.application.publicView.bindingCount site.owner)) = .fresh ∧
      middle.network.Satisfies (fun message => message.sender = site.owner →
        message.payload.call.event? (graph setup) ≠ some event) ∧
      response ∈ (sourceServiceCanonicalOpportunity setup leaks bound profile site.owner event
        (middle.recall site.owner) (middle.observe app site.owner)).support ∧
      stopped = middle.respond app site.owner response ∧
      sourceServiceSelectedInput? setup leaks site.owner event slot.val
        (stopped.recall site.owner) =
          some (middle.recall site.owner, middle.observe app site.owner) ∧
      sourceServiceCanonicalOpportunity setup leaks bound profile site.owner event
        (middle.recall site.owner) (middle.observe app site.owner) =
          if middle.application.publicView.InclusionFitsDeadline (runtime setup) bound event then
            (commitKernel site.residual (site.source.view site.owner)).map fun value =>
              (runtime setup).reactiveBinding leaks site.owner event site.payload value
                (middle.application.publicView.bindingCount site.owner)
          else PMF.pure ⟨none⟩ := by
  classical
  let app := application setup leaks
  have cases := sourceService_binding_selected_stop contract players turns timing profile
    site.owner follows event site.payload site.outputEq slot execution boundary bounded stopped
      reached
  rcases cases with selected | missed
  · obtain ⟨used, before, middle, response, _within, actual, configEq, ⟨raw⟩, _chosen, moved,
      current, absent, unrecorded, responseChosen, result, readout⟩ := selected
    have recalls := app.environmentStep_recall before middle (.activate site.owner) moved
    have beforeAbsent : sourceServiceSelectedInput? setup leaks site.owner event slot.val
        (before.recall site.owner) = none := by
      rwa [recalls] at absent
    obtain ⟨beforeTurn, beforeSlots⟩ := sourceService_binding_family_slots_before_input scheduler
      players bound turns timing profile site.owner follows event slot
      execution.environmentRecall.length execution boundary.supported used before actual
        beforeAbsent
    have atTurn : OwnSubmissionsAtTurn setup leaks middle site.owner := by
      unfold OwnSubmissionsAtTurn
      rw [recalls]
      exact beforeTurn
    have slots := canonicalSlotsUsed_environment moved site.owner beforeSlots
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
    refine ⟨middle, response, ⟨raw⟩, same, turn, current, atTurn, slots, unrecorded, fresh,
      noPacket, responseChosen, result, readout, ?_⟩
    by_cases fits : middle.application.publicView.InclusionFitsDeadline (runtime setup) bound event
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
  · exact (hit missed.2.1).elim

end Vegas
