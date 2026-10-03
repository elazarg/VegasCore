/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceSelectedReference

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
  obtain ⟨middle, recovered, ⟨raw⟩, same, result, turn, current, middleAbsent, atTurn, slots,
    unrecorded, noPacket, readout⟩ := sourceService_selected_reference_resources players turns
      timing profile site.owner follows event execution slot boundary bounded stopped reached hit
  have fresh := canonicalSlot_fresh_of_used raw site.owner atTurn slots event turn unrecorded
  refine ⟨middle, recovered, ⟨raw⟩, same, result, turn, current, middleAbsent, atTurn, slots,
    unrecorded, fresh, noPacket, readout, ?_⟩
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

end Vegas
