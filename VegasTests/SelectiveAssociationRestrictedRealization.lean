/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationRestrictedPolicy
import VegasTests.SelectiveAssociationResponses

/-! # Feasible responses at every restricted native decision

The service and candidate-count arguments quantify over the whole bounded raw
game. The prescribed binding repairs earlier submissions, and successful
accepted bindings retain a feasible ordinary opening.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

theorem history_invariants (control : app.Control) (trace : arena.Trace (some control)) :
    control.execution.application.BindingInvariant ∧
      nativeBounds.AcceptedHandles control.execution.application ∧
      control.execution.network.SerialsBeforeNext := by
  have raw := menu.toRawTrace (FinDist.pure nativeInitial) nativeHorizon scheduler trace
  refine ⟨?_, ?_, app.serialsBeforeNext_history scheduler (FinDist.pure nativeInitial)
    nativeHorizon raw⟩
  · exact nativeRuntime.reactiveBindingInvariant_history leaks (FinDist.pure nativeInputs)
      nativeHorizon scheduler (by rw [FinDist.map_pure]; exact raw)
  · exact (nativeBounds.executionHandles_raw_history nativeRuntime leaks
      (FinDist.pure nativeInputs) nativeHorizon scheduler
        (state := some control)
        (by rw [FinDist.map_pure]; exact trace)).1

/-- The two declared candidates suffice at every legal binding history,
including histories created by arbitrary earlier raw responses. -/
theorem binding_fresh (control : app.Control) (trace : arena.Trace (some control))
    (who : Player) (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativeBindingEvent who)) :
    ∃ slot : Fin 2,
      freshSlot (control.execution.observe app who) = some slot ∧
      control.execution.application.candidates.lookup (who, .prepared slot.val) = .fresh := by
  have count := native_decision_recall_count (observation := leaks) (nativeBindingEvent who)
    control trace who active granted who
  have bounded : (control.execution.recall who).length ≤ 1 := by
    rw [count]
    fin_cases who <;> decide
  have raw := menu.toRawTrace (FinDist.pure nativeInitial) nativeHorizon scheduler trace
  have recorded := nativeRuntime.candidateRecall_history leaks (FinDist.pure nativeInputs)
    nativeHorizon scheduler (state := some control)
      (by rw [FinDist.map_pure]; exact raw)
  obtain ⟨serial, serialBound, selected⟩ :=
    nativeRuntime.reactiveFreshSlot_le_recall leaks control.execution who recorded
  have available : ∃ slot : Fin 2,
      (control.execution.observe app who).application.candidates (.prepared slot.val) = .fresh :=
    ⟨⟨serial, by omega⟩, reactiveFreshSlot_spec _ serial selected⟩
  obtain ⟨slot, chosen⟩ := freshSlot_exists _ available
  exact ⟨slot, chosen, freshSlot_spec _ slot chosen⟩

theorem binding_selected (execution : app.Execution) (who : Player)
    (slot : Fin 2) (bit : Bool) (serials : execution.network.SerialsBeforeNext) :
    nativeRuntime.reactiveLatest leaks (nativeBindingEvent who) who
      ((execution.respond app who
        (bindingResponse who (nativeBindingEvent who) slot bit)).observeEnvironment app) =
      .include (who, execution.network.nextSerial who) :=
  nativeRuntime.reactiveLatest_after_submit leaks who (nativeBindingEvent who) execution serials
    ⟨⟨.commitment (nativeBindingEvent who) (who, .prepared slot.val), some ⟨.bool, bit⟩⟩, .none⟩ rfl

theorem binding_realizes (players : Player → app.Policy) (execution : app.Execution)
    (who : Player) (slot : Fin 2) (bit : Bool)
    (valid : execution.application.BindingInvariant)
    (serials : execution.network.SerialsBeforeNext)
    (fresh : execution.application.candidates.lookup (who, .prepared slot.val) = .fresh)
    (ready : execution.application.config.cut.Ready (nativeBindingEvent who))
    (timely : execution.application.WithinDeadline nativeRuntime (nativeBindingEvent who)) :
    ∃ next, (nativeBindingRef who).get? next.config.store = some (.success bit) ∧
      (nativeRuntime.interactionStep leaks players network
        (.includeLatest (nativeBindingEvent who) who)
        (execution.respond app who (bindingResponse who (nativeBindingEvent who) slot bit))).map
          (fun result => result.application) = FinDist.pure next := by
  let submitted := execution.respond app who (bindingResponse who (nativeBindingEvent who) slot bit)
  have facts := nativeRuntime.reactive_respond_application leaks execution who
    (bindingResponse who (nativeBindingEvent who) slot bit)
  have configEq : submitted.application.config = execution.application.config := facts.1
  have publicEq : submitted.application.publicView = execution.application.publicView := facts.2
  have acceptedEq : submitted.application.accepted = execution.application.accepted :=
    congrArg PublicView.accepted publicEq
  have readyAfter : submitted.application.config.cut.Ready (nativeBindingEvent who) := by rwa
    [configEq]
  have timelyAfter : submitted.application.WithinDeadline nativeRuntime (nativeBindingEvent who)
    := by
    change (match submitted.application.publicView.activatedAt (nativeBindingEvent who) with
      | none => False
      | some entered => submitted.application.publicView.clock - entered <
          nativeRuntime.deadline (nativeBindingEvent who))
    rw [publicEq]
    exact timely
  have vacant : submitted.application.accepted (.inr (nativeBindingEvent who)) = none := by
    rw [acceptedEq]
    cases associated : execution.application.accepted (.inr (nativeBindingEvent who)) with
    | none => rfl
    | some accepted => exact False.elim (ready.1
        (valid.toAssociationInvariant.accepted_complete (nativeBindingEvent who) accepted
          associated))
  have unused : submitted.application.HandleUnused (who, .prepared slot.val) := by
    intro field associated
    rw [acceptedEq] at associated
    exact valid.accepted_fixed field _ associated fresh
  have meaning := nativeRuntime.reactiveBinding_result leaks who (nativeBindingEvent who) .bool
    (.success bit) slot.val execution fresh
  change submitted.application.bindingResult (who, .prepared slot.val) .bool = .success bit
    at meaning
  have accepted := nativeRuntime.handle_commitment_eq submitted.application
    (who, execution.network.nextSerial who) (nativeBindingEvent who) (who, .prepared slot.val)
      who .bool
    (native_binding_output who) (native_binding_code who) (native_binding_node who) readyAfter
      timelyAfter
    rfl rfl vacant unused
  refine ⟨(handle nativeRuntime submitted.application
    ⟨(who, execution.network.nextSerial who), .commitment (nativeBindingEvent who)
      (who, .prepared slot.val)⟩).getD submitted.application, ?_, ?_⟩
  · rw [accepted]
    rw [native_binding_ref_eq]
    fin_cases who <;>
      simpa [nativeBindingEvent, alice, bob, State.complete, EventGraph.Config.store,
        EventGraph.FieldRef.get?, EventGraph.Config.complete] using meaning
  · have found : submitted.network.lookup (who, execution.network.nextSerial who) =
        some ⟨(who, execution.network.nextSerial who),
          ⟨.commitment (nativeBindingEvent who) (who, .prepared slot.val), none⟩⟩ :=
      serials.lookup_submit who _
    simp only [interactionStep, interactionInstruction, binding_selected execution who slot bit
      serials, FinDist.pure_bind, ReactiveApplication.dispatch,
      ReactiveApplication.Execution.environmentStep, FinDist.map_pure, FinDist.pure_bind,
      ReactiveApplication.Command.actor?, ReactiveApplication.resume, FinDist.map_pure]
    change FinDist.pure (submitted.includePending app
      (who, execution.network.nextSerial who)).application = _
    unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
    rw [found]
    rfl

/-- The prescribed correction realizes either bit at every unfinished binding
decision. The statement uses actual native histories and the unchanged selector. -/
theorem correctiveBinding_realizes (players : Player → app.Policy)
    (control : app.Control) (trace : arena.Trace (some control)) (who : Player)
    (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativeBindingEvent who))
    (unfinished : nativeBindingEvent who ∉ control.execution.application.config.cut.completed)
    (bit : Bool) :
    ∃ next, (nativeBindingRef who).get? next.config.store = some (.success bit) ∧
      (nativeRuntime.interactionStep leaks players network
        (.includeLatest (nativeBindingEvent who) who)
        (control.execution.respond app who
          (correctiveBinding who (nativeBindingEvent who) bit (control.execution.observe app
            who)))).map
          (fun result => result.application) = FinDist.pure next := by
  have position := (native_decision_cursor (observation := leaks) (nativeBindingEvent who)
    control trace who active granted).2
  obtain ⟨_, service⟩ := native_decision_service (observation := leaks) (nativeBindingEvent who)
    control trace (by simpa only [native_binding_owner] using active) position
  obtain ⟨ready, timely⟩ := service.resolve_left unfinished
  obtain ⟨valid, _, serials⟩ := history_invariants control trace
  obtain ⟨slot, selected, fresh⟩ := binding_fresh control trace who active granted
  simp only [correctiveBinding, selected]
  exact binding_realizes players control.execution who slot bit valid serials fresh ready timely

end VegasTests.SelectiveAssociation.Restricted
