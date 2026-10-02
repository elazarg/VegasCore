/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceSettledEvidence

/-! # Source observations stay fixed while a sequential event is ready

A recalled owner turn identifies an actually ready event. Until that event
completes, every response keeps the graph configuration and any supported
configuration step would complete that same event. The player's full graph
observation therefore stays fixed, including private typed values and original
completed actions. Network observations and private candidate catalogues need
not stay fixed.

This holds at every initialized raw or menu history, with arbitrary responses
and scheduling. It assumes no source policy, protection window, unrecorded
event, or asynchronous service contract.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- Recalled turn observations are authentic, and retain the full graph
observation while their ready event remains unfinished. -/
def RecalledReadyObservation (execution : (application setup leaks).Execution) : Prop :=
  ∀ who, ∀ entry ∈ execution.recall who,
    entry.beforeView.application.who = who ∧
      ∀ event, entry.beforeView.application.publicView.ownTurn? who = some event →
        event ∉ execution.application.config.cut.completed →
          execution.application.config.cut.Ready event ∧
            HEq entry.beforeView.application.observation
              ((graph setup).playerObserve who execution.application.config)

/-- The recalled observation invariant is preserved by every player response
and every supported environment command. -/
theorem recalledReadyObservation_serviceInvariant
    (scheduler : (application setup leaks).Scheduler) :
    (application setup leaks).ServiceInvariant scheduler
      (RecalledReadyObservation setup leaks) where
  respond execution who response valid := by
    let app := application setup leaks
    have configEq := ((runtime setup).reactive_respond_application leaks execution who
      response).1
    intro observer entry member
    rcases app.respond_entry_origin execution who observer response entry member with
      earlier | ⟨same, fresh⟩
    · obtain ⟨identity, stable⟩ := valid observer entry earlier
      refine ⟨identity, ?_⟩
      intro event turn unfinished
      rw [configEq] at unfinished ⊢
      exact stable event turn unfinished
    · subst observer
      rw [fresh]
      refine ⟨rfl, ?_⟩
      intro event turn _
      rw [configEq]
      refine ⟨?_, HEq.rfl⟩
      exact (execution.application.publicView_eventReady event).mp
        (PublicView.ownTurn?_spec _ who event turn).1
  environment execution next command valid _ reached := by
    let app := application setup leaks
    have recallEq := app.environmentStep_recall execution next command reached
    have step := contractStep_environment (runtime setup) leaks execution next command reached
    intro who entry member
    rw [recallEq] at member
    obtain ⟨identity, stable⟩ := valid who entry member
    refine ⟨identity, ?_⟩
    intro event turn unfinished
    have unfinishedBefore : event ∉ execution.application.config.cut.completed :=
      fun completed => unfinished (step.completed_mono completed)
    obtain ⟨ready, observationEq⟩ := stable event turn unfinishedBefore
    rcases step with ⟨configEq, _⟩ | ⟨completed, completedReady, action, supported⟩
    · rw [configEq]
      exact ⟨ready, observationEq⟩
    · have same := setup.eventGraph.sequentialize_ready_unique execution.application.config.cut
        completedReady ready
      subst completed
      exfalso
      apply unfinished
      rw [execution.application.config.step_cut event completedReady action next.application.config
        supported]
      exact (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl)

/-- Every initialized raw trace has stable recalled observations. The initial
application law is arbitrary; recall is initially empty. -/
theorem recalledReadyObservation_history
    (initial : PMF (EventGraphRuntime.State (graph setup))) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (control : (application setup leaks).Control)
    (trace : ((application setup leaks).protocol initial horizon scheduler).Trace
      (some control)) : RecalledReadyObservation setup leaks control.execution :=
  (recalledReadyObservation_serviceInvariant setup leaks scheduler).history initial horizon
    (fun _ _ _ _ member => False.elim (List.not_mem_nil member)) trace

/-- Any earlier recalled turn at the current event has the current full graph
observation, independently of what the owner previously sent. -/
theorem recalled_ownTurn_observation
    {initial : PMF (EventGraphRuntime.State (graph setup))} {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol initial horizon scheduler).Trace
      (some control))
    (who : Player) (entry : (application setup leaks).PlayerEntry)
    (member : entry ∈ control.execution.recall who) (event : (graph setup).EventId)
    (earlier : entry.beforeView.application.publicView.ownTurn? who = some event)
    (current : control.execution.application.publicView.ownTurn? who = some event) :
    entry.beforeView.application.who = who ∧
      HEq entry.beforeView.application.observation
        ((graph setup).playerObserve who control.execution.application.config) := by
  obtain ⟨identity, stable⟩ := recalledReadyObservation_history setup leaks initial horizon
    scheduler control trace who entry member
  have ready := (control.execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ who event current).1
  exact ⟨identity, (stable event earlier ready.1).2⟩

/-- The typed observation equality after transporting the authentic player
index to the owner. -/
theorem recalled_ownTurn_observation_cast
    {initial : PMF (EventGraphRuntime.State (graph setup))} {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol initial horizon scheduler).Trace
      (some control))
    (who : Player) (entry : (application setup leaks).PlayerEntry)
    (member : entry ∈ control.execution.recall who) (event : (graph setup).EventId)
    (earlier : entry.beforeView.application.publicView.ownTurn? who = some event)
    (current : control.execution.application.publicView.ownTurn? who = some event)
    (identity : entry.beforeView.application.who = who) :
    (identity ▸ entry.beforeView.application.observation) =
      (graph setup).playerObserve who control.execution.application.config := by
  have same := (recalled_ownTurn_observation setup leaks trace who entry member event earlier
    current).2
  exact eq_of_heq ((eqRec_heq identity entry.beforeView.application.observation).trans same)

/-- The compiler's typed choice law is the same at every recalled turn of the
current event. No equality of network views or response laws is asserted. -/
theorem recalled_ownTurn_compiled_choice
    {initial : PMF (EventGraphRuntime.State (graph setup))} {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol initial horizon scheduler).Trace
      (some control))
    (profile : BehavioralProfile setup.program)
    (who : Player) (entry : (application setup leaks).PlayerEntry)
    (member : entry ∈ control.execution.recall who) (event : (graph setup).EventId)
    (earlier : entry.beforeView.application.publicView.ownTurn? who = some event)
    (current : control.execution.application.publicView.ownTurn? who = some event)
    (identity : entry.beforeView.application.who = who)
    (owned : (graph setup).actor? event = some who) :
    (compileEventProfile setup.program profile) who event owned
        (setup.eventGraph.fromModeObservation .sequential who
          (identity ▸ entry.beforeView.application.observation)) =
      (compileEventProfile setup.program profile) who event owned
        (setup.eventGraph.fromModeObservation .sequential who
          ((graph setup).playerObserve who control.execution.application.config)) := by
  rw [recalled_ownTurn_observation_cast setup leaks trace who entry member event earlier current
    identity]

/-- The same operational observation law holds for any response menu, by its
actual raw trace. -/
theorem menu_recalled_ownTurn_observation
    (menu : (application setup leaks).ResponseMenu)
    {initial : PMF (EventGraphRuntime.State (graph setup))} {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {control : (application setup leaks).Control}
    (trace : (menu.protocol initial horizon scheduler).Trace (some control))
    (who : Player) (entry : (application setup leaks).PlayerEntry)
    (member : entry ∈ control.execution.recall who) (event : (graph setup).EventId)
    (earlier : entry.beforeView.application.publicView.ownTurn? who = some event)
    (current : control.execution.application.publicView.ownTurn? who = some event) :
    entry.beforeView.application.who = who ∧
      HEq entry.beforeView.application.observation
        ((graph setup).playerObserve who control.execution.application.config) :=
  recalled_ownTurn_observation setup leaks (menu.toRawTrace initial horizon scheduler trace) who
    entry member event earlier current

end Vegas
