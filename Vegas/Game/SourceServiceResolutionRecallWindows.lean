/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealService
import Vegas.Pending.EventPublicState
import Vegas.Pending.ReactiveCanonicalDecision
import Vegas.Pending.ReactiveStateInvariant
import Vegas.Pending.ReactiveServiceProgress
import Interaction.ReactiveRecallInvariant

/-! # Inclusion windows at earlier recalled own turns

Once an event is ready, its activation timestamp is unchanged until it
completes. The application clock only increases. A currently protected own
turn therefore guarantees protection at every earlier recalled own turn for
the same event. The result allows arbitrary responses and scheduler commands;
it does not identify source observations or source-choice likelihoods.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

private def recalledLiveActivation (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  ∀ who entry, entry ∈ execution.recall who → ∀ event,
    entry.beforeView.application.publicView.ownTurn? who = some event →
      ∃ entered, entry.beforeView.application.publicView.activatedAt event = some entered ∧
        entry.beforeView.application.publicView.clock ≤ execution.application.clock ∧
        (event ∉ execution.application.config.cut.completed →
          execution.application.activatedAt event = some entered)

private theorem recalledLiveActivation_serviceInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) :
    (runtime.reactiveApplication leaks).ServiceInvariant scheduler (fun execution =>
      ∃ inputs, execution.application.Invariant inputs ∧
        recalledLiveActivation runtime leaks execution) where
  respond execution who action valid := by
    let app := runtime.reactiveApplication leaks
    obtain ⟨inputs, invariant, recalled⟩ := valid
    have progress := runtime.reactive_respond_progress leaks inputs execution who action invariant
    refine ⟨inputs, progress.invariant, ?_⟩
    intro observer entry member event serving
    rcases app.respond_entry_origin execution who observer action entry member with prior | fresh
    · obtain ⟨entered, activated, clock, live⟩ := recalled observer entry prior event serving
      refine ⟨entered, activated, ?_, ?_⟩
      · rw [progress.clock]
        omega
      · intro unfinished
        exact progress.activated event entered
          (live (fun done => unfinished (progress.completed done))) unfinished
    · obtain ⟨rfl, view⟩ := fresh
      rw [view] at serving ⊢
      have own := PublicView.ownTurn?_spec execution.application.publicView observer event serving
      obtain ⟨entered, activated⟩ := invariant.activatedAt_eq_some_of_ready_actor event
        ((execution.application.publicView_eventReady event).mp own.1)
          (by rw [own.2]; rfl)
      refine ⟨entered, activated, ?_, ?_⟩
      · change execution.application.clock ≤ _
        rw [progress.clock]
        omega
      · exact progress.activated event entered activated
  environment execution next command valid _ reached := by
    let app := runtime.reactiveApplication leaks
    obtain ⟨inputs, invariant, recalled⟩ := valid
    have progress := runtime.reactive_environment_progress leaks inputs execution next command
      invariant reached
    refine ⟨inputs, progress.invariant, ?_⟩
    intro who entry member event serving
    rw [app.environmentStep_recall execution next command reached] at member
    obtain ⟨entered, activated, clock, live⟩ := recalled who entry member event serving
    refine ⟨entered, activated, ?_, ?_⟩
    · rw [progress.clock]
      omega
    · intro unfinished
      exact progress.activated event entered
        (live (fun done => unfinished (progress.completed done))) unfinished

variable {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (Vegas.graph setup))}

/-- At every actual initialized raw history, current inclusion protection
implies protection at each recalled own turn for the same event. Current
readiness makes the original activation persist; no source-policy, clear-risk
or previous-window premise is needed. -/
theorem sourceService_recalled_turn_inclusionFits
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    (control : (application setup leaks).Control)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (bound : (Vegas.graph setup).EventId → Nat) (who : Player)
    (event : (Vegas.graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (fits : control.execution.application.publicView.InclusionFitsDeadline (runtime setup) bound
      event)
    (entry : (application setup leaks).PlayerEntry) (member : entry ∈ control.execution.recall who)
    (serving : entry.beforeView.application.publicView.ownTurn? who = some event) :
    entry.beforeView.application.publicView.InclusionFitsDeadline (runtime setup) bound event := by
  have facts := (recalledLiveActivation_serviceInvariant (runtime setup) leaks scheduler).history
    (initialLaw setup) horizon (by
      intro state supported
      obtain ⟨initial, _chosen, rfl⟩ := PMF.support_map .. ▸ supported
      refine ⟨setup.eventInputs initial, State.initial_invariant _, ?_⟩
      intro player previous recalled
      exact (List.not_mem_nil recalled).elim) trace
  obtain ⟨_inputs, _invariant, recalled⟩ := facts
  obtain ⟨entered, activated, clock, live⟩ := recalled who entry member event serving
  have ready := (control.execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec control.execution.application.publicView who event turn).1
  have current := live ready.1
  unfold PublicView.InclusionFitsDeadline at fits ⊢
  rw [activated]
  change (match control.execution.application.activatedAt event with
    | none => False
    | some first => control.execution.application.clock - first + bound event <
        (runtime setup).deadline event) at fits
  rw [current] at fits
  omega

end Vegas
