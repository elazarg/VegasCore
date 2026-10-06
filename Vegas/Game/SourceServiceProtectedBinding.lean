/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceAsyncTimeliness
import Vegas.Pending.ReactiveBindingReceipts
import Vegas.Pending.ReactiveBindingOmission

/-! # Protected binding calls cannot become public omissions

One owner's protected fresh commitment, with no other identifier emitted by
that owner for the event, has its selected handle recorded whenever the event
completes. Every legal continuation therefore keeps its public omission flag
clear. Other players' responses are unrestricted, and only the scheduler's
protected inclusion obligation is required.

This is an event-specific statement. It assumes the actual fresh call and the
sole own identifier; it does not assert that a whole policy supplies them.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The actual selected handle survives every legal continuation of one protected
binding call. Silence or rejection by other players cannot create its omission. -/
theorem protected_binding_no_miss {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {bound : (graph setup).EventId → Nat}
    (inclusion : ProtectedInclusion (runtime setup) leaks (initialLaw setup) horizon scheduler
      bound)
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (event : (graph setup).EventId) (owner : Player) (candidate : Handle (graph setup))
    (owned : (graph setup).actor? event = some owner)
    (earlier later : List (application setup leaks).PlayerEntry)
    (entry : (application setup leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup)))
    (split : control.execution.recall owner = earlier ++ entry :: later)
    (call : FreshCall setup leaks owner event bound entry message)
    (commitment : message.payload.call = .commitment event candidate)
    (sole : ∀ other ∈ earlier ++ later,
      ¬ EmitsOtherFor (runtime setup) leaks other event message.id) :
    (event ∈ control.execution.application.config.cut.completed →
      control.execution.application.publicView.accepted (.inr event) = some candidate) ∧
      control.execution.application.publicView.missedBinding event = false := by
  have facts := legalFacts setup leaks horizon scheduler control trace
  have recalled : entry ∈ control.execution.recall owner := by rw [split]; simp
  have emitted : message ∈ (application setup leaks).outputs
      (control.execution.recall owner) :=
    List.mem_filterMap.mpr ⟨entry, recalled, call.emitted⟩
  rw [← facts.inputs owner] at emitted
  have input := (List.mem_filter.mp emitted).1
  have initialized : initialLaw setup =
      (setup.initialLaw.map setup.eventInputs).map
        (State.initial (graph := graph setup)) := by
    simp only [initialLaw, serviceInitialLaw, PMF.map_comp, Function.comp_def]
  have rawTrace := trace
  rw [initialized] at rawTrace
  have recorded := (runtime setup).bindingReceipts_history leaks
    (setup.initialLaw.map setup.eventInputs) horizon scheduler control rawTrace
  have whenever (completed : event ∈ control.execution.application.config.cut.completed) :
      control.execution.application.publicView.accepted (.inr event) = some candidate := by
    have receipt := (prescribed_packet_settles setup leaks inclusion trace event owner owned
      earlier later entry message split call sole).2 completed
    obtain ⟨published, onLedger, identified, selected⟩ := recorded message.id receipt
    have same := (facts.unique.inputs message input).ledger published onLedger identified
    subst published
    exact selected event candidate commitment
  refine ⟨whenever, ?_⟩
  by_cases completed : event ∈ control.execution.application.config.cut.completed
  · exact PublicView.missedBinding_of_accepted _ event candidate (whenever completed)
  · have absent : event ∉
        control.execution.application.publicView.observation.completionOrder := by
      intro member
      exact completed ((control.execution.application.config.history_exact event).mp member)
    unfold PublicView.missedBinding
    cases (graph setup).outputLayout event <;> simp only [absent, decide_false, Bool.false_and]

end Vegas
