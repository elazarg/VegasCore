/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveProvenance
import Interaction.ReactiveServiceInvariant
import Vegas.Pending.ReactiveStateInvariant

/-! # Accepted bindings have an authored commitment in owner recall

Submission provenance and the actual handler associate each accepted candidate
with an earlier owner output addressed to that binding event. Expiry can store
failure but creates no accepted association and no fictitious owner output.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

def AcceptedRecall (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  ∀ event candidate, execution.application.accepted (.inr event) = some candidate →
    ∃ message ∈ (runtime.reactiveApplication leaks).outputs (execution.recall candidate.1),
      message.sender = candidate.1 ∧ message.payload.call = .commitment event candidate

theorem AcceptedRecall.copy
    {before after : (runtime.reactiveApplication leaks).Execution}
    (valid : runtime.AcceptedRecall leaks before)
    (accepted : after.application.accepted = before.application.accepted)
    (recall : ∀ who, before.recall who ⊆ after.recall who) :
    runtime.AcceptedRecall leaks after := by
  intro event candidate stored
  obtain ⟨message, output, author, call⟩ := valid event candidate (accepted ▸ stored)
  obtain ⟨entry, member, emitted⟩ := List.mem_filterMap.mp output
  exact ⟨message, List.mem_filterMap.mpr ⟨entry, recall candidate.1 member, emitted⟩, author, call⟩

theorem acceptedRecall_respond (execution : (runtime.reactiveApplication leaks).Execution)
    (who : Player) (response : (runtime.reactiveApplication leaks).Action)
    (valid : runtime.AcceptedRecall leaks execution) :
    runtime.AcceptedRecall leaks (execution.respond (runtime.reactiveApplication leaks) who
      response) := by
  apply valid.copy runtime leaks
  · exact congrArg PublicView.accepted
      (runtime.reactive_respond_application leaks execution who response).2
  · exact fun observer => (runtime.reactiveApplication leaks).respond_recall_mono
      execution who observer response

private theorem acceptedRecall_handle (execution : (runtime.reactiveApplication leaks).Execution)
    (next : State graph) (message : Message Player (WitnessedPacket graph))
    (valid : runtime.AcceptedRecall leaks execution)
    (issued : execution.Issued (runtime.reactiveApplication leaks) message)
    (handled : handle runtime execution.application
      ⟨message.id, message.payload.call⟩ = some next) :
    runtime.AcceptedRecall leaks { execution with application := next } := by
  rcases message with ⟨id, packet, evidence⟩
  cases packet with
  | commitment event candidate =>
      obtain ⟨_, accepted, owner⟩ :=
        handle_commitment_tables runtime execution.application next id event candidate handled
      intro current handle associated
      change next.accepted (.inr current) = some handle at associated
      rw [accepted] at associated
      by_cases same : current = event
      · subst current
        rw [Function.update_self] at associated
        cases Option.some.inj associated
        obtain ⟨entry, member, _, _, emitted, _⟩ := issued
        change entry ∈ execution.recall id.1 at member
        refine ⟨⟨id, ⟨.commitment event candidate, evidence⟩⟩, ?_, owner.symm, rfl⟩
        exact List.mem_filterMap.mpr ⟨entry, by simpa only [owner] using member, emitted⟩
      · rw [Function.update_of_ne (fun equal => same (Sum.inr.inj equal))] at associated
        exact valid current handle associated
  | opening event candidate raw | withhold event =>
      apply valid.copy runtime leaks
      · exact (handle_resolution_tables runtime execution.application next _
          (by intros; simp) handled).1
      · intro who
        exact List.Subset.refl _
  | malformed raw => simp [handle] at handled

theorem acceptedRecall_environment
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (valid : runtime.AcceptedRecall leaks execution)
    (origins : execution.Provenance (runtime.reactiveApplication leaks))
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support) : runtime.AcceptedRecall leaks next := by
  have recall := (runtime.reactiveApplication leaks).environmentStep_recall
    execution next command reached
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      exact valid
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := FinDist.support_map .. ▸ supported
      exact valid
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : execution.network.lookup id with
      | none => exact valid
      | some message =>
          change runtime.AcceptedRecall leaks { execution with
            application := (handle runtime execution.application
              ⟨message.id, message.payload.call⟩).getD execution.application }
          cases accepted : handle runtime execution.application
              ⟨message.id, message.payload.call⟩ with
          | none => exact valid
          | some state =>
              exact acceptedRecall_handle runtime leaks execution state message valid
                (origins.lookup id message found) accepted
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := FinDist.support_map .. ▸ supported
      exact valid.copy runtime leaks (environmentStep_tables runtime _ _ command changed).1
        (fun _ => List.Subset.refl _)

theorem acceptedRecall_history (inputs : FinDist graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) :
    ∀ {state} (_trace : ((runtime.reactiveApplication leaks).protocol
      (inputs.map State.initial) horizon scheduler).Trace state),
      ReactiveApplication.serviceInvariant (runtime.AcceptedRecall leaks) state := by
  have invariant : (runtime.reactiveApplication leaks).ServiceInvariant scheduler
      (fun execution => runtime.AcceptedRecall leaks execution ∧
        execution.Provenance (runtime.reactiveApplication leaks)) := {
    respond := fun execution who response valid =>
      ⟨runtime.acceptedRecall_respond leaks execution who response valid.1,
        (runtime.reactiveApplication leaks).respond_provenance execution who response valid.2⟩
    environment := fun execution next command valid _ reached =>
      ⟨runtime.acceptedRecall_environment leaks execution next command valid.1 valid.2 reached,
        (runtime.reactiveApplication leaks).environment_provenance execution next command
          valid.2 reached⟩ }
  intro state trace
  have valid := invariant.history (inputs.map State.initial) horizon (by
    intro state supported
    obtain ⟨inputs, _, rfl⟩ := FinDist.support_map .. ▸ supported
    refine ⟨?_, MessageNetwork.Satisfies.empty⟩
    intro event candidate accepted
    obtain ⟨input, owner, payload, impossible, _⟩ :=
      State.initial_accepted_eq_some inputs (.inr event) candidate accepted
    cases impossible) trace
  cases state with
  | none => trivial
  | some control => exact valid.1

end Vegas.EventGraphRuntime
