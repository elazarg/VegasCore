/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveDecisionMiss
import Vegas.Pending.ReactiveServiceEvaluation

/-! # Marker preservation before explicit service expiry

Player responses, protected inclusion, public sampling and clock advancement
preserve the actual public miss table. An expiry-free fixed command prefix
therefore retains exactly its initial markers, including arbitrary raw calls.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactive_environmentStep_missedEvents_eq (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (before after : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (unexpired : ∀ event, command ≠ .application (.expire event))
    (reached : after ∈ (before.environmentStep (runtime.reactiveApplication leaks)
      command).support) :
    after.application.missedEvents = before.application.missedEvents := by
  classical
  apply Finset.Subset.antisymm
  · intro event missed
    by_contra clear
    exact unexpired event ((runtime.reactive_new_missedEvent leaks command reached
      event clear missed).1)
  · intro event missed
    exact (runtime.reactiveMissedDecisionInvariant leaks event).environmentStep
      before after command missed reached

theorem interactionStep_missedEvents_eq (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (instruction : ServiceInstruction graph)
    (noWire : instruction ≠ .wire)
    (unexpired : ∀ event, instruction ≠ .expire event)
    (before after : (runtime.reactiveApplication leaks).Execution)
    (reached : after ∈ (runtime.interactionStep leaks players network instruction
      before).support) :
    after.application.missedEvents = before.application.missedEvents := by
  let app := runtime.reactiveApplication leaks
  obtain ⟨command, chosen, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have commandUnexpired : ∀ event, command ≠ .application (.expire event) := by
    intro event
    cases instruction with
    | wire => exact (noWire rfl).elim
    | expire addressed => exact (unexpired addressed rfl).elim
    | player who | sample addressed | tick =>
        cases (PMF.mem_support_pure_iff _ _).mp chosen
        intro impossible
        cases impossible
    | includeLatest addressed owner =>
        cases (PMF.mem_support_pure_iff _ _).mp chosen
        unfold reactiveLatest
        split <;> intro impossible <;> cases impossible
  obtain ⟨middle, observed, responded⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
  have environmentEq := runtime.reactive_environmentStep_missedEvents_eq leaks before
    middle command commandUnexpired observed
  cases actor : command.actor? app with
  | none =>
      change after ∈ (app.resume players (command.actor? app) middle).support at responded
      rw [actor] at responded
      cases (PMF.mem_support_pure_iff _ _).mp responded
      exact environmentEq
  | some who =>
      change after ∈ (app.resume players (command.actor? app) middle).support at responded
      rw [actor] at responded
      obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ responded
      have same := congrArg PublicView.missedEvents
        (runtime.reactive_respond_application leaks middle who response).2
      exact same.trans environmentEq

theorem runInteractionPlan_missedEvents_eq (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (plan : List (ServiceInstruction graph))
    (noWire : ServiceInstruction.wire ∉ plan)
    (unexpired : ∀ event, ServiceInstruction.expire event ∉ plan)
    (before after : (runtime.reactiveApplication leaks).Execution)
    (reached : after ∈ (runtime.runInteractionPlan leaks players network plan before).support) :
    after.application.missedEvents = before.application.missedEvents := by
  induction plan generalizing before with
  | nil => cases (PMF.mem_support_pure_iff _ _).mp reached; rfl
  | cons instruction rest ih =>
      obtain ⟨middle, moved, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      exact (ih (fun member => noWire (List.mem_cons_of_mem _ member))
        (fun event member => unexpired event (List.mem_cons_of_mem _ member))
        middle continued).trans
          (runtime.interactionStep_missedEvents_eq leaks players network instruction
            (fun equal => noWire (List.mem_cons.mpr (Or.inl equal.symm)))
            (fun event equal => unexpired event (List.mem_cons.mpr (Or.inl equal.symm)))
            before middle moved)

end Vegas.EventGraphRuntime
