/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactivePosteriorUniqueness

/-! # Fresh sampled intentions lie outside retained private memory -/

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A first supported prescribed decision cannot name an event already present
in genuine retained private memory, whether the earlier decision transmitted
or was silent. -/
theorem prescribedReactiveResponse_event_not_saved (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    {history : List (runtime.reactiveApplication leaks).PlayerEntry}
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent history)
    (quiet : ∀ entry ∈ history, entry.action.transmission = none → entry.emitted = none)
    (sent : ∀ entry ∈ history, ∀ material, entry.action.transmission = some material →
      ∃ message, entry.emitted = some message ∧ message.payload.call = material.call.packet)
    (intentions : List (Option graph.Completion))
    (supportedMemory : intentions ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior history).support)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (action : (runtime.reactiveApplication leaks).Action) (remembered : graph.Completion)
    (supportedResponse : (action, some remembered) ∈
      (runtime.prescribedReactiveResponse leaks who policy history intentions view).support) :
    remembered.event ∉ intentions.filterMap (fun saved => saved.map Completion.event) := by
  have fresh := runtime.prescribedReactiveResponse_some_fresh leaks who policy history
    intentions view action remembered supportedResponse
  intro member
  obtain ⟨saved, prior, named⟩ := List.mem_filterMap.mp member
  cases saved with
  | none => simp at named
  | some original =>
      have events : original.event = remembered.event := Option.some.inj named
      have recorded := runtime.prescribedReactivePosterior_recorded leaks who policy
        consistent quiet sent intentions supportedMemory original prior
      rw [events] at recorded
      rcases recorded with submitted | decided
      · rw [fresh.1] at submitted
        cases submitted
      · rw [fresh.2.1] at decided
        cases decided

/-- The sampled-frontier freshness fact at actual initialized supported memory,
with response faithfulness and posterior consistency derived operationally. -/
theorem prescribedReactiveResponse_event_not_saved_of_initialized_support
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (recovery : (runtime.reactiveApplication leaks).Policy)
    (focal : players who =
      (runtime.prescribedReactivePolicy leaks who policy).recover recovery)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (count : Nat)
    (state : State graph) (execution : (runtime.reactiveApplication leaks).Execution)
    (reached : execution ∈ ((runtime.reactiveApplication leaks).runRounds scheduler players count
      (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) state)).support)
    (intentions : List (Option graph.Completion))
    (supportedMemory : intentions ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior
        (execution.recall who)).support)
    (action : (runtime.reactiveApplication leaks).Action) (remembered : graph.Completion)
    (supportedResponse : (action, some remembered) ∈
      (runtime.prescribedReactiveResponse leaks who policy (execution.recall who) intentions
        (execution.observe (runtime.reactiveApplication leaks) who)).support) :
    remembered.event ∉ intentions.filterMap (fun saved => saved.map Completion.event) := by
  have consistent :=
    ((runtime.prescribedReactivePolicy leaks who policy).recover_invariant recovery who
      players focal).runRounds scheduler count
        (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) state)
        execution (.nil) reached
  have quiet :=
    ((runtime.reactiveApplication leaks).silentEmission_invariant players who).runRounds
      scheduler count
      (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) state)
      execution (by simp [ReactiveApplication.Execution.initial]) reached
  have sent :=
    (runtime.reactiveEmission_call_invariant leaks players who).runRounds scheduler count
      (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) state)
      execution (by simp [ReactiveApplication.Execution.initial]) reached
  exact runtime.prescribedReactiveResponse_event_not_saved leaks who policy consistent quiet
    sent intentions supportedMemory _ action remembered supportedResponse

end Vegas.EventGraphRuntime
