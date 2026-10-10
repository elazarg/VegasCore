/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactivePosteriorAlignment

/-! # Stability of original actions under actual response extension -/

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Appending a response and its equally indexed private memory cannot alter
an original completion at a different event. Receipt history is unchanged by
an actual response operation. -/
theorem reactiveOriginal_append_other (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion))
    (aligned : history.length = intentions.length)
    (receipts : List (MessageId Player × Bool))
    (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (saved : Option graph.Completion) (completion : graph.Completion)
    (different : ∀ remembered, saved = some remembered →
      remembered.event ≠ completion.event) :
    runtime.reactiveOriginal leaks who (history ++ [entry]) (intentions ++ [saved])
      receipts completion =
    runtime.reactiveOriginal leaks who history intentions receipts completion := by
  classical
  cases node : nodeView graph completion.event with
  | sample => simp only [reactiveOriginal, node]
  | bind => simp only [reactiveOriginal, node]
  | resolve =>
      cases saved with
      | none =>
          simp [reactiveOriginal, node, List.zip_append aligned, List.filterMap_append]
      | some remembered =>
          have other := different remembered rfl
          simp [reactiveOriginal, node, List.zip_append aligned, List.filterMap_append, other]

/-- A genuine supported original intention always concerns a currently ready
owned event. This applies equally to transmitting and silent responses. -/
theorem prescribedReactiveResponse_some_ready (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion))
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (action : (runtime.reactiveApplication leaks).Action) (remembered : graph.Completion)
    (supported : (action, some remembered) ∈
      (runtime.prescribedReactiveResponse leaks who policy history intentions view).support) :
    view.application.publicView.EventReady remembered.event ∧
      graph.actor? remembered.event = some who := by
  unfold prescribedReactiveResponse at supported
  split at supported
  · simp at supported
  · split at supported
    · simp at supported
    · split at supported
      · split at supported
        · rename_i ready
          split at supported
          · rename_i actor
            obtain ⟨choice, _, image⟩ := PMF.support_map .. ▸ supported
            have intentionEq := Option.some.inj (congrArg Prod.snd image)
            subst remembered
            exact ⟨ready, actor⟩
          · simp at supported
        · simp at supported
      · simp at supported

/-- An actual supported prescribed response preserves every already completed
original action when its private intention is appended beside that response.
Freshness follows from operational readiness, rather than a memory-stability
or desired-history equality hypothesis. -/
theorem reactiveOriginal_respond_completed (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (intentions : List (Option graph.Completion))
    (aligned : (execution.recall who).length = intentions.length)
    (action : (runtime.reactiveApplication leaks).Action) (saved : Option graph.Completion)
    (supported : (action, saved) ∈
      (runtime.prescribedReactiveResponse leaks who policy (execution.recall who) intentions
        (execution.observe (runtime.reactiveApplication leaks) who)).support)
    (completion : graph.Completion)
    (completed : completion.event ∈ execution.application.config.cut.completed) :
    let next := execution.respond (runtime.reactiveApplication leaks) who action
    runtime.reactiveOriginal leaks who (next.recall who) (intentions ++ [saved]) next.receipts
      completion = runtime.reactiveOriginal leaks who (execution.recall who) intentions
        execution.receipts completion := by
  have different : ∀ remembered, saved = some remembered →
      remembered.event ≠ completion.event := by
    intro remembered same
    subst saved
    have ready := (runtime.prescribedReactiveResponse_some_ready leaks who policy
      (execution.recall who) intentions (execution.observe (runtime.reactiveApplication leaks) who)
      action remembered supported).1
    have readyCut : execution.application.config.cut.Ready remembered.event :=
      (execution.application.publicView_eventReady remembered.event).mp ready
    intro events
    exact readyCut.1 (events ▸ completed)
  intro next
  cases action with
  | mk transmission =>
      cases transmission with
      | none =>
          dsimp only [next, ReactiveApplication.Execution.respond]
          simp only [↓reduceIte]
          exact runtime.reactiveOriginal_append_other leaks who (execution.recall who)
            intentions aligned execution.receipts _ saved completion different
      | some material =>
          dsimp only [next, ReactiveApplication.Execution.respond]
          simp only [↓reduceIte]
          exact runtime.reactiveOriginal_append_other leaks who (execution.recall who)
            intentions aligned execution.receipts _ saved completion different

/-- The response stability law at genuine initialized supported memory. The
index alignment is derived from the actual prescribed behavioral posterior. -/
theorem reactiveOriginal_respond_completed_of_initialized_support
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
    (action : (runtime.reactiveApplication leaks).Action) (saved : Option graph.Completion)
    (supportedResponse : (action, saved) ∈
      (runtime.prescribedReactiveResponse leaks who policy (execution.recall who) intentions
        (execution.observe (runtime.reactiveApplication leaks) who)).support)
    (completion : graph.Completion)
    (completed : completion.event ∈ execution.application.config.cut.completed) :
    let next := execution.respond (runtime.reactiveApplication leaks) who action
    runtime.reactiveOriginal leaks who (next.recall who) (intentions ++ [saved]) next.receipts
      completion = runtime.reactiveOriginal leaks who (execution.recall who) intentions
        execution.receipts completion := by
  have consistent :=
    ((runtime.prescribedReactivePolicy leaks who policy).recover_invariant recovery who
      players focal).runRounds scheduler count
        (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) state)
        execution (.nil) reached
  have aligned := (runtime.prescribedReactivePosterior_length leaks who policy consistent
    intentions supportedMemory).symm
  exact runtime.reactiveOriginal_respond_completed leaks who policy execution intentions
    aligned action saved supportedResponse completion completed

end Vegas.EventGraphRuntime
