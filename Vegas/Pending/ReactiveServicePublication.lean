/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveService

/-! # Publication safety at every legal service history

Every inclusion consumes an identifier, independently of application success.
The service enforces this for both reserved inclusion and arbitrary network
requests. The history theorem quantifies over all legal player responses.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactiveLatest_fresh (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (event : graph.EventId) (owner : Player)
    (view : (runtime.reactiveApplication leaks).EnvironmentView)
    (id : MessageId Player) (selected : runtime.reactiveLatest leaks event owner view =
      .include id) :
    view.Unpublished (runtime.reactiveApplication leaks) id := by
  unfold reactiveLatest at selected
  split at selected
  · cases selected
  · rename_i packet found
    cases selected
    exact (of_decide_eq_true (List.find?_eq_some_iff_append.mp found).1).2.2

theorem interactionInstruction_fresh (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (network : runtime.NetworkPolicy leaks)
    (history : List (runtime.reactiveApplication leaks).EnvironmentEntry)
    (view : (runtime.reactiveApplication leaks).EnvironmentView)
    (instruction : ServiceInstruction graph) (id : MessageId Player)
    (selected : (.include id) ∈
      (runtime.interactionInstruction leaks network history view instruction).support) :
    view.Unpublished (runtime.reactiveApplication leaks) id := by
  cases instruction with
  | wire =>
      obtain ⟨choice, _, equal⟩ := FinDist.support_map .. ▸ selected
      exact (runtime.reactiveApplication leaks).atMostOnceCommand_fresh view _ id equal
  | includeLatest event owner =>
      exact runtime.reactiveLatest_fresh leaks event owner view id
        (FinDist.mem_support_pure.mp selected).symm
  | player who | grant event | sample event | tick | expire event =>
      cases FinDist.mem_support_pure.mp selected

theorem interactionScheduler_atMostOnce (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (chosen : ServiceOrder graph) (networkTurns : Nat) (network : runtime.NetworkPolicy leaks) :
    (runtime.reactiveApplication leaks).AtMostOnce
      (runtime.interactionScheduler leaks chosen networkTurns network) := by
  intro history view id selected
  dsimp only [interactionScheduler] at selected
  split at selected
  · cases FinDist.mem_support_pure.mp selected
  · exact runtime.interactionInstruction_fresh leaks network history view _ id selected

theorem interaction_history_publishedOnce (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (chosen : ServiceOrder graph) (networkTurns : Nat) (network : runtime.NetworkPolicy leaks)
    (initial : FinDist (State graph)) (horizon : Nat)
    {state : (runtime.reactiveApplication leaks).ProtocolState}
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon
      (runtime.interactionScheduler leaks chosen networkTurns network)).Trace state) :
    ReactiveApplication.serviceInvariant
      (fun execution => execution.network.PublishedOnce) state :=
  (runtime.reactiveApplication leaks).publishedOnce_history _
    (runtime.interactionScheduler_atMostOnce leaks chosen networkTurns network)
    initial horizon trace

end Vegas.EventGraphRuntime
