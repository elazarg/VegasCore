/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Sequential
import Vegas.EventGraph.Canonical
import Vegas.Pending.EventServiceCompletion

/-! # Sequential pending service over EventGraph

An `EventGraphRuntime` over `graph.sequentialize` uses the ordinary
event-addressed application and bounded service.  The added dependency edges,
rather than a fixed service visit order, force every semantic completion to be
the least unfinished source-ranked event.  Arbitrary wire traffic and adaptive
service permutations remain in the native policy space.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
/-- Every semantic configuration reachable in the sequential specialization
has a source-ranked completed prefix and chronological completion history. -/
theorem sequential_reachable_rankPrefix
    {inputs : graph.sequentialize.Inputs} {config : graph.sequentialize.Config}
    (reachable : config.Reachable inputs) : RankPrefix config := by
  induction reachable with
  | initial => exact rankPrefix_initial inputs
  | step priorReachable event ready action next supported ih =>
      exact rankPrefix_step ih event ready action
        (fun other unfinished =>
          graph.sequentialize_ready_le_unfinished _ ready unfinished)
        supported

/-- An accepted packet in the sequential specialization can only complete the
least unfinished event, even if the packet was selected by an arbitrary wire
policy at an opportunity reserved for another event. -/
theorem sequential_handle_completes_least
    (runtime : EventGraphRuntime graph.sequentialize)
    (state next : State graph.sequentialize)
    (message : Message Player (Payload graph.sequentialize))
    (accepted : runtime.handle state message = some next) :
    ∃ event, Payload.event? graph.sequentialize message.payload = some event ∧
      ∃ (ready : state.config.cut.Ready event)
          (action : graph.sequentialize.Action event),
        next.config ∈ (state.config.step event ready action).support ∧
        ∀ other, other ∉ state.config.cut.completed → event.val ≤ other.val := by
  obtain ⟨event, addressed, ready, action, supported⟩ :=
    runtime.handle_config_mem_step state next message accepted
  exact ⟨event, addressed, ready, action, supported,
    fun other unfinished =>
      graph.sequentialize_ready_le_unfinished state.config.cut ready unfinished⟩

/-- Every complete native play over the sequential specialization records the
exact source-ranked event list.  This holds for arbitrary native player, wire,
and adaptive service-order policies. -/
theorem servicedSequentialGame_history
    (runtime : EventGraphRuntime graph.sequentialize)
    (inputs : FinDist graph.sequentialize.Inputs)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (players : Player → runtime.application.PlayerPolicy)
    (next : runtime.application.PolicyExecution)
    (supported : next ∈
      ((runtime.servicedEventGame inputs roster reactionRounds wire order).play
        players).support) :
    next.native.application.config.history.map Completion.event =
      List.finRange graph.order.eventCount := by
  obtain ⟨input, _, reachable⟩ := runtime.servicedEventGame_reachable inputs roster
    reactionRounds wire order players next supported
  have ranked := sequential_reachable_rankPrefix reachable
  have terminal := runtime.servicedEventGame_complete inputs roster reactionRounds wire order
    players next supported
  apply ranked.2.eq_of_mem_iff
    (List.sortedLT_finRange graph.order.eventCount).pairwise
  intro event
  rw [next.native.application.config.history_exact, terminal]
  simp

end Vegas.EventGraphRuntime
