/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseLive
import Vegas.Pending.PhaseResolution

/-! # Genuine ready requests and disjoint completed phase namespaces -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- Every native-ready event is in the current maximal phase. -/
theorem ready_current_phase (state : PhaseRuntimeState graph)
    (ordered : graph.RevealRelaxedOrdered) (frontier : state.Frontier) (live : state.Live)
    (maximal : state.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (event : graph.EventId) (ready : state.current.native.config.cut.Ready event) :
    ∃ phase ∈ state.phases.head?, event ∈ phase.events := by
  cases phases : state.phases with
  | nil =>
      have complete := frontier.positioned
      rw [phases] at complete
      exact (ready.1 ((complete.2 event).mpr event.isLt)).elim
  | cons phase remaining =>
      have head : phase ∈ state.phases.head? := by
        simp only [phases, List.head?_cons, Option.mem_some_iff]
      have position := frontier.positioned
      rw [phases] at position
      have adjacent := frontier.adjacent
      have last := frontier.last
      rw [phases] at adjacent last maximal
      have boundaries := phase_boundaries phase remaining adjacent last maximal
      refine ⟨phase, by simp only [List.head?_cons, Option.mem_some_iff],
        phase.ready_mem state.current ordered position.2 (live phase head)
        boundaries.1 boundaries.2 event ready⟩

/-- Genuine normalized metadata turns each ready owned event into a precise
current-attempt request; excluded owners have no ready event. -/
theorem request_of_ready (state : PhaseRuntimeState graph)
    (ordered : graph.RevealRelaxedOrdered) (frontier : state.Frontier) (live : state.Live)
    (maximal : state.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (quiescent : ∀ event, ¬ state.current.AutomaticReady event)
    (event : graph.EventId) (ready : state.current.native.config.cut.Ready event)
    (owner : Player) (actor : graph.actor? event = some owner) :
    state.SeedRequest owner ⟨state.attempt, event⟩ := by
  refine ⟨rfl, state.ready_current_phase ordered frontier live maximal event ready,
    ready, actor, ?_⟩
  intro excluded
  exact quiescent event ⟨ready, by simpa only [actor] using excluded⟩

omit [DecidableEq Player] in
/-- Consuming a strict phase suffix puts its lower rank beyond every event in
the old head. This statement is independent of rollback inside either phase. -/
theorem event_before_later_phase (before after : PhaseRuntimeState graph)
    (ordered : before.Ordered) (suffix : after.phases <:+ before.phases)
    (different : before.attempt.phase ≠ after.attempt.phase)
    (event : graph.EventId) (inside : ∃ phase ∈ before.phases.head?, event ∈ phase.events) :
    event.val < after.attempt.phase := by
  obtain ⟨phase, head, member⟩ := inside
  cases phases : before.phases with
  | nil => simp only [phases, List.head?_nil, Option.not_mem_none] at head
  | cons first remaining =>
      have same : first = phase := by
        simpa only [phases, List.head?_cons, Option.mem_some_iff] using head
      subst first
      change before.phases.IsChain (fun first second => first.high = second.low) at ordered
      rw [phases] at suffix ordered
      rcases List.suffix_cons_iff.mp suffix with same | later
      · exact (different (by simp only [attempt, phases, same])).elim
      · have upper := (phase.mem_events event).mp member
        have tailLow : phase.high ≤ phaseLow remaining := by
          cases remaining with
          | nil => exact phase.bounded
          | cons next tail =>
              exact (List.isChain_cons_cons.mp ordered).1.le
        exact upper.2.trans_le (tailLow.trans (phaseLow_suffix ordered.tail later))

/-- A retained ready event cannot belong to both an earlier phase and its
strictly later installed suffix. -/
theorem ready_namespace_phase (before after : PhaseRuntimeState graph)
    (orderedGraph : graph.RevealRelaxedOrdered) (frontier : before.Frontier)
    (live : before.Live)
    (maximal : before.phases.IsChain fun first second =>
      first.kind ≠ second.kind ∨ first.kind = .sample)
    (suffix : after.phases <:+ before.phases) (owner : Player)
    (coordinate : CommitAttemptEvent graph)
    (requested : after.SeedRequest owner coordinate)
    (ready : before.current.native.config.cut.Ready coordinate.event) :
    before.attempt.phase = after.attempt.phase := by
  by_contra different
  have earlier := event_before_later_phase before after frontier.adjacent suffix different
    coordinate.event (ready_current_phase before orderedGraph frontier live maximal _ ready)
  obtain ⟨phase, head, inside⟩ := requested.2.1
  have lower := ((phase.mem_events coordinate.event).mp inside).1
  have headEq : after.phases.head? = some phase := Option.mem_def.mp head
  have phaseEq : after.attempt.phase = phase.low := by
    simp only [attempt, headEq, Option.map_some, Option.getD_some]
  omega

end PhaseRuntimeState

/-- Every actual application transition consumes only a suffix of its plan. -/
theorem phaseApplication_phaseSuffix (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).StepRelation
      (fun before after => after.phases <:+ before.phases) where
  refl _ := List.suffix_refl _
  submit _ _ _ := List.suffix_refl _
  handle state message next accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, _, rfl⟩ := Option.map_eq_some_iff.mp accepted
      exact PhaseRuntimeState.settle_suffix _ _ _ _ _
    · cases accepted
  environment state command next reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · obtain ⟨native, _, rfl⟩ := PMF.support_map .. ▸ reached
      exact PhaseRuntimeState.settle_suffix _ _ _ _ _
    · cases (PMF.mem_support_pure_iff _ _).mp reached
      exact List.suffix_refl _

end Vegas.EventGraphRuntime
