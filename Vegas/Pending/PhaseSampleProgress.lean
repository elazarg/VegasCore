/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseResolution
import Vegas.Pending.PhaseLive

/-! # Actual singleton sampling strictly advances the phase namespace -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseRuntimeState

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
private theorem publicData_actor_none {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {output : EventField Player L} {payload : L.Ty}
    (code : EventCode layout output) (shape : output = .publicData payload) :
    code.actor = none := by
  cases code <;> simp_all [EventCode.actor]

omit [DecidableEq Player] in
/-- A live quiescent sampling phase exposes its actual ready chance event. -/
theorem sample_ready_of_live (state : PhaseRuntimeState graph) (frontier : state.Frontier)
    (live : state.Live) (quiescent : ∀ event, ¬ state.current.AutomaticReady event)
    (phase : RuntimePhase graph) (head : state.phases.head? = some phase)
    (kind : phase.kind = .sample) :
    ∃ event, event.val = phase.low ∧ state.current.native.config.cut.Ready event ∧
      graph.actor? event = none := by
  have nonempty : state.phases ≠ [] := by intro empty; simp only [empty] at head; cases head
  rcases state.request_or_sample frontier live quiescent nonempty with request | chance
  · obtain ⟨owner, event, _, ⟨current, member, inside⟩, _, actor, _⟩ := request
    have same : current = phase :=
      (by simpa only [head, Option.mem_some_iff] using member : phase = current).symm
    subst current
    have bounds := (phase.mem_events event).mp inside
    obtain ⟨payload, output⟩ := (kind ▸ phase.fields event bounds.1 bounds.2)
    have : graph.actor? event = none := publicData_actor_none (graph.nodes event) output
    cases this.symm.trans actor
  · obtain ⟨current, event, currentHead, _, rank, ready, ownerless⟩ := chance
    have same : current = phase := Option.some.inj (currentHead.symm.trans head)
    subst current
    exact ⟨event, rank, ready, ownerless⟩

/-- Every supported physical sampling result retires its singleton source
phase. Automatic closure may pass further phases, but cannot return to it. -/
theorem sample_advances_phase (runtime : EventGraphRuntime graph)
    (state next : PhaseRuntimeState graph) (frontier : state.Frontier)
    (phase : RuntimePhase graph) (head : state.phases.head? = some phase)
    (kind : phase.kind = .sample) (event : graph.EventId) (rank : event.val = phase.low)
    (ready : state.current.native.config.cut.Ready event) (chance : graph.actor? event = none)
    (supported : next ∈ (state.environment runtime (.executeSample event)).support) :
    state.attempt.phase < next.attempt.phase := by
  have inside : event ∈ phase.events := (phase.mem_events event).mpr
    ⟨rank.ge, by have nonempty := phase.nonempty; omega⟩
  have allowed : state.commandAllowed (.executeSample event) = true := by
    simp only [commandAllowed, head, Option.any_some, inside, decide_true]
  unfold environment at supported
  rw [ite_eq_left allowed, PMF.support_map] at supported
  obtain ⟨native, nativeSupported, rfl⟩ := supported
  have completed := environmentStep_sample_complete runtime state.current.native native event
    ready chance nativeSupported
  let raw := state.current.environmentResult (.executeSample event) native
  have rawCompleted : event ∈ raw.native.config.cut.completed := completed
  have finished : phase.Finished (phase.drain raw) := by
    intro other member
    have bounds := (phase.mem_events other).mp member
    have singleton := phase.sample_singleton kind
    have same : other = event := Fin.ext (by omega)
    subst other
    exact phase.drain_completed raw rawCompleted
  have noReset : ¬ (phase.kind = .commitment ∧
      (((phase.drain raw).excluded \ state.entry.excluded) ∩ phase.owners).Nonempty) := by
    rintro ⟨commitment, _⟩
    cases kind.symm.trans commitment
  have beforePhase : state.attempt.phase = phase.low := by
    simp only [attempt, head, Option.map_some, Option.getD_some]
  cases phases : state.phases with
  | nil =>
      simp only [phases, List.head?_nil] at head
      cases head
  | cons current remaining =>
      have same : current = phase := by
        simpa only [phases, List.head?_cons, Option.some.injEq] using head
      subst current
      have ordered : (phase :: remaining).IsChain (fun before after => before.high = after.low) :=
        phases ▸ frontier.adjacent
      have strict := phaseLow_lt_tail phase remaining ordered
      have later := (settle_namespace remaining state.generation (phase.drain raw)
        (phase.drain raw) state.retired ordered.tail).2
      change state.attempt.phase <
        (settle (phase :: remaining) state.generation state.entry raw state.retired).attempt.phase
      rw [settle_clean phase remaining state.generation state.entry raw state.retired
        finished noReset, beforePhase]
      exact strict.trans_le later

end Vegas.EventGraphRuntime.PhaseRuntimeState
