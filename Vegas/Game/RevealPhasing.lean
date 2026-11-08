/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealBlockReflection

/-! # Phases of a graph with concurrent independent reveals

In a graph whose dependencies are the rank order relaxed exactly between
independent reveals, and whose runs of consecutive reveals are pairwise
independent, the events split into phases: a solitary event that is not a
reveal, or a maximal run of reveals. A run of reveals is a flat block, and only
its events are ready while it is unfinished; a later event completes only after
the whole run.
-/

noncomputable section

namespace Vegas

open EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- The dependencies are the rank order relaxed exactly between independent
reveals. -/
def RelaxedOrder (graph : Vegas.EventGraph Player L) : Prop :=
  ∀ prior event : graph.EventId,
    prior ∈ graph.order.predecessors event ↔
      prior.val < event.val ∧ ¬ graph.IndependentReveals prior event

/-- Runs of consecutive reveals are pairwise independent: two reveals with only
reveals between them are by distinct owners and do not read each other. -/
def FlatRevealRuns (graph : Vegas.EventGraph Player L) : Prop :=
  ∀ first last : graph.EventId, first.val < last.val →
    (∀ between : graph.EventId, first.val ≤ between.val → between.val ≤ last.val →
      (graph.outputLayout between).IsPublication) →
    graph.IndependentReveals first last

omit [DecidableEq Player] in
/-- An event that is not a reveal precedes every later event. -/
theorem RelaxedOrder.predecessor_of_not_publication (relaxed : RelaxedOrder graph)
    {prior event : graph.EventId} (notPublication : ¬ (graph.outputLayout prior).IsPublication)
    (earlier : prior.val < event.val) : prior ∈ graph.order.predecessors event :=
  (relaxed prior event).mpr ⟨earlier, fun independent => notPublication independent.1⟩

omit [DecidableEq Player] in
/-- Every earlier event precedes an event that is not a reveal. -/
theorem RelaxedOrder.predecessor_of_later_not_publication (relaxed : RelaxedOrder graph)
    {prior event : graph.EventId} (notPublication : ¬ (graph.outputLayout event).IsPublication)
    (earlier : prior.val < event.val) : prior ∈ graph.order.predecessors event :=
  (relaxed prior event).mpr ⟨earlier, fun independent => notPublication independent.2.1⟩

/-- A run of reveals from `start` to `finish`: every event in between is a
reveal, and the run ends at the last event or at an event that is not a reveal. -/
structure RevealRun (graph : Vegas.EventGraph Player L) (start finish : Nat) : Prop where
  nonempty : start < finish
  bounded : finish ≤ graph.order.eventCount
  publications : ∀ event : graph.EventId, start ≤ event.val → event.val < finish →
    (graph.outputLayout event).IsPublication
  closed : ∀ event : graph.EventId, event.val = finish →
    ¬ (graph.outputLayout event).IsPublication

omit [DecidableEq Player] in
/-- A reveal starts a run of reveals. -/
theorem exists_revealRun {start : graph.EventId}
    (publication : (graph.outputLayout start).IsPublication) :
    ∃ finish, RevealRun graph start.val finish := by
  classical
  let Ending := fun finish : Nat => start.val < finish ∧ (graph.order.eventCount ≤ finish ∨
      ∃ event : graph.EventId, event.val = finish ∧ ¬ (graph.outputLayout event).IsPublication)
  have exists_end : ∃ finish, Ending finish := ⟨graph.order.eventCount, start.isLt, Or.inl le_rfl⟩
  obtain ⟨finish, ⟨after, ending⟩, minimal⟩ : ∃ finish, Ending finish ∧
      ∀ smaller < finish, ¬ Ending smaller :=
    ⟨Nat.find exists_end, Nat.find_spec exists_end, fun _ below => Nat.find_min exists_end below⟩
  have inside (smaller : Nat) (below : smaller < finish) (beyond : start.val < smaller) :
      smaller < graph.order.eventCount ∧ ∀ event : graph.EventId, event.val = smaller →
        (graph.outputLayout event).IsPublication := by
    have notEnd := minimal smaller below
    simp only [Ending, not_and, not_or, not_exists, not_le] at notEnd
    obtain ⟨small, everyPublication⟩ := notEnd beyond
    exact ⟨small, fun event same => by simpa using everyPublication event same⟩
  have bounded : finish ≤ graph.order.eventCount := by
    rcases ending with large | ⟨event, same, _⟩
    · by_contra above
      push Not at above
      obtain ⟨small, _⟩ := inside graph.order.eventCount above start.isLt
      omega
    · have := event.isLt
      omega
  refine ⟨finish, after, bounded, fun event early late => ?_, fun event same => ?_⟩
  · rcases Nat.lt_or_ge start.val event.val with beyond | atStart
    · exact (inside event.val late beyond).2 event rfl
    · have same : event = start := Fin.ext (le_antisymm atStart early)
      rw [same]
      exact publication
  · rcases ending with large | ⟨other, otherSame, notPublication⟩
    · exact absurd event.isLt (by omega)
    · have equal : event = other := Fin.ext (same.trans otherSame.symm)
      rw [equal]
      exact notPublication

omit [DecidableEq Player] in
/-- A run of reveals is a flat block. -/
theorem RevealRun.flat {start finish : Nat} (relaxed : RelaxedOrder graph)
    (runs : FlatRevealRuns graph) (run : RevealRun graph start finish) :
    BlockFlat (graph := graph) start finish := by
  intro event prior early late member
  have priorBefore := graph.order.predecessor_lt member
  by_contra notBefore
  push Not at notBefore
  exact ((relaxed prior event).mp member).2 (runs prior event priorBefore
    (fun between betweenEarly betweenLate => run.publications between (by omega) (by omega)))

omit [DecidableEq Player] in
/-- A completed event of rank at least `finish` follows the whole run. -/
theorem RevealRun.done_of_later {start finish : Nat} (relaxed : RelaxedOrder graph)
    (run : RevealRun graph start finish) {cut : graph.order.Cut} {event : graph.EventId}
    (late : finish ≤ event.val) (done : event ∈ cut.completed) :
    ∀ query : graph.EventId, query.val < finish → query ∈ cut.completed := by
  intro query smaller
  have closing : finish < graph.order.eventCount := by
    have := event.isLt
    omega
  let closer : graph.EventId := ⟨finish, closing⟩
  have closerDone : closer ∈ cut.completed := by
    rcases Nat.eq_or_lt_of_le late with same | later
    · have equal : event = closer := Fin.ext same.symm
      rw [← equal]
      exact done
    · exact cut.predecessor_closed done
        (relaxed.predecessor_of_not_publication (run.closed closer rfl) later)
  exact cut.predecessor_closed closerDone
    (relaxed.predecessor_of_later_not_publication (run.closed closer rfl) smaller)

omit [DecidableEq Player] in
/-- **A run of reveals is shaped.** While it is unfinished, only its events are
ready. -/
theorem RevealRun.shaped {start finish : Nat} (relaxed : RelaxedOrder graph)
    (run : RevealRun graph start finish) : BlockShaped (graph := graph) start finish := by
  intro config inside running event ready
  refine ⟨?_, ?_⟩
  · by_contra smaller
    push Not at smaller
    exact ready.1 (inside.1 event smaller)
  · by_contra late
    push Not at late
    have closing : finish < graph.order.eventCount := by
      have := event.isLt
      omega
    let closer : graph.EventId := ⟨finish, closing⟩
    rcases Nat.eq_or_lt_of_le late with same | later
    · obtain ⟨blocked, blockedLate, blockedPending⟩ : ∃ blocked : graph.EventId,
          blocked.val < finish ∧ blocked ∉ config.cut.completed := by
        by_contra all
        push Not at all
        exact running all
      have equal : event = closer := Fin.ext same.symm
      rw [equal] at ready
      exact blockedPending (ready.2
        (relaxed.predecessor_of_later_not_publication (run.closed closer rfl) blockedLate))
    · exact inside.2 closer le_rfl
        (ready.2 (relaxed.predecessor_of_not_publication (run.closed closer rfl) later))

end Vegas
