module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.RevealBlockReflection
public import Vegas.EventGraph.Dependencies

@[expose] public section

/-! # Public runs and their boundaries

Reveal-relaxed public barriers keep every ready event inside an unfinished
public run and make every later completed event follow the entire earlier
prefix. Runs may contain several reveals by the same owner. Under exact reveal
relaxation, a pairwise independent run is additionally a flat block.
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

/-- Exact independent-reveal relaxation retains the weaker public-barrier discipline. -/
theorem RelaxedOrder.revealRelaxedOrdered (relaxed : RelaxedOrder graph) :
    graph.RevealRelaxedOrdered := by
  intro event prior member dependent
  exact (relaxed prior event).mpr
    ⟨((mem_barrierOrder graph.outputLayout prior event).mp member).1, dependent⟩

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

private theorem public_predecessor (relaxed : graph.RevealRelaxedOrdered)
    {prior event : graph.EventId} (earlier : prior.val < event.val)
    (visible : (graph.outputLayout prior).IsPublic ∨ (graph.outputLayout event).IsPublic)
    (dependent : ¬ graph.IndependentReveals prior event) :
    prior ∈ graph.order.predecessors event :=
  relaxed event prior ((mem_barrierOrder graph.outputLayout prior event).mpr
    ⟨earlier, visible.elim Or.inl (fun last => Or.inr (Or.inl last))⟩) dependent

private theorem publication_dependsOn_later (relaxed : graph.RevealRelaxedOrdered)
    {start finish : Nat} (run : RevealRun graph start finish)
    {prior event : graph.EventId} (publication : (graph.outputLayout prior).IsPublication)
    (before : prior.val < finish) (after : finish ≤ event.val) :
    DependsOn graph prior event := by
  by_cases lastPublication : (graph.outputLayout event).IsPublication
  · have later : finish < event.val := by
      by_contra equal
      have same : event.val = finish := by omega
      exact run.closed event same lastPublication
    let closer : graph.EventId := ⟨finish, lt_trans later event.isLt⟩
    have first : prior ∈ graph.order.predecessors closer :=
      public_predecessor relaxed before (Or.inl publication.isPublic)
        (IndependentReveals.not_of_not_publication_right (run.closed closer rfl))
    have second : closer ∈ graph.order.predecessors event :=
      public_predecessor relaxed later (Or.inr lastPublication.isPublic)
        (IndependentReveals.not_of_not_publication_left (run.closed closer rfl))
    exact (Relation.ReflTransGen.single first).tail second
  · exact .single (public_predecessor relaxed (lt_of_lt_of_le before after)
      (Or.inl publication.isPublic)
      (IndependentReveals.not_of_not_publication_right lastPublication))

/-- Every event before the end of a nonempty public run is a dependency of every
later event, including when the closing event is a private binding. -/
theorem RevealRun.dependsOn_crossing (relaxed : graph.RevealRelaxedOrdered)
    {start finish : Nat} (run : RevealRun graph start finish)
    {prior event : graph.EventId} (before : prior.val < finish) (after : finish ≤ event.val) :
    DependsOn graph prior event := by
  by_cases publication : (graph.outputLayout prior).IsPublication
  · exact publication_dependsOn_later relaxed run publication before after
  have early : prior.val < start := by
    by_contra late
    exact publication (run.publications prior (by omega) before)
  let first : graph.EventId := ⟨start, lt_of_lt_of_le run.nonempty run.bounded⟩
  have firstPublication := run.publications first le_rfl run.nonempty
  have toFirst : prior ∈ graph.order.predecessors first :=
    public_predecessor relaxed early (Or.inr firstPublication.isPublic)
      (IndependentReveals.not_of_not_publication_left publication)
  exact (Relation.ReflTransGen.single toFirst).trans
    (publication_dependsOn_later relaxed run firstPublication run.nonempty after)


/-- A completed event of rank at least `finish` follows the whole run. -/
theorem RevealRun.done_of_later (relaxed : graph.RevealRelaxedOrdered)
    {start finish : Nat} (run : RevealRun graph start finish) {cut : graph.order.Cut}
    {event : graph.EventId} (late : finish ≤ event.val) (done : event ∈ cut.completed) :
    ∀ query : graph.EventId, query.val < finish → query ∈ cut.completed :=
  fun _ before => (run.dependsOn_crossing relaxed before late).completed done


/-- **A run of reveals is shaped.** While it is unfinished, only its events are
ready. -/
theorem RevealRun.shaped (relaxed : graph.RevealRelaxedOrdered)
    {start finish : Nat} (run : RevealRun graph start finish) :
    BlockShaped (graph := graph) start finish := by
  intro config inside running event ready
  refine ⟨?_, ?_⟩
  · by_contra smaller
    push Not at smaller
    exact ready.1 (inside.1 event smaller)
  · by_contra late
    push Not at late
    obtain ⟨blocked, before, pending⟩ : ∃ blocked : graph.EventId,
        blocked.val < finish ∧ blocked ∉ config.cut.completed := by
      by_contra all
      push Not at all
      exact running all
    exact pending (EventGraph.DependsOn.completed_of_ready
      (run.dependsOn_crossing relaxed before late)
      (fun same => by subst same; omega) ready)


end Vegas
