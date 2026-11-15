module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.RevealRelaxation
public import Vegas.EventGraph.CanonicalStep

@[expose] public section

/-! # Runs of independent bindings between public barriers

Under the barrier order, a maximal run of binding events between two public
events forms a block: once the events before the block have completed, only
block events can become ready until the whole block has completed, whatever
order they complete in. A cut whose completed events contain every event below
the block and none at or beyond its end stays so when a ready event completes
(`Vegas.EventOrder.Cut.Within.complete`), and its ready events lie in the block
until the block is complete (`Vegas.EventGraph.BarrierOrdered.ready_lt_of_within`).
-/

namespace Vegas

open EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

section Block

variable {graph : Vegas.EventGraph Player L}

/-- A configuration inside the block of ranks `[start, finish)`: every earlier
event has completed and no event from `finish` on has. -/
def InBlock (start finish : Nat) (config : graph.Config) : Prop :=
  (∀ event : graph.EventId, event.val < start → event ∈ config.cut.completed) ∧
    ∀ event : graph.EventId, finish ≤ event.val → event ∉ config.cut.completed

/-- Every event of rank before `finish` has completed. -/
def BlockDone (finish : Nat) (config : graph.Config) : Prop :=
  ∀ event : graph.EventId, event.val < finish → event ∈ config.cut.completed

instance (finish : Nat) (config : graph.Config) : Decidable (BlockDone finish config) := by
  unfold BlockDone
  infer_instance

/-- The block's shape: inside an unfinished block, only block events are ready. -/
def BlockShaped (start finish : Nat) : Prop :=
  ∀ config : graph.Config, InBlock start finish config → ¬ BlockDone finish config →
    ∀ event, config.cut.Ready event → start ≤ event.val ∧ event.val < finish

/-- Completion is monotone along graph paths, so a finished block stays finished. -/
theorem BlockDone.path {finish : Nat} {before after : graph.Config}
    (path : Relation.ReflTransGen Config.Step before after)
    (done : BlockDone finish before) : BlockDone finish after :=
  fun event smaller => Config.Step.path_completed_mono path (done event smaller)

/-- Graph steps keep a configuration inside an unfinished block. -/
theorem InBlock.path {start finish : Nat} (shaped : BlockShaped (graph := graph) start finish)
    {before after : graph.Config} (path : Relation.ReflTransGen Config.Step before after)
    (inside : InBlock start finish before) (unfinished : ¬ BlockDone finish after) :
    InBlock start finish after := by
  induction path with
  | refl => exact inside
  | @tail middle last _ moved previous =>
      have middleUnfinished : ¬ BlockDone finish middle := fun done =>
        unfinished (BlockDone.path (Relation.ReflTransGen.single moved) done)
      have middleInside := previous middleUnfinished
      obtain ⟨event, ready, action, member⟩ := moved
      have bounded := shaped middle middleInside middleUnfinished event ready
      refine ⟨fun other smaller => Config.Step.path_completed_mono
        (Relation.ReflTransGen.single ⟨event, ready, action, member⟩)
        (middleInside.1 other smaller), fun other late completed => ?_⟩
      rw [middle.step_cut event ready action last member, EventOrder.Cut.mem_complete]
        at completed
      rcases completed with same | earlier
      · subst same
        omega
      · exact middleInside.2 other late earlier

end Block

end Vegas

namespace Vegas.EventOrder.Cut

variable {order : EventOrder}

/-- Every event below `low` has completed and no event at or beyond `high` has. -/
def Within (cut : order.Cut) (low high : Nat) : Prop :=
  (∀ event : Fin order.eventCount, event.val < low → event ∈ cut.completed) ∧
    ∀ event ∈ cut.completed, event.val < high

/-- A completed prefix lies within itself and every later end. -/
theorem IsPrefix.within {cut : order.Cut} {low high : Nat} (ordered : cut.IsPrefix low)
    (later : low ≤ high) : cut.Within low high :=
  ⟨fun event below => (ordered.2 event).mpr below,
    fun event member => Nat.lt_of_lt_of_le ((ordered.2 event).mp member) later⟩

/-- A cut within a block whose events have all completed is the prefix up to
the block's end. -/
theorem Within.isPrefix {cut : order.Cut} {low high : Nat} (within : cut.Within low high)
    (bounded : high ≤ order.eventCount)
    (complete : ∀ event : Fin order.eventCount, event.val < high → event ∈ cut.completed) :
    cut.IsPrefix high :=
  ⟨bounded, fun event => ⟨within.2 event, complete event⟩⟩

/-- Completing a ready event below the block's end keeps the cut within the
block. -/
theorem Within.complete {cut : order.Cut} {low high : Nat} (within : cut.Within low high)
    (event : Fin order.eventCount) (ready : cut.Ready event) (below : event.val < high) :
    (cut.complete event ready).Within low high := by
  refine ⟨fun other lower => (mem_complete cut event ready other).mpr
    (Or.inr (within.1 other lower)), fun other member => ?_⟩
  rcases (mem_complete cut event ready other).mp member with same | old
  · rw [same]
    exact below
  · exact within.2 other old

end Vegas.EventOrder.Cut

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- **Ready events stay in the block.** On a barrier-ordered graph, at a cut
within a block whose end is a public event or the end of the graph, every ready
event lies in the block unless every block event has completed. -/
theorem BarrierOrdered.ready_lt_of_within (ordered : graph.BarrierOrdered)
    {cut : graph.order.Cut} {low high : Nat} (within : cut.Within low high)
    (barrier : ∀ event : graph.EventId, event.val = high →
      (graph.outputLayout event).IsPublic)
    {event : graph.EventId} (ready : cut.Ready event) :
    event.val < high ∨ ∀ other : graph.EventId, other.val < high → other ∈ cut.completed := by
  by_cases inside : event.val < high
  · exact Or.inl inside
  · right
    intro other below
    by_contra missing
    rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt inside) with atEnd | beyond
    · have isPublic := barrier event atEnd.symm
      exact missing (ready.2 (ordered event (barrierOrder_public_event graph.outputLayout
        (by omega) isPublic)))
    · let wall : graph.EventId := ⟨high, Nat.lt_trans beyond event.isLt⟩
      have isPublic := barrier wall rfl
      have done := ready.2 (ordered event (barrierOrder_public_prior graph.outputLayout
        (show wall.val < event.val from beyond) isPublic))
      exact Nat.lt_irrefl _ (within.2 wall done)


/-- A reveal-relaxed graph keeps every barrier dependency of which one end is not
a publication. -/
theorem RevealRelaxedOrdered.keeps (relaxed : graph.RevealRelaxedOrdered)
    {prior event : graph.EventId}
    (member : prior ∈ (barrierOrder graph.outputLayout).predecessors event)
    (plain : ¬ (graph.outputLayout prior).IsPublication ∨
      ¬ (graph.outputLayout event).IsPublication) :
    prior ∈ graph.order.predecessors event :=
  relaxed event prior member fun independent =>
    plain.elim (fun notPrior => notPrior independent.1) (fun notEvent => notEvent independent.2.1)

/-- **Ready events stay in a block of non-publications.** On a reveal-relaxed
graph, at a cut within a block of events that are not publications, whose end
is a public event or the end of the graph, every ready event lies in the block
unless every block event has completed. -/
theorem RevealRelaxedOrdered.ready_lt_of_within (relaxed : graph.RevealRelaxedOrdered)
    {cut : graph.order.Cut} {low high : Nat} (within : cut.Within low high)
    (barrier : ∀ event : graph.EventId, event.val = high →
      (graph.outputLayout event).IsPublic)
    (plain : ∀ event : graph.EventId, low ≤ event.val → event.val < high →
      ¬ (graph.outputLayout event).IsPublication)
    {event : graph.EventId} (ready : cut.Ready event) :
    event.val < high ∨ ∀ other : graph.EventId, other.val < high → other ∈ cut.completed := by
  by_cases inside : event.val < high
  · exact Or.inl inside
  · right
    intro other below
    by_contra missing
    have lower : low ≤ other.val :=
      Nat.le_of_not_gt fun under => missing (within.1 other under)
    have otherPlain := plain other lower below
    by_cases eventPublic : (graph.outputLayout event).IsPublic
    · exact missing (ready.2 (relaxed.keeps (barrierOrder_public_event graph.outputLayout
        (by omega) eventPublic) (Or.inl otherPlain)))
    · rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt inside) with atEnd | beyond
      · exact eventPublic (barrier event atEnd.symm)
      · let wall : graph.EventId := ⟨high, Nat.lt_trans beyond event.isLt⟩
        have wallPublic := barrier wall rfl
        have done := ready.2 (relaxed.keeps (barrierOrder_public_prior graph.outputLayout
          (show wall.val < event.val from beyond) wallPublic)
          (Or.inr fun publication => eventPublic publication.isPublic))
        exact Nat.lt_irrefl _ (within.2 wall done)


/-- **Ready events stay in a block of reveals.** On a reveal-relaxed graph, at
a cut within a block of publications whose end is an event that is not a
publication or the end of the graph, every ready event lies in the block unless
every block event has completed: a later non-publication waits for every
earlier publication, and a later publication waits for the block's end. -/
theorem RevealRelaxedOrdered.ready_lt_of_within_publications
    (relaxed : graph.RevealRelaxedOrdered)
    {cut : graph.order.Cut} {low high : Nat} (within : cut.Within low high)
    (barrier : ∀ event : graph.EventId, event.val = high →
      ¬ (graph.outputLayout event).IsPublication)
    (publications : ∀ event : graph.EventId, low ≤ event.val → event.val < high →
      (graph.outputLayout event).IsPublication)
    {event : graph.EventId} (ready : cut.Ready event) :
    event.val < high ∨ ∀ other : graph.EventId, other.val < high → other ∈ cut.completed := by
  by_cases inside : event.val < high
  · exact Or.inl inside
  · right
    intro other below
    by_contra missing
    have lower : low ≤ other.val :=
      Nat.le_of_not_gt fun under => missing (within.1 other under)
    have otherPublic := (publications other lower below).isPublic
    by_cases eventPublication : (graph.outputLayout event).IsPublication
    · rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt inside) with atEnd | beyond
      · exact barrier event atEnd.symm eventPublication
      · let wall : graph.EventId := ⟨high, Nat.lt_trans beyond event.isLt⟩
        have done := ready.2 (relaxed.keeps (barrierOrder_public_event graph.outputLayout
          (show wall.val < event.val from beyond) eventPublication.isPublic)
          (Or.inl (barrier wall rfl)))
        exact Nat.lt_irrefl _ (within.2 wall done)
    · exact missing (ready.2 (relaxed.keeps (barrierOrder_public_prior graph.outputLayout
        (by omega) otherPublic) (Or.inr eventPublication)))

end Vegas.EventGraph

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

theorem bindingInterval_shaped
    (relaxed : graph.RevealRelaxedOrdered)
    (start finish : Nat)
    (bindings : ∀ event : graph.EventId, start ≤ event.val →
      event.val < finish → ∃ owner payload,
        graph.outputLayout event = .binding owner payload)
    (barrier : ∀ event : graph.EventId, event.val = finish →
      (graph.outputLayout event).IsPublic) :
    BlockShaped (graph := graph) start finish := by
  intro config inside unfinished event ready
  have within : config.cut.Within start finish :=
    ⟨inside.1, fun other completed => Nat.lt_of_not_ge fun later => inside.2 other later completed⟩
  have lower : start ≤ event.val := Nat.le_of_not_gt fun earlier =>
    ready.1 (inside.1 event earlier)
  refine ⟨lower, ?_⟩
  exact (relaxed.ready_lt_of_within within barrier (by
    intro other early late
    obtain ⟨owner, payload, outputEq⟩ := bindings other early late
    rw [outputEq]
    simp [EventField.IsPublication]) ready).resolve_right unfinished

omit [DecidableEq Player] in
theorem exists_ready_binding_of_block_pending
    (start finish : Nat)
    (bindings : ∀ event : graph.EventId, start ≤ event.val →
      event.val < finish → ∃ owner payload,
        graph.outputLayout event = .binding owner payload)
    (config : graph.Config)
    (inside : InBlock start finish config) (unfinished : ¬ BlockDone finish config) :
    ∃ (event : graph.EventId) (owner : Player) (payload : L.Ty),
      config.cut.Ready event ∧
        graph.outputLayout event = .binding owner payload := by
  classical
  have missing : ∃ event : graph.EventId,
      event.val < finish ∧ event ∉ config.cut.completed := by
    by_contra none
    apply unfinished
    intro event earlier
    by_contra pending
    exact none ⟨event, earlier, pending⟩
  obtain ⟨missingEvent, below, pending⟩ := missing
  obtain ⟨event, ready, earlier⟩ := config.cut.exists_ready_le_of_unfinished missingEvent pending
  have lower : start ≤ event.val := Nat.le_of_not_gt fun smaller =>
    ready.1 (inside.1 event smaller)
  obtain ⟨owner, payload, outputEq⟩ := bindings event lower (earlier.trans_lt below)
  exact ⟨event, owner, payload, ready, outputEq⟩

end Vegas.EventGraph
