/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Execution

/-!
# Event-graph checkpoint batches

Primitive event-graph execution is intentionally schedule-free and steps one
available event at a time.  Strategic presentations should not necessarily
expose that primitive linearization as information history.  This module
provides the checkpoint layer: a batch is any finite sequence of available
primitive graph events, while public and player observations are taken once at
the checkpoint reached by the whole batch.

`BatchStep` is operational evidence and intentionally ordered.  Strategic
presentation is carried by `CheckpointPresentation`: it provides an explicit
allowed-checkpoint policy, proves each allowed checkpoint is realizable by some
primitive batch, and proves allowed checkpoints advance the completed-node
downset.  The public history-facing type stores only checkpoint states plus
allowed-policy proofs; it does not expose the ordered primitive witness as
data.

The generic presentation keeps progress explicit. Primitive downset
presentations derive that progress separately from graph well-formedness and
guard liveness. They are useful operational checkpoint presentations, not the
default strategic frontier semantics.
-/

namespace Vegas

namespace EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- A finite primitive execution batch from one reachable graph configuration
to another.  The events inside the batch are operational evidence, not the
strategic observation history. -/
inductive BatchStep (G : Graph Player L) :
    ReachableConfig G → ReachableConfig G → Type where
  | nil (state : ReachableConfig G) :
      BatchStep G state state
  | cons {src : ReachableConfig G}
      (event : AvailableEvent G src.1)
      {nextCfg : Config G}
      (hnext : nextCfg ∈ (stepAvailableEvent G src.1 event).support)
      {dst : ReachableConfig G}
      (tail :
        BatchStep G
          ⟨nextCfg, Reachable.step src.2 event hnext⟩ dst) :
      BatchStep G src dst

namespace BatchStep

variable {G : Graph Player L}

/-- One available primitive event as a singleton checkpoint batch. -/
def singleton (src : ReachableConfig G)
    (event : AvailableEvent G src.1)
    {nextCfg : Config G}
    (hnext : nextCfg ∈ (stepAvailableEvent G src.1 event).support) :
    BatchStep G src ⟨nextCfg, Reachable.step src.2 event hnext⟩ :=
  .cons event hnext (.nil _)

/-- Number of primitive events inside a batch.  This is not an observation
count. -/
def length : {src dst : ReachableConfig G} → BatchStep G src dst → Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ _ tail => length tail + 1

/-- Concatenate primitive execution batches. -/
def append {src mid dst : ReachableConfig G}
    (left : BatchStep G src mid)
    (right : BatchStep G mid dst) :
    BatchStep G src dst :=
  match left with
  | .nil _ => right
  | .cons event hnext tail => .cons event hnext (append tail right)

theorem length_append {src mid dst : ReachableConfig G}
    (left : BatchStep G src mid)
    (right : BatchStep G mid dst) :
    (left.append right).length = left.length + right.length := by
  induction left with
  | nil =>
      simp [append, length]
  | cons event hnext tail ih =>
      simp [append, length, ih, Nat.add_comm, Nat.add_left_comm]

/-- Append a concrete tail to an existentially known batch prefix. -/
theorem append_nonempty {src mid dst : ReachableConfig G}
    (pref : Nonempty (BatchStep G src mid))
    (tail : BatchStep G mid dst) :
    Nonempty (BatchStep G src dst) := by
  rcases pref with ⟨prefStep⟩
  exact ⟨prefStep.append tail⟩

/-- If two checkpoints have the same raw graph configuration, a batch tail
from one checkpoint can be replayed from the other up to proof irrelevance.

This is the proof-level transport used by schedule-independence arguments:
once two primitive schedules reach the same graph state, the ordered witness
that got there is irrelevant to all future graph execution. -/
theorem append_tail_from_cfg_eq
    {src leftMid rightMid dst : ReachableConfig G}
    (pref : Nonempty (BatchStep G src rightMid))
    (hcfg : leftMid.1 = rightMid.1)
    (tail : BatchStep G leftMid dst) :
    ∃ dst' : ReachableConfig G,
      Nonempty (BatchStep G src dst') ∧ dst'.1 = dst.1 := by
  have hmid : leftMid = rightMid := Subtype.ext hcfg
  cases hmid
  exact ⟨dst, append_nonempty pref tail, rfl⟩

/-- Local schedule diamond for two distinct available primitive events.

Choosing one supported result for each event at the source gives two supported
two-event batches, one in each order, whose raw graph configurations are equal.
This is the batch-level base case for later permutation/confluence theorems. -/
theorem two_event_swap
    (hwf : G.WF)
    {src : ReachableConfig G}
    (left right : AvailableEvent G src.1)
    (hne : left.node ≠ right.node)
    {leftNext rightNext : Config G}
    (hleft :
      leftNext ∈ (stepAvailableEvent G src.1 left).support)
    (hright :
      rightNext ∈ (stepAvailableEvent G src.1 right).support) :
    ∃ leftFinal rightFinal : ReachableConfig G,
      Nonempty (BatchStep G src leftFinal) ∧
      Nonempty (BatchStep G src rightFinal) ∧
      leftFinal.1 = rightFinal.1 := by
  rcases supported_available_events_diamond
      hwf left right hne hleft hright with
    ⟨rightAfterLeft, leftAfterRight,
      finalLeft, finalRight, hfinalLeft, hfinalRight, hfinalEq⟩
  let leftMid : ReachableConfig G :=
    ⟨leftNext, Reachable.step src.2 left hleft⟩
  let rightMid : ReachableConfig G :=
    ⟨rightNext, Reachable.step src.2 right hright⟩
  let leftFinal : ReachableConfig G :=
    ⟨finalLeft, Reachable.step leftMid.2 rightAfterLeft hfinalLeft⟩
  let rightFinal : ReachableConfig G :=
    ⟨finalRight, Reachable.step rightMid.2 leftAfterRight hfinalRight⟩
  refine ⟨leftFinal, rightFinal, ?_, ?_, hfinalEq⟩
  · exact
      ⟨.cons left hleft
        (BatchStep.singleton leftMid rightAfterLeft hfinalLeft)⟩
  · exact
      ⟨.cons right hright
        (BatchStep.singleton rightMid leftAfterRight hfinalRight)⟩

/-- A swapped two-event prefix can be followed by any tail from the original
two-event checkpoint.

The conclusion keeps both schedules proof-valued.  The first batch is the
original order followed by `tail`; the second starts with the swapped two-event
prefix and reaches a checkpoint with the same raw graph configuration. -/
theorem two_event_swap_with_tail
    (hwf : G.WF)
    {src : ReachableConfig G}
    (left right : AvailableEvent G src.1)
    (hne : left.node ≠ right.node)
    {leftNext rightNext : Config G}
    (hleft :
      leftNext ∈ (stepAvailableEvent G src.1 left).support)
    (hright :
      rightNext ∈ (stepAvailableEvent G src.1 right).support) :
    ∃ leftFinal rightFinal : ReachableConfig G,
      Nonempty (BatchStep G src leftFinal) ∧
      Nonempty (BatchStep G src rightFinal) ∧
      leftFinal.1 = rightFinal.1 ∧
      ∀ {dst : ReachableConfig G}, BatchStep G leftFinal dst →
        ∃ dst' : ReachableConfig G,
          Nonempty (BatchStep G src dst) ∧
          Nonempty (BatchStep G src dst') ∧ dst'.1 = dst.1 := by
  rcases two_event_swap
      hwf left right hne hleft hright with
    ⟨leftFinal, rightFinal, hleftBatch, hrightBatch, hcfg⟩
  refine
    ⟨leftFinal, rightFinal, hleftBatch, hrightBatch, hcfg, ?_⟩
  intro dst tail
  rcases append_tail_from_cfg_eq hrightBatch hcfg tail with
    ⟨dst', hrightTail, hdst⟩
  exact ⟨dst', append_nonempty hleftBatch tail, hrightTail, hdst⟩

/-- Swapping two distinct available primitive events preserves checkpoint
observations. This is the observable form of `two_event_swap`: the two
two-event batches may carry different proof witnesses, but their public and
player-facing graph observations coincide. -/
theorem two_event_swap_observations
    (hwf : G.WF)
    {src : ReachableConfig G}
    (left right : AvailableEvent G src.1)
    (hne : left.node ≠ right.node)
    {leftNext rightNext : Config G}
    (hleft :
      leftNext ∈ (stepAvailableEvent G src.1 left).support)
    (hright :
      rightNext ∈ (stepAvailableEvent G src.1 right).support) :
    ∃ leftFinal rightFinal : ReachableConfig G,
      Nonempty (BatchStep G src leftFinal) ∧
      Nonempty (BatchStep G src rightFinal) ∧
      publicObserve G leftFinal.1 = publicObserve G rightFinal.1 ∧
      ∀ who : Player,
        observe G leftFinal.1 who = observe G rightFinal.1 who := by
  rcases two_event_swap
      hwf left right hne hleft hright with
    ⟨leftFinal, rightFinal, hleftBatch, hrightBatch, hcfg⟩
  refine
    ⟨leftFinal, rightFinal, hleftBatch, hrightBatch, ?_, ?_⟩
  · rw [hcfg]
  · intro who
    rw [hcfg]

/-- A swapped two-event prefix followed by the same tail preserves checkpoint
observations.

This is the first tail-stable schedule-independence theorem: once a local swap
has reached an equal raw checkpoint, all later graph execution can be replayed
from the swapped checkpoint, and the final public/player observations are the
same. -/
theorem two_event_swap_with_tail_observations
    (hwf : G.WF)
    {src : ReachableConfig G}
    (left right : AvailableEvent G src.1)
    (hne : left.node ≠ right.node)
    {leftNext rightNext : Config G}
    (hleft :
      leftNext ∈ (stepAvailableEvent G src.1 left).support)
    (hright :
      rightNext ∈ (stepAvailableEvent G src.1 right).support) :
    ∃ leftFinal rightFinal : ReachableConfig G,
      Nonempty (BatchStep G src leftFinal) ∧
      Nonempty (BatchStep G src rightFinal) ∧
      leftFinal.1 = rightFinal.1 ∧
      ∀ {dst : ReachableConfig G}, BatchStep G leftFinal dst →
        ∃ dst' : ReachableConfig G,
          Nonempty (BatchStep G src dst) ∧
          Nonempty (BatchStep G src dst') ∧
          publicObserve G dst'.1 = publicObserve G dst.1 ∧
          (∀ who : Player,
            observe G dst'.1 who = observe G dst.1 who) := by
  rcases two_event_swap_with_tail
      hwf left right hne hleft hright with
    ⟨leftFinal, rightFinal, hleftBatch, hrightBatch, hcfg, htail⟩
  refine
    ⟨leftFinal, rightFinal, hleftBatch, hrightBatch, hcfg, ?_⟩
  intro dst tail
  rcases htail tail with ⟨dst', hleftTail, hrightTail, hdst⟩
  refine ⟨dst', hleftTail, hrightTail, ?_, ?_⟩
  · rw [hdst]
  · intro who
    rw [hdst]

/-- A local two-event swap remains observationally valid after an arbitrary
already-executed batch prefix.

This is the adjacent-swap form used by permutation-style schedule arguments:
the swap can occur at any checkpoint reached by prior primitive execution, and
the final checkpoint observations are unchanged after replaying the same tail.
-/
theorem two_event_swap_after_prefix_with_tail_observations
    (hwf : G.WF)
    {src mid : ReachableConfig G}
    (pref : Nonempty (BatchStep G src mid))
    (left right : AvailableEvent G mid.1)
    (hne : left.node ≠ right.node)
    {leftNext rightNext : Config G}
    (hleft :
      leftNext ∈ (stepAvailableEvent G mid.1 left).support)
    (hright :
      rightNext ∈ (stepAvailableEvent G mid.1 right).support) :
    ∃ leftFinal rightFinal : ReachableConfig G,
      Nonempty (BatchStep G mid leftFinal) ∧
      Nonempty (BatchStep G mid rightFinal) ∧
      leftFinal.1 = rightFinal.1 ∧
      ∀ {dst : ReachableConfig G}, BatchStep G leftFinal dst →
        ∃ dst' : ReachableConfig G,
          Nonempty (BatchStep G src dst) ∧
          Nonempty (BatchStep G src dst') ∧
          publicObserve G dst'.1 = publicObserve G dst.1 ∧
          (∀ who : Player,
            observe G dst'.1 who = observe G dst.1 who) := by
  rcases two_event_swap_with_tail_observations
      hwf left right hne hleft hright with
    ⟨leftFinal, rightFinal, hleftBatch, hrightBatch, hcfg, htail⟩
  refine
    ⟨leftFinal, rightFinal, hleftBatch, hrightBatch, hcfg, ?_⟩
  intro dst tail
  rcases htail tail with
    ⟨dst', hleftTail, hrightTail, hpublic, hprivate⟩
  exact
    ⟨dst', append_nonempty pref (Classical.choice hleftTail),
      append_nonempty pref (Classical.choice hrightTail),
      hpublic, hprivate⟩

end BatchStep

/-- There exists some primitive execution batch between two checkpoints.

This is deliberately proof-valued: a strategic history can depend on the fact
that a checkpoint transition is realizable without carrying the ordered
primitive schedule as data. -/
abbrev CheckpointStep (G : Graph Player L)
    (src dst : ReachableConfig G) : Prop :=
  Nonempty (BatchStep G src dst)

/-- Policy for strategic checkpoint timing.

Different game presentations can choose different policies: maximal frontiers,
explicit schedulers, downset transitions, or domain-specific barriers.  The
policy boundary is where observation timing is specified. -/
structure CheckpointPolicy (G : Graph Player L) where
  allowed : ReachableConfig G → ReachableConfig G → Prop
  realizable :
    ∀ {src dst}, allowed src dst → CheckpointStep G src dst
  advances :
    ∀ {src dst}, allowed src dst → src.1.done ⊂ dst.1.done

/-- Progress obligation for the primitive downset checkpoint policy.

Every reachable nonterminal checkpoint must have a realizable successor whose
completed-node downset strictly grows.  Raw graph compilation does not prove
this by itself: commit progress depends on guard legality, and internal
progress depends on the compiled event payloads. -/
def DownsetProgress (G : Graph Player L) : Prop :=
  ∀ {state : ReachableConfig G}, ¬ Terminal G state.1 →
    ∃ dst : ReachableConfig G,
      state.1.done ⊂ dst.1.done ∧ CheckpointStep G state dst

/-- Primitive-event progress for reachable graph states.

This is the operational form of progress: every reachable nonterminal
configuration has at least one executable primitive graph event. -/
def AvailableEventProgress (G : Graph Player L) : Prop :=
  ∀ {state : ReachableConfig G}, ¬ Terminal G state.1 →
    Nonempty (AvailableEvent G state.1)

/-- Well-formed graphs with live commit guards have primitive-event progress. -/
theorem availableEventProgress_of_guardLive {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) :
    AvailableEventProgress G :=
  fun hterminal => exists_availableEvent_of_not_terminal hwf hguards hterminal

/-- Primitive-event progress implies progress for the primitive downset
checkpoint policy by taking any single available event as the next checkpoint
batch. -/
theorem primitiveDownsetProgress_of_availableEventProgress {G : Graph Player L}
    (progress : AvailableEventProgress G) :
    DownsetProgress G := by
  intro state hterminal
  rcases progress hterminal with ⟨event⟩
  rcases (stepAvailableEvent G state.1 event).support_nonempty with
    ⟨nextCfg, hnext⟩
  let dst : ReachableConfig G :=
    ⟨nextCfg, Reachable.step state.2 event hnext⟩
  exact
    ⟨dst,
      done_ssubset_of_stepAvailableEvent_support G event hnext,
      ⟨BatchStep.singleton state event hnext⟩⟩

/-- Primitive downset checkpoint policy for schedule-agnostic graph reasoning.

A checkpoint transition is allowed exactly when it is realizable by some
primitive batch and strictly advances the completed-node downset.  The ordered
primitive batch is proof data, not observation history. This policy is
deliberately permissive: it says which downset advances are operationally
possible, not which strategic rounds should be offered to players. -/
def primitiveDownsetCheckpointPolicy
    (G : Graph Player L) : CheckpointPolicy G where
  allowed src dst :=
    src.1.done ⊂ dst.1.done ∧ CheckpointStep G src dst
  realizable := fun hallowed => hallowed.2
  advances := fun hallowed => hallowed.1

/-- A checkpoint presentation suitable for strategic game construction.

The progress field is the bridge obligation not provided by bare graph
compilation: every reachable nonterminal checkpoint must have at least one
allowed successor. -/
structure CheckpointPresentation (G : Graph Player L) where
  policy : CheckpointPolicy G
  nonterminal_exists_allowed :
    ∀ {state}, ¬ Terminal G state.1 → ∃ dst, policy.allowed state dst

/-- Primitive downset checkpoint presentation from an explicit progress
theorem. -/
def primitiveDownsetCheckpointPresentation (G : Graph Player L)
    (progress : DownsetProgress G) : CheckpointPresentation G where
  policy := primitiveDownsetCheckpointPolicy G
  nonterminal_exists_allowed := by
    intro state hterminal
    rcases progress hterminal with ⟨dst, hadvance, hstep⟩
    exact ⟨dst, hadvance, hstep⟩

namespace CheckpointPresentation

variable {G : Graph Player L}

/-- A checkpoint history is a sequence of reachable checkpoint states.  Each
edge carries only proof that the presentation allows the checkpoint transition;
it does not store the ordered primitive batch witness.  Observations are
checkpoint observations, so independent primitive schedules inside a batch do
not create extra history entries or leak through history shape. -/
inductive History (view : CheckpointPresentation G) :
    ReachableConfig G → ReachableConfig G → Type where
  | nil (state : ReachableConfig G) :
      History view state state
  | snoc {src mid dst : ReachableConfig G}
      (history : History view src mid)
      (step : view.policy.allowed mid dst) :
      History view src dst

namespace History

variable {view : CheckpointPresentation G}

/-- Number of batches in a checkpoint history. -/
def length : {src dst : ReachableConfig G} →
    History view src dst → Nat
  | _, _, .nil _ => 0
  | _, _, .snoc history _ => length history + 1

/-- Concatenate checkpoint histories. -/
def append {src mid dst : ReachableConfig G}
    (left : History view src mid)
    (right : History view mid dst) :
    History view src dst :=
  match right with
  | .nil _ => left
  | .snoc history step => .snoc (append left history) step

theorem length_append {src mid dst : ReachableConfig G}
    (left : History view src mid)
    (right : History view mid dst) :
    (left.append right).length = left.length + right.length := by
  induction right with
  | nil =>
      simp [append, length]
  | snoc history step ih =>
      simp [append, length, ih, Nat.add_assoc]

/-- Public observation history, one entry per completed batch. -/
noncomputable def publicView : {src dst : ReachableConfig G} →
    History view src dst → List (PublicObservation G)
  | _, _, .nil _ => []
  | _, dst, .snoc history _ =>
      publicView history ++ [publicObserve G dst.1]

/-- Player observation history, one entry per completed batch. -/
noncomputable def playerView (who : Player) :
    {src dst : ReachableConfig G} →
      History view src dst → List (Observation G who)
  | _, _, .nil _ => []
  | _, dst, .snoc history _ =>
      playerView who history ++ [observe G dst.1 who]

theorem publicView_append {src mid dst : ReachableConfig G}
    (left : History view src mid)
    (right : History view mid dst) :
    (left.append right).publicView =
      left.publicView ++ right.publicView := by
  induction right with
  | nil =>
      simp [append, publicView]
  | snoc history step ih =>
      simp [append, publicView, ih, List.append_assoc]

theorem playerView_append (who : Player)
    {src mid dst : ReachableConfig G}
    (left : History view src mid)
    (right : History view mid dst) :
    (left.append right).playerView who =
      left.playerView who ++ right.playerView who := by
  induction right with
  | nil =>
      simp [append, playerView]
  | snoc history step ih =>
      simp [append, playerView, ih, List.append_assoc]

theorem publicView_length {src dst : ReachableConfig G}
    (history : History view src dst) :
    history.publicView.length = history.length := by
  induction history with
  | nil =>
      simp [publicView, length]
  | snoc history batch ih =>
      simp [publicView, length, ih]

theorem playerView_length (who : Player) {src dst : ReachableConfig G}
    (history : History view src dst) :
    (history.playerView who).length = history.length := by
  induction history with
  | nil =>
      simp [playerView, length]
  | snoc history batch ih =>
      simp [playerView, length, ih]

end History

end CheckpointPresentation

end EventGraph

end Vegas
