/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionCompletion
import Vegas.EventGraph.BarrierBlocks

/-! # Ranked phases of a compiled event graph

A descriptor names a nonempty rank interval and its event kind. Its address is
its lower rank, so a retry changes generation without changing source identity.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- The three source phase kinds; samples form singleton barriers. -/
inductive RuntimePhaseKind where
  | commitment
  | reveal
  | sample
  deriving DecidableEq

/-- The output field has the kind prescribed by its source phase. -/
def RuntimePhaseKind.Matches (kind : RuntimePhaseKind) (field : EventField Player L) : Prop :=
  match kind with
  | .commitment => ∃ owner payload, field = .binding owner payload
  | .reveal => ∃ payload, field = .publication payload
  | .sample => ∃ payload, field = .publicData payload

/-- A contiguous source phase, addressed by its lower event rank. -/
structure RuntimePhase (graph : Vegas.EventGraph Player L) where
  kind : RuntimePhaseKind
  low : Nat
  high : Nat
  nonempty : low < high
  bounded : high ≤ graph.order.eventCount
  fields : ∀ event, low ≤ event.val → event.val < high →
    kind.Matches (graph.outputLayout event)
  sample_singleton : kind = .sample → high = low + 1

namespace RuntimePhase

/-- Phase membership is defined by rank, rather than supplied as an unrelated set. -/
def events (phase : RuntimePhase graph) : Finset graph.EventId :=
  Finset.univ.filter fun event => phase.low ≤ event.val ∧ event.val < phase.high

omit [DecidableEq Player] in
@[simp] theorem mem_events (phase : RuntimePhase graph) (event : graph.EventId) :
    event ∈ phase.events ↔ phase.low ≤ event.val ∧ event.val < phase.high := by
  simp only [events, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Exactly the principals with an owned event in the interval. -/
def owners (phase : RuntimePhase graph) : Finset Player :=
  phase.events.biUnion fun event => (graph.actor? event).toFinset

/-- Every phase completes before its successor can be installed. -/
def Finished (phase : RuntimePhase graph) (state : RecoveryState graph) : Prop :=
  phase.events ⊆ state.native.config.cut.completed

omit [DecidableEq Player] in
/-- Completing the whole interval reaches its exact semantic end frontier. -/
theorem finished_prefix (phase : RuntimePhase graph) (state : RecoveryState graph)
    (within : state.native.config.cut.Within phase.low phase.high)
    (finished : phase.Finished state) : state.native.config.cut.IsPrefix phase.high := by
  apply within.isPrefix phase.bounded
  intro event upper
  by_cases lower : phase.low ≤ event.val
  · exact finished ((phase.mem_events event).mpr ⟨lower, upper⟩)
  · exact within.1 event (by omega)

end RuntimePhase

/-- A complete ordered partition. The compiler supplies these structural facts. -/
structure RuntimePhasePlan (graph : Vegas.EventGraph Player L) where
  phases : List (RuntimePhase graph)
  adjacent : phases.IsChain fun before after => before.high = after.low
  first : ∀ phase ∈ phases.head?, phase.low = 0
  last : ∀ phase ∈ phases.getLast?, phase.high = graph.order.eventCount
  empty : phases = [] → graph.order.eventCount = 0

end Vegas.EventGraphRuntime
