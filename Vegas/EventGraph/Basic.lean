/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.Order
import Vegas.EventGraph.Code
import Vegas.Foundation.DefaultHistory

/-! # Dependency-driven event graphs

An event graph fixes a typed input layout, one typed output per event, local
event code, and the dependencies that make every declared read available.
Initial values are deliberately absent from the graph: one graph and one
strategy space can therefore serve an entire private setup distribution.
-/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} {L : IExpr} [R : IExpr.ResultTypes L]

/-- Field identities distinguish initial inputs from event outputs. -/
abbrev FieldId (inputCount eventCount : Nat) :=
  Sum (Fin inputCount) (Fin eventCount)

/-- The shared field layout induced by separate input and event-output layouts. -/
def fieldLayout {inputCount eventCount : Nat}
    (inputs : Fin inputCount → EventField Player L)
    (outputs : Fin eventCount → EventField Player L) :
    FieldId inputCount eventCount → EventField Player L :=
  Sum.elim inputs outputs

end Vegas.EventGraph

namespace Vegas

/-- A finite typed event graph. Numeric event ids witness one topological
ranking, while execution may select any event ready at the current cut.

`reads_available` is local structural evidence, not a whole-run simulation
hypothesis: every field read by a node is either an input or is produced by a
declared predecessor. -/
structure EventGraph (Player : Type) (L : IExpr) [IExpr.ResultTypes L] where
  inputCount : Nat
  order : EventOrder
  inputLayout : Fin inputCount → EventGraph.EventField Player L
  outputLayout : Fin order.eventCount → EventGraph.EventField Player L
  nodes : (event : Fin order.eventCount) →
    EventGraph.EventCode (EventGraph.fieldLayout inputLayout outputLayout) (outputLayout event)
  reads_available : ∀ event field,
    field ∈ (nodes event).readFields →
      match field with
      | .inl _ => True
      | .inr producer => producer ∈ order.predecessors event
  payoffs : List (Player ×
    EventGraph.PublicExpr (EventGraph.fieldLayout inputLayout outputLayout) L.int)

namespace EventGraph

variable {Player : Type} {L : IExpr} [R : IExpr.ResultTypes L]
variable (graph : Vegas.EventGraph Player L)

abbrev EventId := Fin graph.order.eventCount
abbrev InputId := Fin graph.inputCount
abbrev Field := EventGraph.FieldId graph.inputCount graph.order.eventCount

/-- The graph's combined typed field layout. -/
def layout : graph.Field → EventGraph.EventField Player L :=
  EventGraph.fieldLayout graph.inputLayout graph.outputLayout

/-- Concrete initial values are supplied separately from the graph. -/
abbrev Inputs := (input : graph.InputId) → (graph.inputLayout input).Value

/-- A complete typed environment over both initial fields and event outputs. -/
abbrev Outcome := (field : graph.Field) → (graph.layout field).Value

/-- The prescribed action type at one event. Resolve actions retain the
original disclosure Boolean even when validation stores failure. -/
abbrev Action (event : graph.EventId) := (graph.nodes event).Action

/-- One completed event with its actual decision and newly public default. -/
structure Completion where
  event : graph.EventId
  decision : Option (graph.Action event)
  defaultEvent : Option Player

namespace Completion

@[simp] theorem event_mk (event : graph.EventId) (decision : Option (graph.Action event))
    (defaultEvent : Option Player) :
    (Completion.mk event decision defaultEvent : graph.Completion).event = event := rfl

end Completion

end EventGraph

end Vegas

namespace Vegas.EventGraph.Completion

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Complete an event, retaining only an actual strategic decision. Mechanical
completions record no new default, including subsequent failures of an excluded owner. -/
def fromDecision (event : graph.EventId) (decision : Option (graph.Action event))
    (value : (graph.outputLayout event).Value) : graph.Completion :=
  ⟨event, decision, decision.bind fun action => (graph.nodes event).defaultEvent action value⟩

/-- The public projection of an event completion contains no action material. -/
def publicEvent (completion : graph.Completion) : graph.EventId × Option Player :=
  (completion.event, completion.defaultEvent)

/-- The source-compatible public default history, derived from chronological completions. -/
def defaults (history : List graph.Completion) : DefaultHistory Player :=
  ⟨(history.map Completion.defaultEvent).reverse⟩

@[simp] theorem defaults_append (history : List graph.Completion)
    (completion : graph.Completion) :
    defaults (history ++ [completion]) = (defaults history).record completion.defaultEvent := by
  simp [defaults, DefaultHistory.record]

/-- Public defaults persist when another event completes. -/
theorem defaults_mono [DecidableEq Player]
    (history : List graph.Completion) (completion : graph.Completion) :
    (defaults history).defaulted ⊆ (defaults (history ++ [completion])).defaulted := by
  rw [defaults_append]
  exact DefaultHistory.defaulted_mono _ _

end Vegas.EventGraph.Completion
