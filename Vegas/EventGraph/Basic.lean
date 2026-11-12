module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.Order
public import Vegas.EventGraph.Code
public import Vegas.Foundation.DefaultHistory

@[expose] public section

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

/-- A completed event's data depends only on its immutable output layout. -/
structure EventCompletion {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
    {eventCount : Nat} (outputs : Fin eventCount → EventGraph.EventField Player L) where
  event : Fin eventCount
  decision : Option (EventGraph.EventField.Action (outputs event))
  defaultEvent : Option Player

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
abbrev Action (event : graph.EventId) := EventField.Action (graph.outputLayout event)

/-- Completed-event data uses the graph's immutable output layout. -/
abbrev Completion := EventCompletion graph.outputLayout

end EventGraph

end Vegas

namespace Vegas.EventGraph

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]

/-- Complete an event, retaining an actual strategic decision and its public default. -/
def completion (graph : Vegas.EventGraph Player L) (event : graph.EventId)
    (decision : Option (graph.Action event)) (value : (graph.outputLayout event).Value) :
    graph.Completion :=
  ⟨event, decision, decision.bind fun action => (graph.nodes event).defaultEvent action value⟩

end Vegas.EventGraph

namespace Vegas.EventCompletion

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L] {eventCount : Nat}
  {outputs : Fin eventCount → EventGraph.EventField Player L}

@[simp] theorem event_mk (event : Fin eventCount)
    (decision : Option (EventGraph.EventField.Action (outputs event)))
    (defaultEvent : Option Player) :
    (EventCompletion.mk event decision defaultEvent : EventCompletion outputs).event = event := rfl

/-- The public projection of an event completion contains no action material. -/
def publicEvent (completion : EventCompletion outputs) : Fin eventCount × Option Player :=
  (completion.event, completion.defaultEvent)

/-- The public default history is derived from chronological completions. -/
def defaults (history : List (EventCompletion outputs)) : DefaultHistory Player :=
  ⟨(history.map EventCompletion.defaultEvent).reverse⟩

@[simp] theorem defaults_append (history : List (EventCompletion outputs))
    (completion : EventCompletion outputs) :
    defaults (history ++ [completion]) = (defaults history).record completion.defaultEvent := by
  simp [defaults, DefaultHistory.record]

/-- Public defaults persist when another event completes. -/
theorem defaults_mono [DecidableEq Player] (history : List (EventCompletion outputs))
    (completion : EventCompletion outputs) :
    (defaults history).defaulted ⊆ (defaults (history ++ [completion])).defaulted := by
  rw [defaults_append]
  exact DefaultHistory.defaulted_mono _ _

end Vegas.EventCompletion
