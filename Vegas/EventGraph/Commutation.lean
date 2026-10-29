/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.Execution

/-! # Local commutation of independent ready events

Two distinct events that are ready at the same cut cannot read one another's
outputs. Their evaluator footprints and typed output writes therefore remain independent.
The actual executor also carries absorbing defaults; no general law commuting
its completed decisions is asserted.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- A ready event cannot read the output of another simultaneously ready
event: every event-output read must name an already completed predecessor. -/
theorem output_not_mem_reads_of_ready {config : graph.Config}
    {reader writer : graph.EventId} (readerReady : config.cut.Ready reader)
    (writerReady : config.cut.Ready writer) :
    (.inr writer : graph.Field) ∉ (graph.nodes reader).readFields := by
  intro read
  exact writerReady.1 (readerReady.2
    (graph.reads_available reader (.inr writer) read))

variable [DecidableEq Player]

/-- Completing one of two simultaneously ready events does not change any
field in the other event's evaluator footprint. -/
theorem store_agreeOn_after_complete {config : graph.Config}
    {completed reader : graph.EventId}
    (completedReady : config.cut.Ready completed)
    (readerReady : config.cut.Ready reader)
    (action : graph.Action completed)
    (value : (graph.outputLayout completed).Value) :
    Store.AgreeOn config.store
      (config.complete completed completedReady action value).store
      (graph.nodes reader).readFields := by
  intro field read
  cases field with
  | inl input => rfl
  | inr producer =>
      have producerNe : producer ≠ completed := by
        intro same
        subst producer
        exact output_not_mem_reads_of_ready readerReady completedReady read
      change config.outputs producer =
        (config.complete completed completedReady action value).outputs producer
      exact (config.complete_output_of_ne completed producer completedReady action value
        producerNe).symm

/-- The other ready node's output law is unchanged after one event completes. -/
theorem eval?_after_complete {config : graph.Config}
    {completed reader : graph.EventId}
    (completedReady : config.cut.Ready completed)
    (readerReady : config.cut.Ready reader)
    (completedAction : graph.Action completed)
    (value : (graph.outputLayout completed).Value)
    (readerAction : graph.Action reader) :
    (graph.nodes reader).eval? readerAction
        (config.complete completed completedReady completedAction value).store =
      (graph.nodes reader).eval? readerAction config.store := by
  exact EventCode.eval?_congr (graph.nodes reader) readerAction _ _
    fun field read =>
      (store_agreeOn_after_complete completedReady readerReady
        completedAction value field read).symm

/-- Writing two distinct event outputs commutes after projecting a
configuration to its typed partial store. -/
theorem store_complete_comm {config : graph.Config} {left right : graph.EventId}
    (leftReady : config.cut.Ready left) (rightReady : config.cut.Ready right)
    (different : left ≠ right)
    (leftAction : graph.Action left) (rightAction : graph.Action right)
    (leftValue : (graph.outputLayout left).Value)
    (rightValue : (graph.outputLayout right).Value) :
    ((config.complete left leftReady leftAction leftValue).complete right
      (rightReady.after_complete leftReady different.symm) rightAction rightValue).store =
    ((config.complete right rightReady rightAction rightValue).complete left
      (leftReady.after_complete rightReady different) leftAction leftValue).store := by
  funext field
  cases field with
  | inl input => rfl
  | inr event =>
      by_cases eventLeft : event = left
      · subst event
        simp [Config.store, Config.complete, Function.update, different]
      · by_cases eventRight : event = right
        · subst event
          simp [Config.store, Config.complete, Function.update, different.symm]
        · simp [Config.store, Config.complete, Function.update, eventLeft, eventRight]


/-- Execute two fixed actions in sequence, using support evidence only to
transport readiness through the first actual `Config.step`. -/
def stepThen (config : graph.Config) (first second : graph.EventId)
    (firstReady : config.cut.Ready first) (secondReady : config.cut.Ready second)
    (different : first ≠ second) (firstAction : graph.Action first)
    (secondAction : graph.Action second) : PMF graph.Config :=
  (config.step first firstReady firstAction).bindOnSupport fun afterFirst member =>
    afterFirst.step second (by
      rw [config.step_cut first firstReady firstAction afterFirst member]
      exact secondReady.after_complete firstReady different.symm) secondAction

end Vegas.EventGraph
