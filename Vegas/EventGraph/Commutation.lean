/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Execution

/-! # Local commutation of independent ready events

Two distinct events that are ready at the same cut cannot read one another's
outputs. Consequently, fixing both event actions makes their local semantic
effects commute after chronological history is projected away. This file does
not claim scheduler- or policy-level schedule invariance.
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

/-- Completing an event is one typed update of the combined partial store. -/
theorem store_complete (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) :
    (config.complete event ready action value).store =
      Function.update config.store (.inr event) (some value) := by
  funext field
  cases field with
  | inl input =>
      simp [Config.store, Function.update]
      rfl
  | inr query =>
      by_cases same : query = event
      · subst query
        simp [Config.store, Config.complete, Function.update]
      · simp [Config.store, Config.complete, Function.update, same]

private def outputLaw (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) (action : graph.Action event) :
    FinDist (graph.outputLayout event).Value :=
  ((graph.nodes event).eval? action config.store).get
    (EventCode.eval?_isSome_of_reads (graph.nodes event) action config.store
      (fun _ read => config.read_available ready read))

private theorem outputLaw_after_complete {config : graph.Config}
    {completed reader : graph.EventId}
    (completedReady : config.cut.Ready completed)
    (readerReady : config.cut.Ready reader)
    (different : completed ≠ reader)
    (completedAction : graph.Action completed)
    (value : (graph.outputLayout completed).Value)
    (readerAction : graph.Action reader) :
    outputLaw (config.complete completed completedReady completedAction value) reader
        (readerReady.after_complete completedReady different.symm) readerAction =
      outputLaw config reader readerReady readerAction := by
  have evalEq := eval?_after_complete completedReady readerReady completedAction value
    readerAction
  have present := EventCode.eval?_isSome_of_reads (graph.nodes reader) readerAction
    (config.complete completed completedReady completedAction value).store
    (fun _ read => (config.complete completed completedReady completedAction value).read_available
      (readerReady.after_complete completedReady different.symm) read)
  cases hleft : (graph.nodes reader).eval? readerAction
      (config.complete completed completedReady completedAction value).store with
  | none => simp [hleft] at present
  | some law =>
      rw [hleft] at evalEq
      have hright : (graph.nodes reader).eval? readerAction config.store = some law :=
        evalEq.symm
      simp [outputLaw, hleft, hright]

private theorem step_eq_outputLaw_map (config : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event)
    (action : graph.Action event) :
    config.step event ready action =
      (outputLaw config event ready action).map
        (config.complete event ready action) := rfl

private theorem map_store_step (config : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event)
    (action : graph.Action event) :
    (config.step event ready action).map Config.store =
      (outputLaw config event ready action).map fun value =>
        Function.update config.store (.inr event) (some value) := by
  rw [step_eq_outputLaw_map, FinDist.map_comp]
  apply congrArg (fun observable =>
    FinDist.map observable (outputLaw config event ready action))
  funext value
  exact store_complete config event ready action value

/-- Execute two fixed actions in sequence, using support evidence only to
transport readiness through the first actual `Config.step`. -/
def stepThen (config : graph.Config) (first second : graph.EventId)
    (firstReady : config.cut.Ready first) (secondReady : config.cut.Ready second)
    (different : first ≠ second) (firstAction : graph.Action first)
    (secondAction : graph.Action second) : FinDist graph.Config :=
  (config.step first firstReady firstAction).bindOnSupport fun afterFirst member =>
    afterFirst.step second (by
      rw [config.step_cut first firstReady firstAction afterFirst member]
      exact secondReady.after_complete firstReady different.symm) secondAction

private theorem stepThen_map_store (config : graph.Config) (first second : graph.EventId)
    (firstReady : config.cut.Ready first) (secondReady : config.cut.Ready second)
    (different : first ≠ second) (firstAction : graph.Action first)
    (secondAction : graph.Action second) :
    (stepThen config first second firstReady secondReady different
      firstAction secondAction).map Config.store =
    (outputLaw config first firstReady firstAction).bind fun firstValue =>
      (outputLaw config second secondReady secondAction).map fun secondValue =>
        ((config.complete first firstReady firstAction firstValue).complete second
          (secondReady.after_complete firstReady different.symm)
          secondAction secondValue).store := by
  unfold stepThen
  rw [FinDist.map_bindOnSupport]
  rw [FinDist.bindOnSupport_eq_bind_of_eq_on_support (g := fun (afterFirst : graph.Config) =>
    (outputLaw config second secondReady secondAction).map fun secondValue =>
      Function.update afterFirst.store (.inr second)
        (show Option (graph.layout (.inr second)).Value from some secondValue))]
  · rw [step_eq_outputLaw_map, FinDist.bind_map]
    apply FinDist.bind_congr
    intro firstValue _
    apply congrArg (fun observable =>
      FinDist.map observable (outputLaw config second secondReady secondAction))
    funext secondValue
    exact (store_complete
      (config.complete first firstReady firstAction firstValue) second
      (secondReady.after_complete firstReady different.symm)
      secondAction secondValue).symm
  · intro afterFirst member
    rw [step_eq_outputLaw_map, FinDist.support_map] at member
    obtain ⟨firstValue, _, rfl⟩ := member
    rw [map_store_step]
    rw [outputLaw_after_complete firstReady secondReady different firstAction firstValue
      secondAction]

/-- Fixed actions at two distinct simultaneously ready events commute after
chronological history is projected away to the typed partial store. -/
theorem stepThen_map_store_comm (config : graph.Config)
    (left right : graph.EventId)
    (leftReady : config.cut.Ready left) (rightReady : config.cut.Ready right)
    (different : left ≠ right)
    (leftAction : graph.Action left) (rightAction : graph.Action right) :
    (stepThen config left right leftReady rightReady different
      leftAction rightAction).map Config.store =
    (stepThen config right left rightReady leftReady different.symm
      rightAction leftAction).map Config.store := by
  rw [stepThen_map_store, stepThen_map_store]
  simp only [FinDist.map_eq_bind]
  rw [FinDist.bind_comm]
  apply FinDist.bind_congr
  intro rightValue _
  apply FinDist.bind_congr
  intro leftValue _
  congr 1
  exact store_complete_comm leftReady rightReady different leftAction rightAction
    leftValue rightValue

end Vegas.EventGraph
