/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveBindingFrame
import Vegas.Pending.EventSampleObservation

/-! # Service constructors of the concrete binding-repair frame

Public chance and publication completions use the same result on both sides;
their original private bindings may differ. Clock steps change only the public
metadata already present in the runtime.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type}
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

namespace BindingShadow

theorem OwnBindings.input_value_none {memory : BindingShadow graph} {owner : Player}
    (onlyBindings : memory.OwnBindings owner) (input : graph.InputId) :
    memory.values (.inl input) = none := by
  cases stored : memory.values (.inl input) with
  | none => rfl
  | some value =>
      obtain ⟨event, payload, impossible, _⟩ := onlyBindings.1 (.inl input)
        (by simp only [stored]; rfl)
      cases impossible
end BindingShadow

variable [DecidableEq Player]

namespace BindingMemory.Frame

variable {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- The frame preserves all persistent setup values jointly, including private
parameters correlated across players. Repairs only replace fresh binding
outputs; they never rewrite the initialized environment. -/
theorem inputs (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner) :
    original.application.config.inputs = repaired.application.config.inputs := by
  funext input
  have seen (observer : Player) (visible : graph.fieldVisibleTo observer (.inl input)) :
      original.application.config.inputs input = repaired.application.config.inputs input := by
    apply Option.some.inj
    by_cases own : observer = owner
    · subst observer
      have stored := congrFun (congrArg
        (fun view : (runtime.reactiveApplication leaks).PlayerView =>
          view.application.observation.store) frame.observed) (.inl input)
      change memory.shadow.store (graph.playerObserve owner repaired.application.config).store
          (.inl input) = (graph.playerObserve owner original.application.config).store
            (.inl input) at stored
      simpa only [BindingShadow.store, playerObserve, playerStore_of_visible, visible,
        Config.store_input, Option.map_some, onlyBindings.input_value_none,
        Option.getD_none] using stored.symm
    · have stored := congrFun (congrArg
        (fun view : PlayerView graph => view.observation.store) (frame.views observer own))
          (.inl input)
      simpa only [State.playerView, playerObserve, playerStore_of_visible, visible,
        Config.store_input] using stored
  have observes : ∃ observer, graph.fieldVisibleTo observer (.inl input) := by
    cases layout : graph.inputLayout input with
    | publicData payload | publication payload =>
        refine ⟨owner, ?_⟩
        change (graph.inputLayout input).VisibleTo owner
        rw [layout]
        trivial
    | privateInput observer payload | binding observer payload =>
        refine ⟨observer, ?_⟩
        change (graph.inputLayout input).VisibleTo observer
        rw [layout]
        rfl
  obtain ⟨observer, visible⟩ := observes
  exact seen observer visible

theorem advanceClock (frame : Frame runtime leaks memory owner original repaired) :
    let app := runtime.reactiveApplication leaks
    Frame runtime leaks memory owner
      { original with
        application := { original.application with clock := original.application.clock + 1 }
        environmentRecall := original.environmentRecall ++
          [⟨original.observeEnvironment app, .application .advanceClock⟩] }
      { repaired with
        application := { repaired.application with clock := repaired.application.clock + 1 }
        environmentRecall := repaired.environmentRecall ++
          [⟨repaired.observeEnvironment app, .application .advanceClock⟩] } := by
  refine ⟨frame.past, ?_, frame.lengths, frame.network, ?_, ?_, frame.recall, frame.slots,
    frame.successful, frame.submissions⟩
  · exact congrArg (fun view : (runtime.reactiveApplication leaks).PlayerView =>
      { view with application := { view.application with publicView :=
        { view.application.publicView with clock := view.application.publicView.clock + 1 } } })
          frame.observed
  · rw [frame.service, frame.environment]
  · intro who different
    exact congrArg (fun view : PlayerView graph =>
      { view with publicView := { view.publicView with clock := view.publicView.clock + 1 } })
        (frame.views who different)

private theorem complete_publicView (left right : State graph)
    (publicEq : left.publicView = right.publicView)
    (event : graph.EventId) (leftReady : left.config.cut.Ready event)
    (rightReady : right.config.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) :
    (left.complete event leftReady action value).publicView =
      (right.complete event rightReady action value).publicView := by
  apply State.complete_publicView_congr left right publicEq event leftReady rightReady
  · intro _
    rfl
  · have defaults : left.config.defaulted = right.config.defaulted :=
      congrArg (fun view : PublicView graph => view.observation.defaulted) publicEq
    simp only [EventGraph.completion, Config.actualDecision, defaults]

/-- A completion outside the shadow is read from the real runtime on both
sides. This covers public results and other players' private bindings. -/
theorem complete_unmodified (frame : Frame runtime leaks memory owner original repaired)
    (event : graph.EventId) (leftReady : original.application.config.cut.Ready event)
    (rightReady : repaired.application.config.cut.Ready event)
    (noValue : memory.shadow.values (.inr event) = none)
    (noAction : memory.shadow.actions event = none)
    (action : graph.Action event) (value : (graph.outputLayout event).Value) :
    Frame runtime leaks memory owner
      { original with application := original.application.complete event leftReady action value }
      { repaired with
        application := repaired.application.complete event rightReady action value } := by
  let app := runtime.reactiveApplication leaks
  have application := congrArg ReactiveApplication.PlayerView.application frame.observed
  have reconstructed := memory.shadow.complete_unmodified_observation owner
    original.application.config repaired.application.config
    (congrArg (fun view : PlayerView graph => view.observation.store) application)
    (congrArg (fun view : PlayerView graph => view.observation.ownActions) application)
    (congrArg (fun view : PublicView graph => view.observation.defaulted) frame.publicView)
    event leftReady rightReady noValue noAction action value
  have nextPublic := complete_publicView original.application repaired.application frame.publicView
    event leftReady rightReady action value
  have nextObservation :
      (memory.shadow.view (app.observePlayer
        (repaired.application.complete event rightReady action value) owner)).observation =
      (app.observePlayer
        (original.application.complete event leftReady action value) owner).observation := by
    apply EventPlayerObservation.ext
    · exact (congrArg (fun view : PublicView graph => view.observation.completionOrder)
        nextPublic).symm
    · exact reconstructed.1
    · exact reconstructed.2
    · exact (congrArg (fun view : PublicView graph => view.observation.defaults) nextPublic).symm
  have nextApplication : memory.shadow.view (app.observePlayer
      (repaired.application.complete event rightReady action value) owner) =
        app.observePlayer (original.application.complete event leftReady action value) owner := by
    exact congr (congr (congrArg (PlayerView.mk owner) nextPublic.symm) nextObservation)
      (congrArg PlayerView.candidates application)
  refine ⟨frame.past, ?_, frame.lengths, frame.network, frame.service, ?_,
    frame.recall, frame.slots, ?_, frame.submissions⟩
  · change (⟨repaired.network.observe owner, memory.shadow.view (app.observePlayer
      (repaired.application.complete event rightReady action value) owner),
        repaired.receipts⟩ : app.PlayerView) =
      ⟨original.network.observe owner, app.observePlayer
        (original.application.complete event leftReady action value) owner, original.receipts⟩
    exact congr (congr (congrArg (ReactiveApplication.PlayerView.mk (app := app))
      (congrArg (fun network => network.observe owner) frame.network.symm)) nextApplication)
        frame.receipts.symm
  · intro who different
    exact State.complete_playerView_congr original.application repaired.application who
      frame.publicView
      (original.application.playerView_observation_eq repaired.application who
        (frame.views who different))
      (congrArg PlayerView.candidates (frame.views who different)) event leftReady rightReady
      action action value value (fun _ => rfl) (fun _ => rfl) (by
        have defaults : original.application.config.defaulted =
            repaired.application.config.defaulted :=
          congrArg (fun view : PublicView graph => view.observation.defaulted) frame.publicView
        simp only [EventGraph.completion, Config.actualDecision, defaults])
  · exact Config.bindingRefines_complete frame.successful event leftReady rightReady action action
      value value (EventField.BindingRefines.refl _ _)

/-- Public chance has an explicit common-draw coupling of the two actual
environment steps. Its support carries the full concrete frame, including the
reconstructed owner input, not just the opponents' separate marginal laws. -/
theorem sample_coupling (frame : Frame runtime leaks memory owner original repaired)
    (clear : original.application.config.defaulted = ∅)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (event : graph.EventId) (ready : original.application.config.cut.Ready event)
    (payload : L.Ty) (law : PublicDist graph.layout payload)
    (outputEq : graph.outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .sample payload law)
    (node : nodeView graph event = .sample payload law outputEq codeEq) :
    ∃ coupled : PMF ((runtime.reactiveApplication leaks).Execution ×
        (runtime.reactiveApplication leaks).Execution),
      coupled.map Prod.fst = original.environmentStep (runtime.reactiveApplication leaks)
          (.application (.executeSample event)) ∧
      coupled.map Prod.snd = repaired.environmentStep (runtime.reactiveApplication leaks)
          (.application (.executeSample event)) ∧
      ∀ pair ∈ coupled.support, Frame runtime leaks memory owner pair.1 pair.2 := by
  let app := runtime.reactiveApplication leaks
  have rightClear : repaired.application.config.defaulted = ∅ :=
    (congrArg (fun view : PublicView graph => view.observation.defaulted)
      frame.publicView).symm.trans clear
  have ownerless : (graph.nodes event).actor = none := by
    rw [← EventCode.actor_cast outputEq (graph.nodes event), codeEq]
    rfl
  have rightReady : repaired.application.config.cut.Ready event := by
    rw [← State.publicView_eventReady, ← frame.publicView, State.publicView_eventReady]
    exact ready
  have available : (law.eval? original.application.config.store).isSome = true := by
    apply law.eval?_isSome
    intro field member
    apply original.application.config.read_available ready
    rw [← EventCode.readFields_cast outputEq (graph.nodes event), codeEq]
    exact member
  let draw := (law.eval? original.application.config.store).get available
  have leftLaw : law.eval? original.application.config.store = some draw :=
    (Option.some_get _).symm
  have rightLaw : law.eval? repaired.application.config.store = some draw := by
    rw [← law.eval?_publicStore repaired.application.config.store,
      ← show graph.publicStore original.application.config.store =
          graph.publicStore repaired.application.config.store from
        congrArg (fun view : PublicView graph => view.observation.store) frame.publicView,
      law.eval?_publicStore original.application.config.store]
    exact leftLaw
  let next (execution : app.Execution) (ready : execution.application.config.cut.Ready event)
      (value : L.Val payload) : app.Execution :=
    { execution with
      application := execution.application.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
        (cast (congrArg EventField.Value outputEq.symm) value)
      environmentRecall := execution.environmentRecall ++
        [⟨execution.observeEnvironment app, .application (.executeSample event)⟩] }
  have actual (execution : app.Execution) (empty : execution.application.config.defaulted = ∅)
      (ready : execution.application.config.cut.Ready event)
      (evaluates : law.eval? execution.application.config.store = some draw) :
      execution.environmentStep app (.application (.executeSample event)) =
        draw.map (next execution ready) := by
    have applicationLaw : environmentStep runtime execution.application (.executeSample event) =
        draw.map (fun value => execution.application.complete event ready
          (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
          (cast (congrArg EventField.Value outputEq.symm) value)) := by
      rw [environmentStep_executeSample_eq runtime execution.application event ready payload
        law outputEq codeEq node, execution.application.config.step_eq_map_of_code event ready
          outputEq (.sample payload law) codeEq PUnit.unit draw evaluates, PMF.map_comp]
      rfl
    have nativeLaw : app.environment execution.application (.executeSample event) =
        draw.map (fun value => execution.application.complete event ready
          (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
          (cast (congrArg EventField.Value outputEq.symm) value)) := by
      change (environmentStep runtime execution.application (.executeSample event)).map
        State.drain = _
      rw [applicationLaw, PMF.map_comp]
      apply congrArg draw.map
      funext value
      apply State.drain_eq_of_empty
      change (execution.application.config.complete event ready _ _).defaults.defaulted = ∅
      rw [Config.complete_defaults]
      have silent : execution.application.config.actualDecision event
          (cast (congrArg EventField.Action outputEq.symm) PUnit.unit) = none := by
        simp only [Config.actualDecision, EventCode.actualDecision, ownerless]
      rw [silent]
      exact empty
    simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp]
    change (app.environment execution.application (.executeSample event)).map _ = _
    rw [nativeLaw, PMF.map_comp]
    rfl
  refine ⟨draw.map (fun value => (next original ready value, next repaired rightReady value)),
    ?_, ?_, ?_⟩
  · rw [PMF.map_comp]
    exact (actual original clear ready leftLaw).symm
  · rw [PMF.map_comp]
    exact (actual repaired rightClear rightReady rightLaw).symm
  · intro pair supported
    obtain ⟨value, _, rfl⟩ := PMF.support_map .. ▸ supported
    have visible : (graph.outputLayout event).IsPublic := by rw [outputEq]; trivial
    have completed := frame.complete_unmodified event ready rightReady
      (onlyBindings.public_value_none (.inr event) visible)
      (onlyBindings.public_action_none event visible)
      (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
      (cast (congrArg EventField.Value outputEq.symm) value)
    exact { completed with
      service := by
        change original.environmentRecall ++ [_] = repaired.environmentRecall ++ [_]
        rw [frame.service, frame.environment] }

end BindingMemory.Frame
end Vegas.EventGraphRuntime
