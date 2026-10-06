/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

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

/-- At a completed service boundary, remembered completions refer only to
past events. The temporary shadow created by submission becomes such a past
completion at the immediately following protected inclusion. -/
def CompletedAt (memory : BindingShadow graph) (config : graph.Config) : Prop :=
  ∀ event, (memory.actions event).isSome ∨ (memory.values (.inr event)).isSome →
    event ∈ config.cut.completed

theorem completedAt_empty (config : graph.Config) :
    (empty : BindingShadow graph).CompletedAt config := by
  intro event present
  rcases present with present | present <;> cases present

theorem CompletedAt.rememberCandidate {memory : BindingShadow graph} {config : graph.Config}
    (past : memory.CompletedAt config) (slot : CandidateSlot graph)
    (value : CommitmentCandidate (Raw L)) :
    (memory.rememberCandidate slot value).CompletedAt config := past

theorem CompletedAt.complete {memory : BindingShadow graph} {config : graph.Config}
    (past : memory.CompletedAt config) (event : graph.EventId) (ready : config.cut.Ready event)
    (action : graph.Action event) (value : (graph.outputLayout event).Value) :
    memory.CompletedAt (config.complete event ready action value) := by
  intro query present
  rw [Config.complete_cut, EventOrder.Cut.mem_complete]
  exact Or.inr (past query present)

theorem CompletedAt.rememberCompletion {memory : BindingShadow graph} {config : graph.Config}
    (past : memory.CompletedAt config) (event : graph.EventId) (ready : config.cut.Ready event)
    (originalAction actualAction : graph.Action event)
    (originalValue actualValue : (graph.outputLayout event).Value) :
    (memory.rememberCompletion event originalAction originalValue).CompletedAt
      (config.complete event ready actualAction actualValue) := by
  classical
  intro query present
  rw [Config.complete_cut, EventOrder.Cut.mem_complete]
  by_cases same : query = event
  · exact Or.inl same
  · apply Or.inr
    apply past query
    simpa only [BindingShadow.rememberCompletion, Function.update_of_ne same,
      Function.update_of_ne (Sum.inr_injective.ne same)] using present

theorem CompletedAt.ready_none {memory : BindingShadow graph} {config : graph.Config}
    (past : memory.CompletedAt config) (event : graph.EventId) (ready : config.cut.Ready event) :
    memory.actions event = none ∧ memory.values (.inr event) = none := by
  constructor
  · cases stored : memory.actions event with
    | none => rfl
    | some action =>
        exact False.elim (ready.1 (past event (Or.inl (by simp only [stored]; rfl))))
  · cases stored : memory.values (.inr event) with
    | none => rfl
    | some value =>
        exact False.elim (ready.1 (past event (Or.inr (by simp only [stored]; rfl))))

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

omit [DecidableEq Player] in
private theorem complete_publicView (left right : State graph)
    (publicEq : left.publicView = right.publicView)
    (event : graph.EventId) (leftReady : left.config.cut.Ready event)
    (rightReady : right.config.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) :
    (left.complete event leftReady action value).publicView =
      (right.complete event rightReady action value).publicView := by
  classical
  have observations := congrArg PublicView.observation publicEq
  have orders := congrArg PublicObservation.completionOrder observations
  have cuts := cut_eq_of_completionOrder_eq left.config right.config orders
  have observed : graph.publicObserve (left.config.complete event leftReady action value) =
      graph.publicObserve (right.config.complete event rightReady action value) := by
    apply PublicObservation.ext graph
    · simpa only [State.publicView, publicObserve, Config.complete,
        List.map_append, List.map_cons, List.map_nil] using
        congrArg (fun order => order ++ [event]) orders
    · apply graph.publicStore_congr
      intro field visible
      rw [store_complete, store_complete]
      by_cases selected : field = .inr event
      · subst field
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne selected, Function.update_of_ne selected]
        have prior := congrFun (congrArg PublicObservation.store observations) field
        simpa only [State.publicView, publicObserve, publicStore_of_public, visible] using prior
  have clockEq := congrArg PublicView.clock publicEq
  have activatedEq := congrArg PublicView.activatedAt publicEq
  have acceptedEq := congrArg PublicView.accepted publicEq
  have nextActivated :
      State.refreshActivated (left.config.complete event leftReady action value)
          left.clock left.activatedAt =
        State.refreshActivated (right.config.complete event rightReady action value)
          right.clock right.activatedAt := by
    funext query
    simp only [State.refreshActivated, Config.complete_cut, cuts]
    rw [show left.clock = right.clock from clockEq,
      show left.activatedAt = right.activatedAt from activatedEq]
  unfold State.publicView State.complete
  congr 1

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
    event leftReady rightReady noValue noAction action value
  have nextPublic := complete_publicView original.application repaired.application frame.publicView
    event leftReady rightReady action value
  have nextObservation :
      (memory.shadow.view (app.observePlayer
        (repaired.application.complete event rightReady action value) owner)).observation =
      (app.observePlayer
        (original.application.complete event leftReady action value) owner).observation := by
    apply PlayerObservation.ext graph
    · exact (congrArg (fun view : PublicView graph => view.observation.completionOrder)
        nextPublic).symm
    · exact reconstructed.1
    · exact reconstructed.2
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
      action action value value (fun _ => rfl) (fun _ => rfl)
  · exact Config.bindingRefines_complete frame.successful event leftReady rightReady action action
      value value (EventField.BindingRefines.refl _ _)

/-- Public chance has an explicit common-draw coupling of the two actual
environment steps. Its support carries the full concrete frame, including the
reconstructed owner input, not just the opponents' separate marginal laws. -/
theorem sample_coupling (frame : Frame runtime leaks memory owner original repaired)
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
  have actual (execution : app.Execution)
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
    simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp]
    change (environmentStep runtime execution.application (.executeSample event)).map _ = _
    rw [applicationLaw, PMF.map_comp]
    rfl
  refine ⟨draw.map (fun value => (next original ready value, next repaired rightReady value)),
    ?_, ?_, ?_⟩
  · rw [PMF.map_comp]
    exact (actual original ready leftLaw).symm
  · rw [PMF.map_comp]
    exact (actual repaired rightReady rightLaw).symm
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

/-- The complete real clock-padding and expiry suffix is deterministic and
preserves the same execution-pair frame after an event has settled. This is
the actual existing service evaluator, for arbitrary response/network policies. -/
theorem completed_clock_tail (frame : Frame runtime leaks memory owner original repaired)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (scheduler : runtime.NetworkPolicy leaks) (event : graph.EventId)
    (completed : event ∈ original.application.config.cut.completed) (ticks : Nat) :
    ∃ left right,
      runtime.runInteractionPlan leaks players scheduler
        (List.replicate ticks .tick ++ [.expire event]) original = PMF.pure left ∧
      runtime.runInteractionPlan leaks players scheduler
        (List.replicate ticks .tick ++ [.expire event]) repaired = PMF.pure right ∧
      Frame runtime leaks memory owner left right := by
  let app := runtime.reactiveApplication leaks
  induction ticks generalizing original repaired with
  | zero =>
      let finish (execution : app.Execution) : app.Execution :=
        { execution with environmentRecall := execution.environmentRecall ++
          [⟨execution.observeEnvironment app, .application (.expire event)⟩] }
      have settled (execution : app.Execution)
          (done : event ∈ execution.application.config.cut.completed) :
          runtime.runInteractionPlan leaks players scheduler [.expire event] execution =
            PMF.pure (finish execution) := by
        have notReady : ¬ execution.application.config.cut.Ready event := fun ready => ready.1 done
        have unchanged : app.environment execution.application (.expire event) =
            PMF.pure execution.application :=
          runtime.environmentStep_expire_of_not_ready execution.application event notReady
        simp only [runInteractionPlan, interactionStep, interactionInstruction, PMF.pure_bind,
          ReactiveApplication.dispatch, ReactiveApplication.Command.actor?, PMF.bind_pure]
        change (execution.environmentStep app (.application (.expire event))).bind
          PMF.pure = _
        rw [PMF.bind_pure]
        change (((app.environment execution.application (.expire event)).map _).map _) = _
        rw [unchanged, PMF.pure_map, PMF.pure_map]
      have sameCut := cut_eq_of_completionOrder_eq original.application.config
        repaired.application.config
          (congrArg (fun view : PublicView graph => view.observation.completionOrder)
            frame.publicView)
      have rightDone : event ∈ repaired.application.config.cut.completed := sameCut ▸ completed
      refine ⟨finish original, finish repaired, settled original completed,
        settled repaired rightDone, ?_⟩
      exact { frame with
        service := by
          change original.environmentRecall ++ [_] = repaired.environmentRecall ++ [_]
          rw [frame.service, frame.environment] }
  | succ ticks ih =>
      let advance (execution : app.Execution) : app.Execution :=
        { execution with
          application := { execution.application with clock := execution.application.clock + 1 }
          environmentRecall := execution.environmentRecall ++
            [⟨execution.observeEnvironment app, .application .advanceClock⟩] }
      have tick (execution : app.Execution) :
          runtime.interactionStep leaks players scheduler .tick execution =
            PMF.pure (advance execution) := by
        simp only [interactionStep, interactionInstruction, PMF.pure_bind,
          ReactiveApplication.dispatch, ReactiveApplication.Command.actor?]
        change (execution.environmentStep app (.application .advanceClock)).bind PMF.pure = _
        rw [PMF.bind_pure]
        change ((PMF.pure { execution.application with
          clock := execution.application.clock + 1 }).map _).map _ = _
        rw [PMF.pure_map, PMF.pure_map]
      obtain ⟨left, right, leftLaw, rightLaw, coupled⟩ :=
        ih (original := advance original) (repaired := advance repaired)
          frame.advanceClock completed
      refine ⟨left, right, ?_, ?_, coupled⟩
      · rw [List.replicate_succ, List.cons_append, runInteractionPlan, tick, PMF.pure_bind]
        exact leftLaw
      · rw [List.replicate_succ, List.cons_append, runInteractionPlan, tick, PMF.pure_bind]
        exact rightLaw

end BindingMemory.Frame
end Vegas.EventGraphRuntime
