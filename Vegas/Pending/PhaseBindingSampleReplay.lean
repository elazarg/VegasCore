/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingRejectedReplay

/-! # Actual common-draw chance kernels during directed phased repair -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

/-- One public chance completion before phase installation, retaining the
actual pre-command environment observation and the saved semantic checkpoint. -/
def rawSample (physical : (phaseApplication runtime leaks).Execution) (event : graph.EventId)
    (payload : L.Ty) (outputEq : graph.outputLayout event = .publicData payload)
    (ready : physical.application.current.native.config.cut.Ready event)
    (value : L.Val payload) : (phaseApplication runtime leaks).Execution :=
  { physical with
    application := { physical.application with
      current := { physical.application.current with
        native := physical.application.current.native.complete event ready
          (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
          (cast (congrArg EventField.Value outputEq.symm) value) } }
    environmentRecall := physical.environmentRecall ++
      [⟨physical.observeEnvironment (phaseApplication runtime leaks),
        .application (.executeSample event)⟩] }

/-- The real sample command law retains the exact public draw through
physical phase normalization. -/
theorem sample_environment_law (physical : (phaseApplication runtime leaks).Execution)
    (event : graph.EventId)
    (ready : physical.application.current.native.config.cut.Ready event)
    (payload : L.Ty) (law : PublicDist graph.layout payload)
    (outputEq : graph.outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .sample payload law)
    (node : nodeView graph event = .sample payload law outputEq codeEq)
    (allowed : physical.application.commandAllowed (.executeSample event) = true)
    (draw : PMF (L.Val payload))
    (evaluates : law.eval? physical.application.current.native.config.store = some draw) :
    physical.environmentStep (phaseApplication runtime leaks)
        (.application (.executeSample event)) =
      draw.map (fun value => PhaseRuntimeState.normalizeExecution runtime leaks
        (rawSample runtime leaks physical event payload outputEq ready value)) := by
  have applicationLaw : environmentStep runtime physical.application.current.native
      (.executeSample event) = draw.map (fun value =>
        physical.application.current.native.complete event ready
          (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
          (cast (congrArg EventField.Value outputEq.symm) value)) := by
    rw [environmentStep_executeSample_eq runtime physical.application.current.native event
      ready payload law outputEq codeEq node,
      physical.application.current.native.config.step_eq_map_of_code event ready outputEq
        (.sample payload law) codeEq PUnit.unit draw evaluates, PMF.map_comp]
    rfl
  simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp]
  change (physical.application.environment runtime (.executeSample event)).map _ = _
  rw [PhaseRuntimeState.environment]
  simp only [allowed, ↓reduceIte, applicationLaw, PMF.map_comp]
  rfl

namespace Frame

variable {runtime leaks}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- Public chance records no private shadow value, so the same realized draw
preserves the native frame and then both actual phase checkpoints. -/
theorem sample_value (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner) (event : graph.EventId)
    (payload : L.Ty) (outputEq : graph.outputLayout event = .publicData payload)
    (ready : original.application.current.native.config.cut.Ready event)
    (rightReady : repaired.application.current.native.config.cut.Ready event)
    (value : L.Val payload) :
    Frame runtime leaks memory owner
      (PhaseRuntimeState.normalizeExecution runtime leaks
        (rawSample runtime leaks original event payload outputEq ready value))
      (PhaseRuntimeState.normalizeExecution runtime leaks
        (rawSample runtime leaks repaired event payload outputEq rightReady value)) := by
  let nativeApp := runtime.reactiveApplication (nativeLeaks (graph := graph))
  let left := rawSample runtime leaks original event payload outputEq ready value
  let right := rawSample runtime leaks repaired event payload outputEq rightReady value
  have visible : (graph.outputLayout event).IsPublic := by rw [outputEq]; trivial
  have recorded := frame.live.recordEnvironment (.application (.executeSample event))
  have native := recorded.complete_unmodified event ready rightReady
    (onlyBindings.public_value_none (.inr event) visible)
    (onlyBindings.public_action_none event visible)
    (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
    (cast (congrArg EventField.Value outputEq.symm) value)
  rw [PhaseBindingRepair.observeEnvironment runtime leaks original,
    PhaseBindingRepair.observeEnvironment runtime leaks repaired] at native
  have live : BindingMemory.Frame runtime (nativeLeaks (graph := graph)) memory owner
      (execution runtime leaks left) (execution runtime leaks right) := by
    simpa only [left, right, rawSample, execution, List.map_append, List.map_cons, List.map_nil,
      environmentEntry, command] using native
  have savedLeft : (checkpoint runtime leaks left).application =
      (checkpoint runtime leaks original).application := rfl
  have savedRight : (checkpoint runtime leaks right).application =
      (checkpoint runtime leaks repaired).application := rfl
  have saved : BindingMemory.Frame runtime (nativeLeaks (graph := graph)) memory owner
      (checkpoint runtime leaks left) (checkpoint runtime leaks right) := by
    apply checkpointFrame live (checkpoint runtime leaks left).application
      (checkpoint runtime leaks right).application
    · rw [savedRight, savedLeft]
      exact congrArg ReactiveApplication.PlayerView.application frame.saved.observed
    · rw [savedLeft, savedRight]
      exact frame.saved.views
    · rw [savedLeft, savedRight]
      exact frame.saved.slots
    · rw [savedLeft, savedRight]
      exact frame.saved.successful
  have service : left.environmentRecall = right.environmentRecall := by
    change original.environmentRecall ++ [_] = repaired.environmentRecall ++ [_]
    rw [frame.service, frame.environment_input]
  have raw : Frame runtime leaks memory owner left right :=
    ⟨live, saved, frame.phases, frame.generation, frame.clearOriginal, frame.clearRepaired,
      frame.archiveOriginal, frame.archiveRepaired, frame.network, service, frame.foreignRecall⟩
  exact raw.normalize

/-- The complete phased chance kernels have a common-draw coupling. Its
marginals are the real application commands, including phase installation and
physical scheduler recall, and every supported pair carries both repair frames. -/
theorem sample_coupling (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (event : graph.EventId) (ready : original.application.current.native.config.cut.Ready event)
    (payload : L.Ty) (law : PublicDist graph.layout payload)
    (outputEq : graph.outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .sample payload law)
    (node : nodeView graph event = .sample payload law outputEq codeEq)
    (allowed : original.application.commandAllowed (.executeSample event) = true) :
    ∃ coupled : PMF ((phaseApplication runtime leaks).Execution ×
        (phaseApplication runtime leaks).Execution),
      coupled.map Prod.fst = original.environmentStep (phaseApplication runtime leaks)
          (.application (.executeSample event)) ∧
      coupled.map Prod.snd = repaired.environmentStep (phaseApplication runtime leaks)
          (.application (.executeSample event)) ∧
      ∀ pair ∈ coupled.support, Frame runtime leaks memory owner pair.1 pair.2 := by
  let app := phaseApplication runtime leaks
  have publicNative : original.application.current.native.publicView =
      repaired.application.current.native.publicView := frame.live.publicView
  have rightReady : repaired.application.current.native.config.cut.Ready event := by
    rw [← State.publicView_eventReady, ← publicNative, State.publicView_eventReady]
    exact ready
  have rightAllowed : repaired.application.commandAllowed (.executeSample event) = true := by
    change (repaired.application.phases.head?.any _ ) = true
    rw [← frame.phases]
    exact allowed
  have available : (law.eval? original.application.current.native.config.store).isSome = true := by
    apply law.eval?_isSome
    intro field member
    apply original.application.current.native.config.read_available ready
    rw [← EventCode.readFields_cast outputEq (graph.nodes event), codeEq]
    exact member
  let draw := (law.eval? original.application.current.native.config.store).get available
  have leftLaw : law.eval? original.application.current.native.config.store = some draw :=
    (Option.some_get _).symm
  have rightLaw : law.eval? repaired.application.current.native.config.store = some draw := by
    rw [← law.eval?_publicStore repaired.application.current.native.config.store,
      ← show graph.publicStore original.application.current.native.config.store =
          graph.publicStore repaired.application.current.native.config.store from
        congrArg (fun view : PublicView graph => view.observation.store) publicNative,
      law.eval?_publicStore original.application.current.native.config.store]
    exact leftLaw
  let next (physical : app.Execution)
      (ready : physical.application.current.native.config.cut.Ready event)
      (value : L.Val payload) :=
    PhaseRuntimeState.normalizeExecution runtime leaks
      (rawSample runtime leaks physical event payload outputEq ready value)
  refine ⟨draw.map (fun value => (next original ready value, next repaired rightReady value)),
    ?_, ?_, ?_⟩
  · rw [PMF.map_comp]
    exact (sample_environment_law runtime leaks original event ready payload law outputEq codeEq
      node
      allowed draw leftLaw).symm
  · rw [PMF.map_comp]
    exact (sample_environment_law runtime leaks repaired event rightReady payload law outputEq
      codeEq node
      rightAllowed draw rightLaw).symm
  · intro pair supported
    obtain ⟨value, _member, rfl⟩ := PMF.support_map .. ▸ supported
    exact frame.sample_value onlyBindings event payload outputEq ready rightReady value

end Frame

end Vegas.EventGraphRuntime.PhaseBindingRepair
