/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveBindingRejectedInclusion
import Vegas.Pending.AttemptNamespace
import Vegas.Pending.ExclusionApplication
import Vegas.Pending.ExclusionCompletion
import Vegas.Pending.PhaseApplication
import Vegas.Pending.PhaseBindingInertResponse

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

end Frame

end Vegas.EventGraphRuntime.PhaseBindingRepair
