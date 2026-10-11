/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveDeviationRecall
import Vegas.Pending.ReactiveOriginalInclusionStability

/-! # Accepted raw focal calls retain actual source history -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- An accepted focal envelope appends its actual graph action to reconstructed
source history. Earlier foreign intentions remain fixed by actual trace receipt
invariants; the focal player needs no prescribed policy or sampled memory. -/
theorem originalConfig_include_focal_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (memories : Player → List (Option graph.Completion)) (focal : Player)
    (empty : memories focal = []) (event : graph.EventId)
    (actor : graph.actor? event = some focal)
    (message : Message Player (WitnessedPacket graph))
    (named : message.payload.call.event? graph = some event) (after : State graph)
    (found : control.execution.network.lookup message.id = some message)
    (accepted : (runtime.reactiveApplication leaks).handle control.execution.application message =
      some after) :
    ∃ (ready : control.execution.application.config.cut.Ready event) (action : graph.Action event),
      after.config ∈ (control.execution.application.config.step event ready action).support ∧
      (runtime.originalConfig leaks
        (control.execution.includePending (runtime.reactiveApplication leaks) message.id)
        memories).history =
          (runtime.originalConfig leaks control.execution memories).history ++
            [⟨event, action⟩] := by
  obtain ⟨address, addressed, ready, action, supported⟩ := handle_config_mem_step runtime
    control.execution.application after ⟨message.id, message.payload.call⟩
      (reactiveHandle_call accepted)
  have same : address = event := Option.some.inj (addressed.symm.trans named)
  subst address
  refine ⟨ready, action, supported, ?_⟩
  let next := control.execution.includePending (runtime.reactiveApplication leaks) message.id
  have included : next.application.config = after.config := by
    simp only [next, ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, accepted, Option.getD_some]
  have history : after.config.history =
      control.execution.application.config.history ++ [⟨event, action⟩] :=
    control.execution.application.config.step_history event ready action after.config supported
  change next.application.config.history.map (runtime.originalCompletion leaks next memories) = _
  rw [included, history, List.map_append, List.map_singleton]
  have retained : ∀ completion ∈ control.execution.application.config.history,
      runtime.originalCompletion leaks next memories completion =
        runtime.originalCompletion leaks control.execution memories completion := by
    intro completion member
    unfold originalCompletion
    cases owns : graph.actor? completion.event with
    | none => rfl
    | some owner =>
        dsimp only
        exact runtime.reactiveOriginal_include_completed_history leaks inputs horizon scheduler
          control trace owner (memories owner) message.id completion
          ((control.execution.application.config.history_exact completion.event).mp
            (List.mem_map.mpr ⟨completion, member, rfl⟩))
  have previous := List.map_congr_left retained
  have current : runtime.originalCompletion leaks next memories ⟨event, action⟩ =
      ⟨event, action⟩ := by
    simp only [originalCompletion, actor, empty]
    cases node : nodeView graph event <;> simp [reactiveOriginal, node]
  rw [previous, current]
  rfl

/-- An actual accepted focal envelope performs the same full graph completion
in the physical and reconstructed configurations. Its action and value are
extracted from the native handler, while earlier foreign recall is retained. -/
theorem originalConfig_include_focal_eq_complete (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (memories : Player → List (Option graph.Completion)) (focal : Player)
    (empty : memories focal = []) (event : graph.EventId)
    (actor : graph.actor? event = some focal)
    (message : Message Player (WitnessedPacket graph))
    (named : message.payload.call.event? graph = some event) (after : State graph)
    (found : control.execution.network.lookup message.id = some message)
    (accepted : (runtime.reactiveApplication leaks).handle control.execution.application message =
      some after) :
    ∃ (ready : control.execution.application.config.cut.Ready event) (action : graph.Action event)
      (value : (graph.outputLayout event).Value),
      after.config = control.execution.application.config.complete event ready action value ∧
      (runtime.originalConfig leaks
        (control.execution.includePending (runtime.reactiveApplication leaks) message.id)
        memories) =
          (runtime.originalConfig leaks control.execution memories).complete
            event ready action value := by
  obtain ⟨ready, action, supported, history⟩ := runtime.originalConfig_include_focal_history
    leaks inputs horizon scheduler control trace memories focal empty event actor message named
      after found accepted
  rw [Config.step, PMF.support_map] at supported
  obtain ⟨value, _, produced⟩ := supported
  refine ⟨ready, action, value, produced.symm, ?_⟩
  let next := control.execution.includePending (runtime.reactiveApplication leaks) message.id
  have included : next.application.config = after.config := by
    simp only [next, ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, accepted, Option.getD_some]
  have configEq := included.trans produced.symm
  apply Config.eq_of_fields
  · change next.application.config.inputs = control.execution.application.config.inputs
    rw [configEq]
    rfl
  · change next.application.config.cut =
      (control.execution.application.config.cut.complete event ready)
    rw [configEq]
    rfl
  · change next.application.config.outputs =
      (control.execution.application.config.complete event ready action value).outputs
    rw [configEq]
  · exact history

end Vegas.EventGraphRuntime
