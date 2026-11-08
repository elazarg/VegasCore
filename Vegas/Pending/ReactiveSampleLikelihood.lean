/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveBindingLikelihood
import Vegas.Pending.EventSampleObservation

/-! # Public sampling preserves the focal traffic correspondence

The same public draw completes both actual states and records the real
environment command. Foreign private submission parameters need not agree.
The result is used with the source sample law, retaining correlations with
the original private source history.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- Coupling the public draw preserves the complete focal traffic readout,
including the scheduler's true pre-sample observation. -/
theorem bindingTraffic_sample_result
    (left right : ((reactiveApplication timeouts) leaks).Execution) (focal : Player)
    (same : (bindingTraffic timeouts) leaks focal left = (bindingTraffic timeouts) leaks focal
      right)
    (event : graph.EventId) (leftReady : left.application.config.cut.Ready event)
    (rightReady : right.application.config.cut.Ready event)
    (payload : L.Ty) (outputEq : graph.outputLayout event = .publicData payload)
    (value : L.Val payload) :
    let app := (reactiveApplication timeouts) leaks
    let after := fun (execution : app.Execution)
        (ready : execution.application.config.cut.Ready event) =>
      { execution with
        application := (execution.application.complete event ready
          (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
          (cast (congrArg EventField.Value outputEq.symm) value)).drain
        environmentRecall := execution.environmentRecall ++
          [⟨execution.observeEnvironment app, .application (.executeSample event)⟩] }
    (bindingTraffic timeouts) leaks focal (after left leftReady) =
      (bindingTraffic timeouts) leaks focal (after right rightReady) := by
  intro app after
  have networks := congrArg Prod.fst same
  have receipts := congrArg (fun data => data.2.1) same
  have environments := congrArg (fun data => data.2.2.1) same
  have recalled := congrArg (fun data => data.2.2.2.1) same
  have views := congrArg (fun data => data.2.2.2.2.1) same
  have publics := congrArg (fun data => data.2.2.2.2.2) same
  dsimp only [bindingTraffic] at networks receipts environments recalled views publics
  have environment : left.observeEnvironment app = right.observeEnvironment app := by
    change ReactiveApplication.EnvironmentView.mk left.network.publicView
      left.application.publicView left.receipts = _
    rw [networks, publics, receipts]
    rfl
  have completed := State.complete_playerView_congr left.application right.application focal
    publics (left.application.playerView_observation_eq right.application focal views)
    (congrArg PlayerView.candidates views)
    event leftReady rightReady
    (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
    (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
    (cast (congrArg EventField.Value outputEq.symm) value)
    (cast (congrArg EventField.Value outputEq.symm) value) (fun _ => rfl) (fun _ => rfl) (by
      cases codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) with
      | sample payload law =>
          rw [left.application.config.completion_defaultEvent_of_code event outputEq
            (.sample payload law) codeEq, right.application.config.completion_defaultEvent_of_code
              event outputEq (.sample payload law) codeEq]
          rfl)
  have complete := State.drain_playerView_congr _ _ focal completed
  change (bindingTraffic timeouts) leaks focal (after left leftReady) = _
  have completedPublic : (after left leftReady).application.publicView =
      (after right rightReady).application.publicView := congrArg PlayerView.publicView complete
  dsimp only [after] at completedPublic
  simp only [bindingTraffic, after]
  rw [networks, receipts, environments, environment, recalled, complete, completedPublic]

/-- Actual public chance uses a common law determined by public data. This
compares the genuine environment transition, with no independent noise kernel. -/
theorem bindingTraffic_sample
    (left right : ((reactiveApplication timeouts) leaks).Execution) (focal : Player)
    (same : (bindingTraffic timeouts) leaks focal left = (bindingTraffic timeouts) leaks focal
      right)
    (event : graph.EventId) (leftReady : left.application.config.cut.Ready event)
    (rightReady : right.application.config.cut.Ready event)
    (payload : L.Ty) (law : PublicDist graph.layout payload)
    (outputEq : graph.outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .sample payload law)
    (node : nodeView graph event = .sample payload law outputEq codeEq) :
    (left.environmentStep ((reactiveApplication timeouts) leaks)
      (.application (.executeSample event))).map ((bindingTraffic timeouts) leaks focal) =
    (right.environmentStep ((reactiveApplication timeouts) leaks)
      (.application (.executeSample event))).map ((bindingTraffic timeouts) leaks focal) := by
  let app := (reactiveApplication timeouts) leaks
  have publics := congrArg (fun data => data.2.2.2.2.2) same
  have stores : graph.publicStore left.application.config.store =
      graph.publicStore right.application.config.store :=
    congrArg (fun view : PublicView graph => view.observation.store) publics
  have laws : law.eval? left.application.config.store =
      law.eval? right.application.config.store := by
    rw [← law.eval?_publicStore left.application.config.store,
      ← law.eval?_publicStore right.application.config.store, stores]
  have available : (law.eval? left.application.config.store).isSome = true := by
    apply law.eval?_isSome
    intro field member
    apply left.application.config.read_available leftReady
    rw [← EventCode.readFields_cast outputEq (graph.nodes event), codeEq]
    exact member
  obtain ⟨draw, leftLaw⟩ := Option.isSome_iff_exists.mp available
  have rightLaw := laws.symm.trans leftLaw
  have sampleLaw (execution : app.Execution)
      (ready : execution.application.config.cut.Ready event)
      (evaluates : law.eval? execution.application.config.store = some draw) :
      environmentStep timeouts execution.application (.executeSample event) =
        draw.map (fun value => execution.application.complete event ready
          (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
          (cast (congrArg EventField.Value outputEq.symm) value)) := by
    rw [environmentStep_executeSample_eq timeouts execution.application event ready payload law
      outputEq codeEq node,
      execution.application.config.step_eq_map_of_code event ready outputEq (.sample payload law)
        codeEq PUnit.unit draw evaluates, PMF.map_comp]
    rfl
  simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp]
  change ((environmentStep timeouts left.application (.executeSample event)).map State.drain).map
      _ = ((environmentStep timeouts right.application (.executeSample event)).map
        State.drain).map _
  rw [sampleLaw left leftReady leftLaw, sampleLaw right rightReady rightLaw]
  simp only [PMF.map_comp]
  apply map_congr_on_support _
  intro value _
  exact (bindingTraffic_sample_result timeouts) leaks left right focal same event leftReady
    rightReady
    payload outputEq value

end Vegas.EventGraphRuntime
