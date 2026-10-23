/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalShadowNormalization
import Vegas.Pending.EventCommandFrame

/-! # Original public chance laws under private binding shadows

PublicDist reads only publicData and publication fields. Private binding
repair therefore retains its exact chance law without any assumption about
the correlation of the original initialized inputs.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
private theorem sample_native_law (runtime : EventGraphRuntime graph) (state : State graph)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (payload : L.Ty) (law : PublicDist graph.layout payload)
    (outputEq : graph.outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .sample payload law)
    (node : nodeView graph event = .sample payload law outputEq codeEq)
    (draw : PMF (L.Val payload)) (evaluates : law.eval? state.config.store = some draw) :
    environmentStep runtime state (.executeSample event) = draw.map (fun value =>
      state.complete event ready (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
        (cast (congrArg EventField.Value outputEq.symm) value)) := by
  rw [environmentStep_executeSample_eq runtime state event ready payload law outputEq codeEq node,
    state.config.step_eq_map_of_code event ready outputEq (.sample payload law) codeEq PUnit.unit
      draw evaluates, PMF.map_comp]
  rfl

/-- Actual native sample laws commute with an owner-local binding shadow.
Neither a source-world independence law nor a compiler read premise is supplied. -/
theorem native_executeSample (memory : BindingShadow graph) (owner : Player)
    (owned : memory.OwnBindings owner) (runtime : EventGraphRuntime graph)
    (state : State graph) (event : graph.EventId) :
    environmentStep runtime (memory.native owner state) (.executeSample event) =
      (environmentStep runtime state (.executeSample event)).map (memory.native owner) := by
  classical
  by_cases ready : state.config.cut.Ready event
  · have originalReady : (memory.native owner state).config.cut.Ready event := ready
    cases node : nodeView graph event with
    | bind actor payload outputEq codeEq =>
        have acting : graph.actor? event = some actor :=
          (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
            (congrArg EventCode.actor codeEq)
        rw [environmentStep_executeSample_of_owned runtime state event actor acting,
          environmentStep_executeSample_of_owned runtime (memory.native owner state) event actor
            acting, PMF.pure_map]
    | resolve actor payload binding checks outputEq codeEq =>
        have acting : graph.actor? event = some actor :=
          (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
            (congrArg EventCode.actor codeEq)
        rw [environmentStep_executeSample_of_owned runtime state event actor acting,
          environmentStep_executeSample_of_owned runtime (memory.native owner state) event actor
            acting, PMF.pure_map]
    | sample payload law outputEq codeEq =>
        have available : (law.eval? state.config.store).isSome = true := by
          apply law.eval?_isSome
          intro field member
          apply state.config.read_available ready
          rw [← EventCode.readFields_cast outputEq (graph.nodes event), codeEq]
          exact member
        let draw := (law.eval? state.config.store).get available
        have evaluated : law.eval? state.config.store = some draw := (Option.some_get _).symm
        have publicEq : graph.publicStore (memory.native owner state).config.store =
            graph.publicStore state.config.store :=
          congrArg (fun view : PublicView graph => view.observation.store)
            (native_publicView owned state)
        have originalEval : law.eval? (memory.native owner state).config.store = some draw := by
          rw [← law.eval?_publicStore (memory.native owner state).config.store, publicEq,
            law.eval?_publicStore state.config.store]
          exact evaluated
        have visible : (graph.outputLayout event).IsPublic := by rw [outputEq]; trivial
        have noValue := owned.public_value_none (.inr event) visible
        have noAction := owned.public_action_none event visible
        rw [sample_native_law runtime state event ready payload law outputEq codeEq node draw
          evaluated, sample_native_law runtime (memory.native owner state) event originalReady
            payload law outputEq codeEq node draw originalEval, PMF.map_comp]
        apply congrArg (fun kernel => draw.map kernel)
        funext value
        exact (native_complete_unmodified memory owner state event ready noValue noAction _ _).symm
  · have originalReady : ¬ (memory.native owner state).config.cut.Ready event := ready
    rw [environmentStep_executeSample_of_not_ready runtime state event ready,
      environmentStep_executeSample_of_not_ready runtime (memory.native owner state) event
        originalReady, PMF.pure_map]

end Vegas.EventGraphRuntime.BindingShadow
