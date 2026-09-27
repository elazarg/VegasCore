/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveContinuationObservation

/-! # Public chance under hidden binding repair

Public distributions read only public fields. Equal public observations give
one common sampling law, whose shared draws preserve opponents' views jointly.
-/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
theorem PublicRead.field_isPublic {payload : L.Ty}
    (read : PublicRead graph.layout payload) : graph.fieldPublic read.field := by
  cases read with
  | publicData ref | publication ref =>
      change (graph.layout ref.field).IsPublic
      rw [ref.layout_eq]
      trivial

omit [DecidableEq Player] in
/-- Conservative dependency footprints do not expose otherwise unused hidden
fields to a public distribution. -/
theorem PublicDist.eval?_publicStore {payload : L.Ty}
    (law : PublicDist graph.layout payload) (store : Store graph.layout) :
    law.eval? (graph.publicStore store) = law.eval? store := by
  apply law.eval?_congr_reads
  intro name input ref _
  exact PublicRead.get?_congr (law.reads ref) _ _
    (graph.publicStore_of_public store _ (law.reads ref).field_isPublic)

end Vegas.EventGraph

namespace Vegas.EventGraphRuntime

open EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)

omit [DecidableEq Player] in
private theorem sample_available
    (state : State graph) (event : graph.EventId) (ready : state.config.cut.Ready event)
    (payload : L.Ty) (law : PublicDist graph.layout payload)
    (outputEq : graph.outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .sample payload law) :
    (law.eval? state.config.store).isSome = true := by
  apply law.eval?_isSome
  intro field member
  apply state.config.read_available ready
  rw [← EventCode.readFields_cast outputEq (graph.nodes event), codeEq]
  exact member

omit [DecidableEq Player] in
private theorem sample_eq_map
    (state : State graph) (event : graph.EventId) (ready : state.config.cut.Ready event)
    (payload : L.Ty) (law : PublicDist graph.layout payload)
    (outputEq : graph.outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .sample payload law)
    (viewEq : nodeView graph event = .sample payload law outputEq codeEq)
    (draw : FinDist (L.Val payload)) (evaluates : law.eval? state.config.store = some draw) :
    environmentStep runtime state (.executeSample event) = draw.map (fun value =>
      state.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
        (cast (congrArg EventField.Value outputEq.symm) value)) := by
  rw [environmentStep_executeSample_eq runtime state event ready payload law outputEq codeEq viewEq,
    state.config.step_eq_map_of_code event ready outputEq (.sample payload law) codeEq
      PUnit.unit draw evaluates, FinDist.map_comp]
  rfl

/-- A ready public chance event is coupled by the same sampled value. The
complete vector of foreign observations is preserved, even for correlated
private inputs and different hidden-owner candidate tables. -/
theorem environmentStep_sample_hidden_congr
    (left right : State graph) (hidden : Player) (event : graph.EventId)
    (publicEq : left.publicView = right.publicView)
    (views : ∀ who, who ≠ hidden → left.playerView who = right.playerView who)
    (leftReady : left.config.cut.Ready event) (rightReady : right.config.cut.Ready event)
    (payload : L.Ty) (law : PublicDist graph.layout payload)
    (outputEq : graph.outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .sample payload law)
    (viewEq : nodeView graph event = .sample payload law outputEq codeEq) :
    let readout := fun state : State graph => fun who =>
      if who = hidden then none else some (state.playerView who)
    (environmentStep runtime left (.executeSample event)).map readout =
      (environmentStep runtime right (.executeSample event)).map readout := by
  have stores : graph.publicStore left.config.store = graph.publicStore right.config.store :=
    congrArg (fun view : PublicView graph => view.observation.store) publicEq
  have laws : law.eval? left.config.store = law.eval? right.config.store := by
    rw [← law.eval?_publicStore left.config.store, ← law.eval?_publicStore right.config.store,
      stores]
  let draw := (law.eval? left.config.store).get
    (sample_available left event leftReady payload law outputEq codeEq)
  have leftLaw : law.eval? left.config.store = some draw := (Option.some_get _).symm
  have rightLaw : law.eval? right.config.store = some draw := laws.symm.trans leftLaw
  rw [sample_eq_map runtime left event leftReady payload law outputEq codeEq viewEq draw leftLaw,
    sample_eq_map runtime right event rightReady payload law outputEq codeEq viewEq draw rightLaw]
  simp only [FinDist.map_comp]
  apply FinDist.map_congr_of_eq_on_support
  intro value _
  funext who
  dsimp only [Function.comp_apply]
  split
  · rfl
  · rename_i ordinary
    apply congrArg some
    exact State.complete_playerView_congr left right who publicEq
      (left.playerView_observation_eq right who (views who ordinary))
      (congrArg PlayerView.remembered (views who ordinary))
      (congrArg PlayerView.candidates (views who ordinary)) event leftReady rightReady
      _ _ _ _ (fun _ => rfl) (fun _ => rfl)

end Vegas.EventGraphRuntime
