/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.EventHandleObservation
import Vegas.Pending.EventPublicState
import Vegas.EventGraph.Commutation

/-! # Public native binding steps for arbitrary private meanings -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
/-- A binding completion exposes its identity, accepted handle and clock,
irrespective of its private result, including accepted failure. -/
theorem State.complete_binding_publicView_congr (left right : State graph)
    (publicEq : left.publicView = right.publicView)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (leftReady : left.config.cut.Ready event) (rightReady : right.config.cut.Ready event)
    (leftAction rightAction : graph.Action event)
    (leftValue rightValue : (graph.outputLayout event).Value) :
    (left.complete event leftReady leftAction leftValue).publicView =
      (right.complete event rightReady rightAction rightValue).publicView := by
  classical
  have observed := congrArg PublicView.observation publicEq
  have orders := congrArg PublicObservation.completionOrder observed
  have cuts := cut_eq_of_completionOrder_eq left.config right.config orders
  have observations : graph.publicObserve (left.config.complete event leftReady leftAction
      leftValue) = graph.publicObserve (right.config.complete event rightReady rightAction
        rightValue) := by
    apply PublicObservation.ext graph
    · simpa only [State.publicView, publicObserve, Config.complete, List.map_append,
        List.map_cons, List.map_nil] using congrArg (fun order => order ++ [event]) orders
    · apply graph.publicStore_congr
      intro field visible
      rw [store_complete, store_complete]
      by_cases selected : field = .inr event
      · subst field
        change (graph.outputLayout event).IsPublic at visible
        rw [binding] at visible
        cases visible
      · rw [Function.update_of_ne selected, Function.update_of_ne selected]
        have prior := congrFun (congrArg PublicObservation.store observed) field
        simpa only [State.publicView, publicObserve, publicStore_of_public, visible] using prior
  have clocks : left.clock = right.clock := congrArg PublicView.clock publicEq
  have activations : left.activatedAt = right.activatedAt :=
    congrArg PublicView.activatedAt publicEq
  have refreshed : State.refreshActivated (left.config.complete event leftReady leftAction
      leftValue) left.clock left.activatedAt =
      State.refreshActivated (right.config.complete event rightReady rightAction rightValue)
        right.clock right.activatedAt := by
    funext query
    simp only [State.refreshActivated, Config.complete_cut, cuts]
    rw [show left.clock = right.clock from clocks,
      show left.activatedAt = right.activatedAt from activations]
  have accepted : left.accepted = right.accepted := congrArg PublicView.accepted publicEq
  change (⟨_, left.accepted, left.clock, _⟩ : PublicView graph) =
    ⟨_, right.accepted, right.clock, _⟩
  dsimp only [State.complete]
  rw [observations, accepted, refreshed, clocks]

/-- The entire optional public output of a binding handler depends only on
its public input. This also covers wrong owners, reused handles and late calls. -/
theorem handle_commitment_publicView_congr (runtime : EventGraphRuntime graph)
    (left right : State graph) (publicEq : left.publicView = right.publicView)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph) :
    (handle runtime left ⟨id, .commitment event candidate⟩).map State.publicView =
      (handle runtime right ⟨id, .commitment event candidate⟩).map State.publicView := by
  classical
  have status : (handle runtime left ⟨id, .commitment event candidate⟩).isSome =
      (handle runtime right ⟨id, .commitment event candidate⟩).isSome := by
    apply Bool.eq_iff_iff.mpr
    rw [← State.publicView_bindingIncludable runtime left id event candidate,
      ← State.publicView_bindingIncludable runtime right id event candidate, publicEq]
  cases first : handle runtime left ⟨id, .commitment event candidate⟩ with
  | none =>
      cases second : handle runtime right ⟨id, .commitment event candidate⟩ with
      | none => rfl
      | some value =>
          simp only [first, second, Option.isSome_none, Option.isSome_some] at status
          cases status
  | some firstNext =>
      cases second : handle runtime right ⟨id, .commitment event candidate⟩ with
      | none =>
          simp only [first, second, Option.isSome_none, Option.isSome_some] at status
          cases status
      | some secondNext =>
          have possible := (left.publicView_bindingIncludable runtime id event candidate).mpr
            (by rw [first]; rfl)
          have otherPossible := (right.publicView_bindingIncludable runtime id event candidate).mpr
            (by rw [second]; rfl)
          simp only [PublicView.BindingIncludable,
            State.publicView_eventReady] at possible otherPossible
          obtain ⟨ready, timely, conditions⟩ := possible
          obtain ⟨otherReady, otherTimely, otherConditions⟩ := otherPossible
          cases node : nodeView graph event with
          | sample payload law outputEq codeEq => simp only [node] at conditions
          | resolve owner payload binding checks outputEq codeEq => simp only [node] at conditions
          | bind owner payload outputEq codeEq =>
              simp only [node] at conditions otherConditions
              obtain ⟨sender, owned, vacant, unused⟩ := conditions
              obtain ⟨_, _, otherVacant, otherUnused⟩ := otherConditions
              rw [handle_commitment_eq runtime left id event candidate owner payload outputEq
                codeEq node ready timely sender owned vacant unused] at first
              rw [handle_commitment_eq runtime right id event candidate owner payload outputEq
                codeEq node otherReady otherTimely sender owned otherVacant otherUnused] at second
              cases Option.some.inj first
              cases Option.some.inj second
              simp only [Option.map_some]
              apply congrArg some
              have completed := State.complete_binding_publicView_congr left right publicEq event
                owner payload outputEq ready otherReady
                (cast (congrArg EventField.Action outputEq.symm)
                  (left.bindingResult candidate payload))
                (cast (congrArg EventField.Action outputEq.symm)
                  (right.bindingResult candidate payload))
                (cast (congrArg EventField.Value outputEq.symm)
                  (left.bindingResult candidate payload))
                (cast (congrArg EventField.Value outputEq.symm)
                  (right.bindingResult candidate payload))
              exact congrArg (fun view : PublicView graph =>
                {view with accepted := Function.update view.accepted (.inr event) (some candidate)})
                completed

end Vegas.EventGraphRuntime
