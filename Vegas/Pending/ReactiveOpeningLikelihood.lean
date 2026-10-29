/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveBindingSchedule
import Vegas.Pending.ReactiveContinuationObservation

/-! # Opening windows after private binding histories

These couplings retain the real network, service recall, focal input and focal
private recall. They do not equate other players' earlier private submissions.
The opening response still uses authentic candidate evidence and every passive
sample remains in the actual execution.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem bindingTraffic_include_of_handler (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (left right : (runtime.reactiveApplication leaks).Execution) (focal : Player)
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right)
    (id : MessageId Player) (message : Message Player (WitnessedPacket graph))
    (found : left.network.lookup id = some message)
    (handled : ((runtime.reactiveApplication leaks).handle left.application message).map
        (fun state => state.playerView focal) =
      ((runtime.reactiveApplication leaks).handle right.application message).map
        (fun state => state.playerView focal)) :
    runtime.bindingTraffic leaks focal
        (left.includePending (runtime.reactiveApplication leaks) id) =
      runtime.bindingTraffic leaks focal
        (right.includePending (runtime.reactiveApplication leaks) id) := by
  let app := runtime.reactiveApplication leaks
  have networks : left.network = right.network := congrArg Prod.fst same
  have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) same
  have recalled : left.recall focal = right.recall focal :=
    congrArg (fun value => value.2.2.2.1) same
  have views : left.application.playerView focal = right.application.playerView focal :=
    congrArg (fun value => value.2.2.2.2.1) same
  have publics : left.application.publicView = right.application.publicView :=
    congrArg (fun value => value.2.2.2.2.2) same
  have rightFound : right.network.lookup id = some message := networks ▸ found
  simp only [bindingTraffic, ReactiveApplication.Execution.includePending,
    MessageNetwork.includePending, found, rightFound]
  cases first : (runtime.reactiveApplication leaks).handle left.application message with
  | none =>
      cases second : (runtime.reactiveApplication leaks).handle right.application message with
      | none =>
          simp only [Option.getD_none, Option.isSome_none]
          exact Prod.ext (by rw [networks]) (Prod.ext (by rw [receipts])
            (Prod.ext environments (Prod.ext recalled (Prod.ext views publics))))
      | some state =>
          simp only [first, second, Option.map_none, Option.map_some] at handled
          cases handled
  | some before =>
      cases second : (runtime.reactiveApplication leaks).handle right.application message with
      | none =>
          simp only [first, second, Option.map_none, Option.map_some] at handled
          cases handled
      | some after =>
          have nextViews : before.playerView focal = after.playerView focal := by
            simpa only [first, second, Option.map_some, Option.some.injEq] using handled
          simp only [Option.getD_some, Option.isSome_some]
          exact Prod.ext (by rw [networks]) (Prod.ext (by rw [receipts])
            (Prod.ext environments (Prod.ext recalled
              (Prod.ext nextViews (congrArg PlayerView.publicView nextViews)))))

/-- Real clock and expiry commands preserve the focal traffic law.
Public chance is handled with its source sample, rather than by this lemma. -/
theorem bindingTraffic_maintenance (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (left right : (runtime.reactiveApplication leaks).Execution) (focal : Player)
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right)
    (command : EnvironmentCommand graph)
    (maintenance : ∀ event, command ≠ .executeSample event) :
    (left.environmentStep (runtime.reactiveApplication leaks) (.application command)).map
        (runtime.bindingTraffic leaks focal) =
      (right.environmentStep (runtime.reactiveApplication leaks) (.application command)).map
        (runtime.bindingTraffic leaks focal) := by
  let app := runtime.reactiveApplication leaks
  have networks : left.network = right.network := congrArg Prod.fst same
  have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) same
  have recalled : left.recall focal = right.recall focal :=
    congrArg (fun value => value.2.2.2.1) same
  have views : left.application.playerView focal = right.application.playerView focal :=
    congrArg (fun value => value.2.2.2.2.1) same
  have publics : left.application.publicView = right.application.publicView :=
    congrArg (fun value => value.2.2.2.2.2) same
  have environment : left.observeEnvironment app = right.observeEnvironment app := by
    change ReactiveApplication.EnvironmentView.mk left.network.publicView
      left.application.publicView left.receipts = _
    rw [networks, publics, receipts]
    rfl
  have changes := maintenance_playerView_congr runtime left.application right.application focal
    command maintenance views
  simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp]
  change (((environmentStep runtime left.application command).map State.drain).map _) =
    (((environmentStep runtime right.application command).map State.drain).map _)
  rw [PMF.map_comp, PMF.map_comp]
  rw [← PMF.bind_pure_comp, Function.comp_def, ← PMF.bind_pure_comp, Function.comp_def]
  apply bind_eq_of_map_eq _ _ _ _ changes
  intro before _ after _ equal
  have drained := State.drain_playerView_congr before after focal equal
  apply congrArg PMF.pure
  dsimp only [bindingTraffic, Function.comp_apply]
  rw [networks, receipts, environments, environment, recalled, drained]
  exact congrArg (fun publicView => (right.network, right.receipts,
    right.environmentRecall ++ [⟨right.observeEnvironment app, .application command⟩],
      right.recall focal, after.drain.playerView focal, publicView))
        (congrArg PlayerView.publicView drained)

end Vegas.EventGraphRuntime
