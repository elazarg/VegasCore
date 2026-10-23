/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingSchedule
import Vegas.Pending.ReactiveOpeningSettlement
import Vegas.Pending.ReactiveRevealBlock
import GameTheoryExtensions.Math.Probability.Support

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

theorem bindingTraffic_opening (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (left right : (runtime.reactiveApplication leaks).Execution) (owner focal : Player)
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (owned : candidate.1 = owner)
    (leftValid : left.application.candidates.lookup candidate = .openable raw)
    (rightValid : right.application.candidates.lookup candidate = .openable raw)
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right) :
    runtime.bindingTraffic leaks focal
        (left.respond (runtime.reactiveApplication leaks) owner
          (runtime.windowOpening leaks event candidate raw)) =
      runtime.bindingTraffic leaks focal
        (right.respond (runtime.reactiveApplication leaks) owner
          (runtime.windowOpening leaks event candidate raw)) := by
  let app := runtime.reactiveApplication leaks
  have networks := congrArg Prod.fst same
  have receipts := congrArg (fun value => value.2.1) same
  have environments := congrArg (fun value => value.2.2.1) same
  have recalled := congrArg (fun value => value.2.2.2.1) same
  have views := congrArg (fun value => value.2.2.2.2.1) same
  have publics := congrArg (fun value => value.2.2.2.2.2) same
  dsimp only [bindingTraffic] at networks receipts environments recalled views publics
  have observed : left.observe app focal = right.observe app focal := by
    change ReactiveApplication.PlayerView.mk _ _ _ = _
    rw [networks]
    exact congrArg₂ (fun view receipts =>
      (⟨right.network.observe focal, view, receipts⟩ : app.PlayerView)) views receipts
  have emitted : app.packet left.application owner (left.network.known owner)
        (disclosureSubmission (.opening event candidate raw)) =
      app.packet right.application owner (right.network.known owner)
        (disclosureSubmission (.opening event candidate raw)) :=
    (runtime.windowOpening_packet leaks owner event candidate raw left.application
      (left.network.known owner) owned leftValid).trans
        ((congrArg (fun view : PublicView graph => (⟨.opening event candidate raw,
          some ⟨candidate, raw⟩, view.tokenFor (.opening event candidate raw)⟩ :
            WitnessedPacket graph)) publics).trans
        (runtime.windowOpening_packet leaks owner event candidate raw right.application
          (right.network.known owner) owned rightValid).symm)
  have recallEq := app.respond_focal_recall_eq left right owner focal
    (runtime.windowOpening leaks event candidate raw) networks observed recalled (by
      intro submission transmitted
      have selected : disclosureSubmission (.opening event candidate raw) = submission :=
        Option.some.inj transmitted
      subst submission
      exact emitted)
  refine Prod.ext ?_ (Prod.ext receipts (Prod.ext environments
    (Prod.ext recallEq (Prod.ext views publics))))
  change (left.network.submit owner (app.packet left.application owner
    (left.network.known owner) (disclosureSubmission (.opening event candidate raw)))).2 = _
  rw [emitted, networks]
  rfl

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
  change ((environmentStep runtime left.application command).map _) =
    ((environmentStep runtime right.application command).map _)
  rw [← PMF.bind_pure_comp, Function.comp_def, ← PMF.bind_pure_comp, Function.comp_def]
  apply bind_eq_of_map_eq _ _ _ _ changes
  intro before _ after _ equal
  apply congrArg PMF.pure
  dsimp only [bindingTraffic, Function.comp_apply]
  rw [networks, receipts, environments, environment, recalled, equal]
  exact congrArg (fun publicView => (right.network, right.receipts,
    right.environmentRecall ++ [⟨right.observeEnvironment app, .application command⟩],
      right.recall focal, after.playerView focal, publicView))
        (congrArg PlayerView.publicView equal)

end Vegas.EventGraphRuntime
