module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveBindingLikelihood
public import Interaction.ReactiveMessageReadout

@[expose] public section

/-! # Scheduled opaque bindings under passive observation

A designated existing owner visit submits one canonical binding. All other
visits respond silently. The actual roster law has
the same foreign auxiliary readout for any private binding result. The owner
case requires the same private result. The policy uses only its actual response
count to choose the visit.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem bindingTraffic_activation (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (left right : ((reactiveApplication timeouts) leaks).Execution) (focal actor : Player)
    (same : (bindingTraffic timeouts) leaks focal left = (bindingTraffic timeouts) leaks focal
      right)
    (sample : Finset (MessageId Player)) :
    (bindingTraffic timeouts) leaks focal
        (left.sampledActivation ((reactiveApplication timeouts) leaks) actor sample) =
      (bindingTraffic timeouts) leaks focal
        (right.sampledActivation ((reactiveApplication timeouts) leaks) actor sample) := by
  have networks := congrArg Prod.fst same
  have receipts := congrArg (fun value => value.2.1) same
  have environments := congrArg (fun value => value.2.2.1) same
  have privateViews := congrArg (fun value => value.2.2.2) same
  have publics := congrArg (fun value => value.2.2.2.2.2) same
  dsimp only [bindingTraffic] at networks receipts environments privateViews publics
  have observed : left.observeEnvironment ((reactiveApplication timeouts) leaks) =
      right.observeEnvironment ((reactiveApplication timeouts) leaks) := by
    change ReactiveApplication.EnvironmentView.mk left.network.publicView
      left.application.publicView left.receipts = _
    rw [networks, publics, receipts]
    rfl
  refine Prod.ext ?_ (Prod.ext receipts (Prod.ext ?_ privateViews))
  · change left.network.learn actor sample = right.network.learn actor sample
    rw [networks]
  · change left.environmentRecall ++ [⟨left.observeEnvironment _, .activate actor⟩] = _
    rw [environments, observed]
    rfl

theorem bindingTraffic_silent (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (left right : ((reactiveApplication timeouts) leaks).Execution) (focal actor : Player)
    (same : (bindingTraffic timeouts) leaks focal left = (bindingTraffic timeouts) leaks focal
      right)
    (response : ((reactiveApplication timeouts) leaks).Action)
    (transport : response = ⟨none⟩) :
    (bindingTraffic timeouts) leaks focal
        (left.respond ((reactiveApplication timeouts) leaks) actor response) =
      (bindingTraffic timeouts) leaks focal
        (right.respond ((reactiveApplication timeouts) leaks) actor response) := by
  let app := (reactiveApplication timeouts) leaks
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
  have recalledAfter := app.respond_focal_recall_eq left right actor focal response
    networks observed recalled (by
      intro submission transmitted
      rcases transport with rfl
      cases transmitted)
  have firstState : (left.respond app actor response).application = left.application := by
    rcases transport with rfl
    rfl
  have secondState : (right.respond app actor response).application = right.application := by
    rcases transport with rfl
    rfl
  refine Prod.ext ?_ (Prod.ext receipts (Prod.ext environments (Prod.ext recalledAfter ?_)))
  · rcases transport with rfl
    exact networks
  · change ((left.respond app actor response).application.playerView focal,
        (left.respond app actor response).application.publicView) =
      ((right.respond app actor response).application.playerView focal,
        (right.respond app actor response).application.publicView)
    rw [firstState, secondState]
    exact Prod.ext views publics

end Vegas.EventGraphRuntime
