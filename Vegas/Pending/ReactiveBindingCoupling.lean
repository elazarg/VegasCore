/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingShadowInvariant

/-! # Native responses inside the repaired continuation

Other players may use arbitrary raw responses, including forwarding known
evidence. Their equal inputs give the same emitted packet. The repaired owner
continues reconstructing its original input from its existing private memory.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

private theorem response_other_observation
    (execution : (runtime.reactiveApplication leaks).Execution) (actor who : Player)
    (different : who ≠ actor) (response : (runtime.reactiveApplication leaks).Action) :
    (runtime.reactiveApplication leaks).observePlayer
      (execution.respond (runtime.reactiveApplication leaks) actor response).application who =
      (runtime.reactiveApplication leaks).observePlayer execution.application who := by
  have strong : State.playerView
      (execution.respond (runtime.reactiveApplication leaks) actor response).application who =
        execution.application.playerView who := by
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => rfl
    | some transmission =>
        cases transmission with
        | submit material =>
            exact (submitStep_playerView_other (material.call.register execution.application actor)
              actor who different material.call.packet).trans
                (material.call.register_other execution.application actor who different)
        | replay id =>
            cases (execution.network.known actor).find? (fun packet => packet.id = id) <;> rfl
  exact congrArg (fun view : PlayerView graph =>
    (⟨view.who, view.publicView, view.observation, view.candidates⟩ :
      ReactivePlayerView graph)) strong

namespace BindingMemory

/-- Silence and replay keep the reconstructed own history exactly. Replay
here means the existing network operation on an already known envelope; whether
that envelope is conforming remains the separate audit question. -/
theorem transport_response (memory : BindingMemory runtime leaks)
    (left right : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (lengths : (right.recall who).length = memory.responses.length)
    (past : memory.restoreRecall runtime leaks (right.recall who) = left.recall who)
    (observed : memory.shadow.inputView runtime leaks
      (right.observe (runtime.reactiveApplication leaks) who) =
        left.observe (runtime.reactiveApplication leaks) who)
    (network : left.network = right.network)
    (response : (runtime.reactiveApplication leaks).Action)
    (notSubmitted : ∀ submission, response.transmission ≠ some (.submit submission)) :
    let app := runtime.reactiveApplication leaks
    let remembered := memory.record runtime leaks
      (memory.shadow.inputView runtime leaks (right.observe app who)) response
    let before := left.respond app who response
    let after := right.respond app who response
    remembered.restoreRecall runtime leaks (after.recall who) = before.recall who ∧
      remembered.shadow.inputView runtime leaks (after.observe app who) = before.observe app who ∧
      (after.recall who).length = remembered.responses.length := by
  let app := runtime.reactiveApplication leaks
  have receipts : left.receipts = right.receipts :=
    (congrArg ReactiveApplication.PlayerView.receipts observed).symm
  have application := congrArg ReactiveApplication.PlayerView.application observed
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      refine ⟨?_, observed, ?_⟩
      · simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
        rw [restoreRecall_record runtime leaks memory _ lengths, past, observed]
      · simp only [ReactiveApplication.Execution.respond, ↓reduceIte, record,
          List.length_append, List.length_singleton, lengths]
  | some transmission =>
      cases transmission with
      | submit submission => exact (notSubmitted submission rfl).elim
      | replay id =>
          refine ⟨?_, ?_, ?_⟩
          · simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
            rw [restoreRecall_record runtime leaks memory _ lengths, past, observed, network]
          · change (⟨(right.network.replay who id).2.observe who,
              memory.shadow.view (app.observePlayer right.application who), right.receipts⟩ :
                app.PlayerView) =
              ⟨(left.network.replay who id).2.observe who,
                app.observePlayer left.application who, left.receipts⟩
            exact congr (congr (congrArg (ReactiveApplication.PlayerView.mk (app := app))
              (congrArg (fun net => (net.replay who id).2.observe who) network.symm))
                application) receipts.symm
          · simp only [ReactiveApplication.Execution.respond, ↓reduceIte, record,
              List.length_append, List.length_singleton, lengths]

/-- One arbitrary nonowner response preserves the whole reconstructed input
frame. This includes the private catalog and complete response recall; it does
not treat network observations merely by separate marginal equality. -/
theorem foreign_response (memory : BindingMemory runtime leaks)
    (left right : (runtime.reactiveApplication leaks).Execution) (who actor : Player)
    (foreign : actor ≠ who)
    (past : memory.restoreRecall runtime leaks (right.recall who) = left.recall who)
    (observed : memory.shadow.inputView runtime leaks
      (right.observe (runtime.reactiveApplication leaks) who) =
        left.observe (runtime.reactiveApplication leaks) who)
    (network : left.network = right.network)
    (views : ∀ other, other ≠ who →
      left.application.playerView other = right.application.playerView other)
    (recall : ∀ other, other ≠ who → left.recall other = right.recall other)
    (response : (runtime.reactiveApplication leaks).Action) :
    let app := runtime.reactiveApplication leaks
    let before := left.respond app actor response
    let after := right.respond app actor response
    memory.restoreRecall runtime leaks (after.recall who) = before.recall who ∧
      memory.shadow.inputView runtime leaks (after.observe app who) = before.observe app who ∧
      before.network = after.network ∧ before.receipts = after.receipts ∧
      (∀ other, other ≠ who → before.application.playerView other =
        after.application.playerView other) ∧
      (∀ other, other ≠ who → before.recall other = after.recall other) := by
  let app := runtime.reactiveApplication leaks
  let before := left.respond app actor response
  let after := right.respond app actor response
  have receipts : left.receipts = right.receipts :=
    (congrArg ReactiveApplication.PlayerView.receipts observed).symm
  have others := runtime.reactive_respond_hidden_congr leaks left right who actor foreign network
    receipts views recall response
  have leftView := response_other_observation runtime leaks left actor who foreign.symm response
  have rightView := response_other_observation runtime leaks right actor who foreign.symm response
  have application := congrArg ReactiveApplication.PlayerView.application observed
  change memory.restoreRecall runtime leaks (after.recall who) = before.recall who ∧
    memory.shadow.inputView runtime leaks (after.observe app who) = before.observe app who ∧ _
  refine ⟨?_, ?_, others⟩
  · rw [app.respond_recall_other right actor who foreign.symm response,
      app.respond_recall_other left actor who foreign.symm response]
    exact past
  · change (⟨after.network.observe who, memory.shadow.view (app.observePlayer
      after.application who), after.receipts⟩ : app.PlayerView) =
        ⟨before.network.observe who, app.observePlayer before.application who, before.receipts⟩
    rw [leftView, rightView]
    exact congr (congr (congrArg (ReactiveApplication.PlayerView.mk (app := app))
      (congrArg (fun net => net.observe who) others.1.symm)) application) others.2.1.symm

/-- A common passive sample preserves the complete vector of reconstructed
player inputs jointly with the network and scheduler recall. The activated
player may be the repaired owner. No observation is suppressed. -/
theorem activation_inputs (memory : BindingMemory runtime leaks)
    (left right : (runtime.reactiveApplication leaks).Execution) (who actor : Player)
    (past : memory.restoreRecall runtime leaks (right.recall who) = left.recall who)
    (observed : memory.shadow.inputView runtime leaks
      (right.observe (runtime.reactiveApplication leaks) who) =
        left.observe (runtime.reactiveApplication leaks) who)
    (network : left.network = right.network)
    (serviceRecall : left.environmentRecall = right.environmentRecall)
    (views : ∀ other, other ≠ who →
      left.application.playerView other = right.application.playerView other)
    (recall : ∀ other, other ≠ who → left.recall other = right.recall other) :
    let app := runtime.reactiveApplication leaks
    let original := fun next : app.Execution =>
      (next.network, next.environmentRecall, fun player =>
        (next.recall player, next.observe app player))
    let repaired := fun next : app.Execution =>
      (next.network, next.environmentRecall, fun player =>
        if player = who then
          (memory.restoreRecall runtime leaks (next.recall player),
            memory.shadow.inputView runtime leaks (next.observe app player))
        else (next.recall player, next.observe app player))
    (left.environmentStep app (.activate actor)).map original =
      (right.environmentStep app (.activate actor)).map repaired := by
  let app := runtime.reactiveApplication leaks
  have receipts : left.receipts = right.receipts :=
    (congrArg ReactiveApplication.PlayerView.receipts observed).symm
  have ownApplication := congrArg ReactiveApplication.PlayerView.application observed
  have publicEq : left.application.publicView = right.application.publicView :=
    (congrArg ReactivePlayerView.publicView ownApplication).symm
  have environment : left.observeEnvironment app = right.observeEnvironment app := by
    change (⟨left.network.publicView, left.application.publicView, left.receipts⟩ :
      app.EnvironmentView) =
        ⟨right.network.publicView, right.application.publicView, right.receipts⟩
    rw [network, publicEq, receipts]
  dsimp only
  simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp]
  rw [show left.network.pending = right.network.pending from
    congrArg MessageNetwork.pending network]
  apply map_congr_on_support _
  intro selected _
  dsimp only [Function.comp_apply]
  refine Prod.ext (by rw [network]) (Prod.ext (by rw [serviceRecall, environment]) ?_)
  funext player
  by_cases own : player = who
  · subst player
    simp only [↓reduceIte]
    apply Prod.ext past.symm
    change (⟨(left.network.learn actor selected).observe who,
      app.observePlayer left.application who, left.receipts⟩ : app.PlayerView) =
        ⟨(right.network.learn actor selected).observe who,
          memory.shadow.view (app.observePlayer right.application who), right.receipts⟩
    exact congr (congr (congrArg (ReactiveApplication.PlayerView.mk (app := app))
      (congrArg (fun net => (net.learn actor selected).observe who) network))
        ownApplication.symm) receipts
  · simp only [own, ↓reduceIte]
    apply Prod.ext (recall player own)
    change (⟨(left.network.learn actor selected).observe player,
      app.observePlayer left.application player, left.receipts⟩ : app.PlayerView) =
        ⟨(right.network.learn actor selected).observe player,
          app.observePlayer right.application player, right.receipts⟩
    have application := congrArg (fun view : PlayerView graph =>
      (⟨view.who, view.publicView, view.observation, view.candidates⟩ : ReactivePlayerView graph))
        (views player own)
    exact congr (congr (congrArg (ReactiveApplication.PlayerView.mk (app := app))
      (congrArg (fun net => (net.learn actor selected).observe player) network)) application)
        receipts

end BindingMemory

end Vegas.EventGraphRuntime
