/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveContinuationObservation
import Vegas.Pending.ReactiveResponseObservation
import Vegas.Pending.EvidenceNormalization
import Interaction.ReactiveRounds
import GameTheoryExtensions.Math.Probability.Support

/-! # Opponent responses during a private binding repair

Matching nondeviator inputs produce the same response law and the same emitted
packet, including arbitrary raw evidence requests and forwarding. The result
preserves the opponents' inputs jointly, together with the network and service
recall. It does not assert equivalence after arbitrary later packet inclusion.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

private theorem observed_eq
    (left right : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (views : left.application.playerView who = right.application.playerView who) :
    left.observe (runtime.reactiveApplication leaks) who =
      right.observe (runtime.reactiveApplication leaks) who := by
  have projected := congrArg (fun view : PlayerView graph =>
    (⟨view.who, view.publicView, view.observation, view.candidates⟩ :
      ReactivePlayerView graph)) views
  change ReactiveApplication.PlayerView.mk (app := runtime.reactiveApplication leaks)
    _ _ _ = _
  rw [network, receipts]
  exact congrArg (fun view => (⟨right.network.observe who, view, right.receipts⟩ :
    (runtime.reactiveApplication leaks).PlayerView)) projected

private theorem response_other_playerView
    (execution : (runtime.reactiveApplication leaks).Execution) (actor observer : Player)
    (different : observer ≠ actor) (response : (runtime.reactiveApplication leaks).Action) :
    (execution.respond (runtime.reactiveApplication leaks) actor response).application.playerView
      observer = execution.application.playerView observer := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | submit material =>
          exact (submitStep_playerView_other (material.call.register execution.application actor)
            actor observer different material.call.packet).trans
              (material.call.register_other execution.application actor observer different)
      | replay id =>
          cases (execution.network.known actor).find? (fun packet => packet.id = id) <;> rfl

private theorem response_actor_playerView
    (left right : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (views : left.application.playerView who = right.application.playerView who)
    (response : (runtime.reactiveApplication leaks).Action) :
    (left.respond (runtime.reactiveApplication leaks) who response).application.playerView who =
      (right.respond (runtime.reactiveApplication leaks) who response).application.playerView
        who := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact views
  | some transmission =>
      cases transmission with
      | submit material => exact submit_playerView_congr runtime leaks _ _ who material views
      | replay id =>
          cases (left.network.known who).find? (fun packet => packet.id = id) <;>
            cases (right.network.known who).find? (fun packet => packet.id = id) <;> exact views

private theorem submission_packet_congr
    (left right : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (network : left.network = right.network)
    (views : left.application.playerView who = right.application.playerView who)
    (submission : WitnessedSubmission graph) :
    submission.emit ((runtime.reactiveApplication leaks).submit left.application who submission)
        who (left.network.known who) =
      submission.emit ((runtime.reactiveApplication leaks).submit right.application who submission)
        who (right.network.known who) := by
  have submitted := submit_playerView_congr runtime leaks left.application right.application
    who submission views
  have candidates := congrArg PlayerView.candidates submitted
  have publics : ((runtime.reactiveApplication leaks).submit left.application who
        submission).publicView =
      ((runtime.reactiveApplication leaks).submit right.application who submission).publicView :=
    congrArg PlayerView.publicView submitted
  rw [WitnessedSubmission.emit_eq_resolve, WitnessedSubmission.emit_eq_resolve, network, publics]
  exact congrArg (fun table => WitnessedPacket.mk submission.call.packet
    (submission.evidence.resolve who table (right.network.known who))
    (((runtime.reactiveApplication leaks).submit right.application who
      submission).publicView.tokenFor submission.call.packet)) candidates

/-- A common opponent response preserves all opponents' local states at once.
The private owner's candidates and recall may differ throughout. -/
theorem reactive_respond_hidden_congr
    (left right : (runtime.reactiveApplication leaks).Execution) (hidden actor : Player)
    (foreign : actor ≠ hidden)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (views : ∀ who, who ≠ hidden →
      left.application.playerView who = right.application.playerView who)
    (recall : ∀ who, who ≠ hidden → left.recall who = right.recall who)
    (response : (runtime.reactiveApplication leaks).Action) :
    let first := left.respond (runtime.reactiveApplication leaks) actor response
    let second := right.respond (runtime.reactiveApplication leaks) actor response
    first.network = second.network ∧ first.receipts = second.receipts ∧
      (∀ who, who ≠ hidden →
        first.application.playerView who = second.application.playerView who) ∧
      (∀ who, who ≠ hidden → first.recall who = second.recall who) := by
  let app := runtime.reactiveApplication leaks
  have actingView := observed_eq runtime leaks left right actor network receipts
    (views actor foreign)
  have actingRecall := recall actor foreign
  have networks : (left.respond app actor response).network =
      (right.respond app actor response).network := by
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => exact network
    | some transmission =>
        cases transmission with
        | replay id =>
            change (left.network.replay actor id).2 = (right.network.replay actor id).2
            rw [network]
        | submit material =>
            have packet := submission_packet_congr runtime leaks left right actor network
              (views actor foreign) material
            change (left.network.submit actor (material.emit
              (app.submit left.application actor material) actor (left.network.known actor))).2 =
              (right.network.submit actor (material.emit
                (app.submit right.application actor material) actor
                  (right.network.known actor))).2
            rw [packet, network]
  refine ⟨networks, receipts, ?_, ?_⟩
  · intro who ordinary
    by_cases same : who = actor
    · subst who
      exact response_actor_playerView runtime leaks left right actor (views actor foreign) response
    · exact (response_other_playerView runtime leaks left actor who same response).trans
        ((views who ordinary).trans
          (response_other_playerView runtime leaks right actor who same response).symm)
  · intro who ordinary
    by_cases same : who = actor
    · subst who
      rcases response with ⟨transmission⟩
      cases transmission with
      | none =>
          simp only [ReactiveApplication.Execution.respond, ↓reduceIte,
            actingView, actingRecall]
      | some transmission =>
          cases transmission with
          | replay id =>
              simp only [ReactiveApplication.Execution.respond, network,
                MessageNetwork.replay, ↓reduceIte, actingView, actingRecall]
          | submit material =>
              have packet := submission_packet_congr runtime leaks left right actor network
                (views actor foreign) material
              simp only [ReactiveApplication.Execution.respond, MessageNetwork.submit,
                ↓reduceIte]
              change left.recall actor ++ [⟨left.observe app actor, _,
                some ⟨(actor, left.network.nextSerial actor), material.emit
                  (app.submit left.application actor material) actor
                  (left.network.known actor)⟩⟩] = _
              rw [actingRecall, actingView, packet, network]
              rfl
    · rw [app.respond_recall_other left actor who same response,
        app.respond_recall_other right actor who same response]
      exact recall who ordinary

/-- One common random response couples the complete vector of opponent inputs.
This is joint-law equality, not merely equality of individual marginals. -/
theorem reactive_invoke_hidden_congr
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (left right : (runtime.reactiveApplication leaks).Execution) (hidden actor : Player)
    (foreign : actor ≠ hidden)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (serviceRecall : left.environmentRecall = right.environmentRecall)
    (views : ∀ who, who ≠ hidden →
      left.application.playerView who = right.application.playerView who)
    (recall : ∀ who, who ≠ hidden → left.recall who = right.recall who) :
    let readout := fun next : (runtime.reactiveApplication leaks).Execution =>
      (next.network, next.receipts, next.environmentRecall, fun who =>
        if who = hidden then none else some (next.recall who, next.application.playerView who))
    ((runtime.reactiveApplication leaks).invoke players actor left).map readout =
      ((runtime.reactiveApplication leaks).invoke players actor right).map readout := by
  dsimp only
  have input := observed_eq runtime leaks left right actor network receipts (views actor foreign)
  have past := recall actor foreign
  simp only [ReactiveApplication.invoke, PMF.map_comp, input, past]
  apply map_congr_on_support _
  intro response _
  obtain ⟨networks, charges, observed, recalled⟩ := reactive_respond_hidden_congr runtime leaks
    left right hidden actor foreign network receipts views recall response
  apply Prod.ext networks
  apply Prod.ext charges
  apply Prod.ext serviceRecall
  funext who
  dsimp only [Function.comp_apply]
  split
  · rfl
  · rename_i ordinary
    exact congrArg some (Prod.ext (recalled who ordinary) (observed who ordinary))

end Vegas.EventGraphRuntime
