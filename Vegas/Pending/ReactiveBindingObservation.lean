/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveResponseObservation
import Vegas.Pending.EventHandleObservation
import Interaction.MessageNetworkCounters

/-! # Foreign observations of an opaque binding prefix

Changing the privately fixed meaning of one submitted handle preserves the
complete network and every other player's response input. Including that
binding preserves this equality even when its hidden result differs. The
statement retains foreign own-action recall and permits arbitrary passive
observation of the opaque packet.

These are native prefix laws, not a sequential-equilibrium theorem. The owner
has different private information, and its later repaired continuation must
withhold wherever the original unusable binding could not publish.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

private theorem reactive_input_congr
    (left right : (runtime.reactiveApplication leaks).Execution) (observer : Player)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (recall : left.recall observer = right.recall observer)
    (observed : left.application.playerView observer = right.application.playerView observer) :
    (left.recall observer, left.observe (runtime.reactiveApplication leaks) observer) =
      (right.recall observer, right.observe (runtime.reactiveApplication leaks) observer) := by
  have projected := congrArg (fun view : PlayerView graph =>
    (⟨view.who, view.publicView, view.observation, view.candidates⟩ :
      ReactivePlayerView graph)) observed
  apply Prod.ext recall
  change ReactiveApplication.PlayerView.mk (app := runtime.reactiveApplication leaks)
    _ _ _ = _
  rw [network, receipts]
  exact congrArg (fun view =>
    (⟨right.network.observe observer, view, right.receipts⟩ :
      (runtime.reactiveApplication leaks).PlayerView)) projected

/-- The complete network state, including earlier leaks, is independent of the
new handle's private meaning. No foreign-message observation is removed. -/
theorem reactiveBinding_network
    (execution : (runtime.reactiveApplication leaks).Execution)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (first second : PublicationResult (L.Val payload)) (serial : Nat) :
    (execution.respond (runtime.reactiveApplication leaks) owner
      (runtime.reactiveBinding leaks owner event payload first serial)).network =
      (execution.respond (runtime.reactiveApplication leaks) owner
        (runtime.reactiveBinding leaks owner event payload second serial)).network := by
  cases first <;> cases second <;> rfl

private theorem reactiveBinding_other_view
    (execution : (runtime.reactiveApplication leaks).Execution)
    (owner observer : Player) (different : observer ≠ owner)
    (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (serial : Nat) :
    (execution.respond (runtime.reactiveApplication leaks) owner
      (runtime.reactiveBinding leaks owner event payload result serial)).application.playerView
        observer = execution.application.playerView observer := by
  let material : Submission graph :=
    ⟨.commitment event (owner, .prepared serial), match result with
      | .failure => none
      | .success value => some ⟨payload, value⟩⟩
  exact (submitStep_playerView_other (material.register execution.application owner)
    owner observer different material.packet).trans
      (material.register_other execution.application owner observer different)

/-- An actual include operation preserves a foreign input whenever the opaque
binding and that observer's earlier input agree. Acceptance is proved equal;
no premise asserts that the hidden binding values or owner observations agree. -/
theorem reactive_include_commitment_input_congr
    (left right : (runtime.reactiveApplication leaks).Execution) (observer : Player)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (recall : left.recall observer = right.recall observer)
    (observed : left.application.playerView observer = right.application.playerView observer)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (evidence : Option (OpeningFact graph))
    (found : left.network.lookup id = some ⟨id, ⟨.commitment event candidate, evidence⟩⟩) :
    let first := left.includePending (runtime.reactiveApplication leaks) id
    let second := right.includePending (runtime.reactiveApplication leaks) id
    first.network = second.network ∧ first.receipts = second.receipts ∧
      (first.recall observer, first.observe (runtime.reactiveApplication leaks) observer) =
        (second.recall observer, second.observe (runtime.reactiveApplication leaks) observer) :=
    by
  have rightFound : right.network.lookup id =
      some ⟨id, ⟨.commitment event candidate, evidence⟩⟩ := network ▸ found
  have handled := handle_commitment_playerView_congr runtime left.application right.application
    observer id event candidate observed
  simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    found, rightFound, reactiveApplication]
  cases first : handle runtime left.application ⟨id, .commitment event candidate⟩ with
  | none =>
      cases second : handle runtime right.application ⟨id, .commitment event candidate⟩ with
      | none =>
          simp only [Option.getD_none, Option.isSome_none]
          refine ⟨by rw [network], by rw [receipts], ?_⟩
          apply Prod.ext recall
          change ReactiveApplication.PlayerView.mk (app := runtime.reactiveApplication leaks)
            _ _ _ = _
          rw [network, receipts]
          congr 1
          exact congrArg (fun view : PlayerView graph =>
            (⟨view.who, view.publicView, view.observation, view.candidates⟩ :
              ReactivePlayerView graph)) observed
      | some after => simp only [first, second, Option.map_none, Option.map_some] at handled
                      contradiction
  | some before =>
      cases second : handle runtime right.application ⟨id, .commitment event candidate⟩ with
      | none => simp only [first, second, Option.map_none, Option.map_some] at handled
                contradiction
      | some after =>
          simp only [first, second, Option.map_some, Option.some.injEq] at handled
          simp only [Option.getD_some, Option.isSome_some]
          refine ⟨by rw [network], by rw [receipts], ?_⟩
          apply Prod.ext recall
          change ReactiveApplication.PlayerView.mk (app := runtime.reactiveApplication leaks)
            _ _ _ = _
          rw [network, receipts]
          congr 1
          exact congrArg (fun view : PlayerView graph =>
            (⟨view.who, view.publicView, view.observation, view.candidates⟩ :
              ReactivePlayerView graph)) handled

/-- Atomic submission followed by inclusion hides the chosen binding meaning
from every other player's full response input, not merely from the ledger.
Failure versus a valid value is one instance of this statement. -/
theorem reactiveBinding_include_other_input
    (execution : (runtime.reactiveApplication leaks).Execution)
    (owner observer : Player) (different : observer ≠ owner)
    (event : graph.EventId) (payload : L.Ty)
    (first second : PublicationResult (L.Val payload)) (serial : Nat)
    (freshSerial : execution.network.SerialsBeforeNext) :
    let left := (execution.respond (runtime.reactiveApplication leaks) owner
      (runtime.reactiveBinding leaks owner event payload first serial)).includePending
        (runtime.reactiveApplication leaks) (owner, execution.network.nextSerial owner)
    let right := (execution.respond (runtime.reactiveApplication leaks) owner
      (runtime.reactiveBinding leaks owner event payload second serial)).includePending
        (runtime.reactiveApplication leaks) (owner, execution.network.nextSerial owner)
    left.network = right.network ∧ left.receipts = right.receipts ∧
      (left.recall observer, left.observe (runtime.reactiveApplication leaks) observer) =
        (right.recall observer, right.observe (runtime.reactiveApplication leaks) observer) := by
  let app := runtime.reactiveApplication leaks
  let submitted (result : PublicationResult (L.Val payload)) := execution.respond app owner
    (runtime.reactiveBinding leaks owner event payload result serial)
  have network := reactiveBinding_network runtime leaks execution owner event payload
    first second serial
  have recalled := (app.respond_recall_other execution owner observer different
    (runtime.reactiveBinding leaks owner event payload first serial)).trans
      (app.respond_recall_other execution owner observer different
        (runtime.reactiveBinding leaks owner event payload second serial)).symm
  have observed := (reactiveBinding_other_view runtime leaks execution owner observer different
    event payload first serial).trans (reactiveBinding_other_view runtime leaks execution
      owner observer different event payload second serial).symm
  apply reactive_include_commitment_input_congr runtime leaks (submitted first) (submitted second)
    observer network rfl recalled observed (owner, execution.network.nextSerial owner) event
    (owner, .prepared serial) none
  cases first <;>
    exact freshSerial.lookup_submit owner ⟨.commitment event (owner, .prepared serial), none⟩

/-- Passive observation of the submitted opaque envelope has the same law for
every foreign player, with its actual preexisting private recall preserved. -/
theorem reactiveBinding_activation_other_input
    (execution : (runtime.reactiveApplication leaks).Execution)
    (owner observer : Player) (different : observer ≠ owner)
    (event : graph.EventId) (payload : L.Ty)
    (first second : PublicationResult (L.Val payload)) (serial : Nat) :
    ((execution.respond (runtime.reactiveApplication leaks) owner
      (runtime.reactiveBinding leaks owner event payload first serial)).environmentStep
        (runtime.reactiveApplication leaks) (.activate observer)).map (fun next =>
          (next.recall observer, next.observe (runtime.reactiveApplication leaks) observer)) =
      ((execution.respond (runtime.reactiveApplication leaks) owner
        (runtime.reactiveBinding leaks owner event payload second serial)).environmentStep
          (runtime.reactiveApplication leaks) (.activate observer)).map (fun next =>
            (next.recall observer, next.observe (runtime.reactiveApplication leaks) observer)) := by
  let app := runtime.reactiveApplication leaks
  let submitted (result : PublicationResult (L.Val payload)) := execution.respond app owner
    (runtime.reactiveBinding leaks owner event payload result serial)
  have network := reactiveBinding_network runtime leaks execution owner event payload
    first second serial
  have recalled := (app.respond_recall_other execution owner observer different
    (runtime.reactiveBinding leaks owner event payload first serial)).trans
      (app.respond_recall_other execution owner observer different
        (runtime.reactiveBinding leaks owner event payload second serial)).symm
  have observed := (reactiveBinding_other_view runtime leaks execution owner observer different
    event payload first serial).trans (reactiveBinding_other_view runtime leaks execution
      owner observer different event payload second serial).symm
  change ((submitted first).environmentStep app (.activate observer)).map _ =
    ((submitted second).environmentStep app (.activate observer)).map _
  simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_comp]
  change (submitted first).network = (submitted second).network at network
  rw [show (submitted first).network.pending = (submitted second).network.pending from
    congrArg MessageNetwork.pending network]
  apply FinDist.map_congr_of_eq_on_support
  intro selected _
  apply reactive_input_congr runtime leaks
  · rw [network]
    rfl
  · rfl
  · exact recalled
  · exact observed

end Vegas.EventGraphRuntime
