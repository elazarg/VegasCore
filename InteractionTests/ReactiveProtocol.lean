/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveEvaluation
import Interaction.ReactiveObservation

/-! # Network observation, repeated activation, and in-flight reactions

Alice sends a packet; Bob privately observes it and replies before inclusion.
The scheduler then sees Bob's actual output and can revisit Alice. These are
transitions of the canonical reactive protocol, with no response batches.
-/

noncomputable section

namespace InteractionTests.ReactiveProtocol

open Interaction GameTheory.Protocol GameTheory.Math.Probability

private abbrev app : ReactiveApplication Bool where
  State := Unit
  Payload := Nat
  Submission := Nat
  EnvironmentCommand := Empty
  LocalObservation := Unit
  PublicObservation := Unit
  packet := fun _ _ _ => id
  submit state _ _ := state
  handle state _ := some state
  environment _ command := nomatch command
  observePlayer _ _ := ()
  observePublic _ := ()
  observePending _ pending := FinDist.pure (pending.map Message.id).toFinset

private def send (value : Nat) : app.Action := ⟨some (.submit value)⟩

private def players : Bool → app.Policy := fun who _ view =>
  FinDist.pure (send (if who then
    (view.messages.leaked.head?.map Message.payload).getD 0 + 1 else 7))

/-- Later scheduling can depend on the actual incoming message, including
the broadcaster. The second Alice activation is an explicit network choice. -/
private def scheduler : app.Scheduler := fun history view =>
  FinDist.pure (match history.length with
    | 0 => .activate false
    | 1 => .activate true
    | _ => if view.network.inputs.any (fun input =>
        input.broadcaster && input.envelope.payload == 8) then
          .activate false else .wait)

private def e0 : app.Execution := .initial app ()
private def e1 : app.Execution := { e0 with environmentRecall :=
  [⟨e0.observeEnvironment app, .activate false⟩] }
private def e2 : app.Execution := e1.respond app false (send 7)
private def e3 : app.Execution := { e2 with
  network := e2.network.learn true {(false, 0)}
  environmentRecall := e2.environmentRecall ++ [⟨e2.observeEnvironment app,
    .activate true⟩] }
private def e4 : app.Execution := e3.respond app true (send 8)

private def kernel : app.ProtocolState → FinDist app.ProtocolState :=
  app.controlStep (FinDist.pure ()) 3 scheduler players

private theorem setup_step : kernel none = FinDist.pure (some ⟨3, none, e0⟩) := by
  simp only [kernel, ReactiveApplication.controlStep, ReactiveApplication.actor,
    Option.bind_none, ReactiveApplication.transition, FinDist.map_pure]
  rfl

private theorem activate_alice :
    kernel (some ⟨3, none, e0⟩) = FinDist.pure (some ⟨2, some false, e1⟩) := by
  simp only [kernel, ReactiveApplication.controlStep, ReactiveApplication.actor,
    Option.bind_some, ReactiveApplication.transition, scheduler, e0,
    ReactiveApplication.Execution.initial, List.length_nil, FinDist.pure_bind,
    ReactiveApplication.Execution.environmentStep, FinDist.map_pure]
  rw [show (MessageNetwork.empty.pending.map Message.id).toFinset =
    (∅ : Finset (MessageId Bool)) from rfl, MessageNetwork.learn_empty]
  rfl

private theorem alice_sends :
    kernel (some ⟨2, some false, e1⟩) = FinDist.pure (some ⟨2, none, e2⟩) := by
  simp only [kernel, ReactiveApplication.controlStep, ReactiveApplication.actor,
    Option.bind_some, players, Bool.false_eq_true, ↓reduceIte, FinDist.pure_bind,
    ReactiveApplication.transition, Option.getD_some]
  rfl

private theorem activate_bob :
    kernel (some ⟨2, none, e2⟩) = FinDist.pure (some ⟨1, some true, e3⟩) := by
  change (FinDist.pure (.activate true : app.Command)).bind _ = _
  simp only [FinDist.pure_bind, ReactiveApplication.Execution.environmentStep]
  change (((FinDist.pure {(false, 0)}).map _).map _).map _ = _
  simp only [FinDist.map_pure]
  rfl

private theorem bob_reacts :
    kernel (some ⟨1, some true, e3⟩) = FinDist.pure (some ⟨1, none, e4⟩) := by
  change (FinDist.pure (send 8)).bind _ = _
  rw [FinDist.pure_bind]
  rfl

/-- Actual canonical play reaches the received-message reaction. All messages
remain pending, and Alice is revisited only after the network sees Bob's reply. -/
theorem canonical_in_flight :
    ((app.information (FinDist.pure ()) 3 scheduler).runSingleMoverBehavioralFrom
      (app.singleMover (FinDist.pure ()) 3 scheduler)
      (fun who => app.encodePolicy (players who)) 5
      (app.protocol (FinDist.pure ()) 3 scheduler).initHistory).map
        ExecutionProtocol.History.state = FinDist.pure (some ⟨1, none, e4⟩) := by
  rw [app.run_map_state]
  change (fun law => law.bind kernel)^[5] (FinDist.pure none) = _
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, FinDist.pure_bind,
    setup_step, activate_alice, alice_sends, activate_bob, bob_reacts]

theorem reaction_before_inclusion :
    e4.network.pending = [⟨(false, 0), 7⟩, ⟨(true, 0), 8⟩] ∧
      e4.network.ledger = [] ∧ e4.receipts = [] ∧
      scheduler e4.environmentRecall (e4.observeEnvironment app) =
        FinDist.pure (.activate false) := ⟨rfl, rfl, rfl, rfl⟩

theorem replay_preserves_author_records_broadcaster :
    let next := e3.respond app true ⟨some (.replay (false, 0))⟩
    next.network.inputs = [⟨false, ⟨(false, 0), 7⟩⟩, ⟨true, ⟨(false, 0), 7⟩⟩] := rfl

/-- Even a rule selecting an own identifier cannot return that packet to its author. -/
theorem own_packet_is_not_a_leak :
    (e2.network.learn false {(false, 0)}).leaked false = [] := rfl

theorem redundant_observation_is_inert :
    e3.network.learn true {(false, 0)} = e3.network := by
  change MessageNetwork.mk _ _ _ _ _ = MessageNetwork.mk _ _ _ _ _
  congr 1
  funext who
  cases who <;> rfl

private abbrev partialApp : ReactiveApplication Bool :=
  { app with observePending := fun _ _ =>
      (FinDist.uniformOfFintype (α := Bool)).map fun bit =>
        if bit then {(false, 0)} else ∅ }

private def beforePartial : partialApp.Execution :=
  { application := (), network := e2.network, receipts := [], recall := fun _ => [],
    environmentRecall := [] }

private def afterPartial (bit : Bool) : partialApp.Execution :=
  { beforePartial with
    network := beforePartial.network.learn true (if bit then {(false, 0)} else ∅)
    environmentRecall := [⟨beforePartial.observeEnvironment partialApp, .activate true⟩] }

private theorem partial_activation :
    beforePartial.environmentStep partialApp (.activate true) =
      (FinDist.uniformOfFintype (α := Bool)).map afterPartial := by
  simp only [ReactiveApplication.Execution.environmentStep]
  rw [FinDist.map_comp, FinDist.map_comp]
  rfl

/-- Both learning and missing the packet are supported private outcomes. -/
theorem partial_outcomes (bit : Bool) :
    afterPartial bit ∈ (beforePartial.environmentStep partialApp (.activate true)).support := by
  rw [partial_activation, FinDist.support_map]
  exact ⟨bit, FinDist.mem_support_uniformOfFintype bit, rfl⟩

theorem partial_knowledge_differs :
    (afterPartial false).network.leaked true = [] ∧
      (afterPartial true).network.leaked true = [⟨(false, 0), 7⟩] := ⟨rfl, rfl⟩

/-- No scheduler can distinguish these samples through either view or recall. -/
theorem partial_observation_hidden (scheduler : partialApp.Scheduler) :
    scheduler (afterPartial false).environmentRecall
        ((afterPartial false).observeEnvironment partialApp) =
      scheduler (afterPartial true).environmentRecall
        ((afterPartial true).observeEnvironment partialApp) :=
  partialApp.scheduler_after_activation scheduler beforePartial _ _ true
    (partial_outcomes false) (partial_outcomes true)

end InteractionTests.ReactiveProtocol
