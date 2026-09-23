/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveEvaluation
import Interaction.ReactiveRecall

/-! # Network observation, repeated activation, and in-flight reactions

Alice sends a packet; Bob receives it and replies while the ledger is empty.
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
  Memory := Unit
  EnvironmentCommand := Empty
  LocalObservation := Unit
  PublicObservation := Unit
  packet := id
  submit state _ _ := state
  handle state _ := some state
  environment _ command := nomatch command
  observePlayer _ _ := ()
  observePublic _ := ()

private instance : Inhabited app.Memory := ⟨()⟩

private def send (value : Nat) : app.Action := ⟨(), some (.submit value)⟩

private def players : Bool → app.Policy := fun who _ view =>
  FinDist.pure (send (if who then
    (view.messages.inbox.head?.map Message.payload).getD 0 + 1 else 7))

/-- Later scheduling can depend on the actual incoming message, including
the broadcaster. The second Alice activation is an explicit network choice. -/
private def scheduler : app.Scheduler := fun history view =>
  FinDist.pure (match history.length with
    | 0 => .activate false
    | 1 => .deliver true (false, 0)
    | 2 => .activate true
    | _ => if view.network.inputs.any (fun input =>
        input.broadcaster && input.envelope.payload == 8) then
          .activate false else .wait)

private def e0 : app.Execution := .initial app ()
private def e1 : app.Execution := { e0 with environmentRecall :=
  [⟨e0.observeEnvironment app, .activate false⟩] }
private def e2 : app.Execution := e1.respond app false (send 7)
private def e3 : app.Execution := { e2 with
  network := e2.network.deliver true (false, 0)
  environmentRecall := e2.environmentRecall ++ [⟨e2.observeEnvironment app,
    .deliver true (false, 0)⟩] }
private def e4 : app.Execution := { e3 with environmentRecall := e3.environmentRecall ++
  [⟨e3.observeEnvironment app, .activate true⟩] }
private def e5 : app.Execution := e4.respond app true (send 8)

private def kernel : app.ProtocolState → FinDist app.ProtocolState :=
  app.controlStep (FinDist.pure ()) 4 scheduler players

private theorem setup_step : kernel none = FinDist.pure (some ⟨4, none, e0⟩) := by
  simp only [kernel, ReactiveApplication.controlStep, ReactiveApplication.actor,
    Option.bind_none, ReactiveApplication.transition, FinDist.map_pure]
  rfl

private theorem activate_alice :
    kernel (some ⟨4, none, e0⟩) = FinDist.pure (some ⟨3, some false, e1⟩) := by
  simp only [kernel, ReactiveApplication.controlStep, ReactiveApplication.actor,
    Option.bind_some, ReactiveApplication.transition, scheduler, e0,
    ReactiveApplication.Execution.initial, List.length_nil, FinDist.pure_bind,
    ReactiveApplication.Execution.environmentStep, FinDist.map_pure]
  rfl

private theorem alice_sends :
    kernel (some ⟨3, some false, e1⟩) = FinDist.pure (some ⟨3, none, e2⟩) := by
  simp only [kernel, ReactiveApplication.controlStep, ReactiveApplication.actor,
    Option.bind_some, players, Bool.false_eq_true, ↓reduceIte, FinDist.pure_bind,
    ReactiveApplication.transition, Option.getD_some]
  rfl

private theorem network_delivers :
    kernel (some ⟨3, none, e2⟩) = FinDist.pure (some ⟨2, none, e3⟩) := by
  change (FinDist.pure (.deliver true (false, 0) : app.Command)).bind _ = _
  simp only [FinDist.pure_bind, ReactiveApplication.Execution.environmentStep, FinDist.map_pure]
  rfl

private theorem activate_bob :
    kernel (some ⟨2, none, e3⟩) = FinDist.pure (some ⟨1, some true, e4⟩) := by
  change (FinDist.pure (.activate true : app.Command)).bind _ = _
  simp only [FinDist.pure_bind, ReactiveApplication.Execution.environmentStep, FinDist.map_pure]
  rfl

private theorem bob_reacts :
    kernel (some ⟨1, some true, e4⟩) = FinDist.pure (some ⟨1, none, e5⟩) := by
  change (FinDist.pure (send 8)).bind _ = _
  rw [FinDist.pure_bind]
  rfl

/-- Actual canonical play reaches the received-message reaction. All messages
remain pending, and Alice is revisited only after the network sees Bob's reply. -/
theorem canonical_in_flight :
    ((app.information (FinDist.pure ()) 4 scheduler).runSingleMoverBehavioralFrom
      (app.singleMover (FinDist.pure ()) 4 scheduler)
      (fun who => app.encodePolicy (players who)) 6
      (app.protocol (FinDist.pure ()) 4 scheduler).initHistory).map
        ExecutionProtocol.History.state = FinDist.pure (some ⟨1, none, e5⟩) := by
  rw [app.run_map_state]
  change (fun law => law.bind kernel)^[6] (FinDist.pure none) = _
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, FinDist.pure_bind,
    setup_step, activate_alice, alice_sends, network_delivers, activate_bob, bob_reacts]

theorem reaction_before_inclusion :
    e5.network.pending = [⟨(false, 0), 7⟩, ⟨(true, 0), 8⟩] ∧
      e5.network.ledger = [] ∧ e5.receipts = [] ∧
      scheduler e5.environmentRecall (e5.observeEnvironment app) =
        FinDist.pure (.activate false) := ⟨rfl, rfl, rfl, rfl⟩

theorem replay_preserves_author_records_broadcaster :
    let next := e3.respond app true ⟨(), some (.replay (false, 0))⟩
    next.network.inputs = [⟨false, ⟨(false, 0), 7⟩⟩, ⟨true, ⟨(false, 0), 7⟩⟩] := rfl

end InteractionTests.ReactiveProtocol
