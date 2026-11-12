module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Interaction.ReactiveEvaluation

@[expose] public section

/-! # Canonical in-flight reactions and authenticated network recall

Alice sends a packet; Bob privately observes it and replies before inclusion.
The scheduler sees Bob's actual output and can revisit Alice. These are steps
of the canonical reactive protocol, with one response per activation.
-/

noncomputable section

namespace InteractionTests.ReactiveProtocol

open Interaction GameTheory.Protocol GameTheory.Math.Probability

abbrev app : ReactiveApplication Bool where
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
  observePending _ pending := PMF.pure (pending.map Message.id).toFinset

def send (value : Nat) : app.Action := ⟨some value⟩

def players : Bool → app.Policy := fun who _ view =>
  PMF.pure (send (if who then
    (view.messages.leaked.head?.map Message.payload).getD 0 + 1 else 7))

def scheduler : app.Scheduler := fun history view =>
  PMF.pure (match history.length with
    | 0 => .activate false
    | 1 => .activate true
    | _ => if view.network.inputs.any (fun input =>
        input.sender && input.payload == 8) then .activate false else .wait)

def e0 : app.Execution := .initial app ()
def e1 : app.Execution := { e0 with environmentRecall :=
  [⟨e0.observeEnvironment app, .activate false⟩] }
def e2 : app.Execution := e1.respond app false (send 7)
def e3 : app.Execution := { e2 with
  network := e2.network.learn true {(false, 0)}
  environmentRecall := e2.environmentRecall ++ [⟨e2.observeEnvironment app, .activate true⟩] }
def e4 : app.Execution := e3.respond app true (send 8)

def kernel : app.ProtocolState → PMF app.ProtocolState :=
  app.controlStep (PMF.pure ()) 3 scheduler players

private theorem setup_step : kernel none = PMF.pure (some ⟨3, none, e0⟩) := by
  simp only [kernel, ReactiveApplication.controlStep, ReactiveApplication.actor,
    Option.bind_none, ReactiveApplication.transition, PMF.pure_map]
  rfl

private theorem activate_alice :
    kernel (some ⟨3, none, e0⟩) = PMF.pure (some ⟨2, some false, e1⟩) := by
  simp only [kernel, ReactiveApplication.controlStep, ReactiveApplication.actor,
    Option.bind_some, ReactiveApplication.transition, scheduler, e0,
    ReactiveApplication.Execution.initial, List.length_nil, PMF.pure_bind,
    ReactiveApplication.Execution.environmentStep, PMF.pure_map]
  rw [show (MessageNetwork.empty.pending.map Message.id).toFinset =
    (∅ : Finset (MessageId Bool)) from rfl, MessageNetwork.learn_empty]
  rfl

private theorem alice_sends :
    kernel (some ⟨2, some false, e1⟩) = PMF.pure (some ⟨2, none, e2⟩) := by
  simp only [kernel, ReactiveApplication.controlStep, ReactiveApplication.actor,
    Option.bind_some, players, Bool.false_eq_true, ↓reduceIte, PMF.pure_bind,
    ReactiveApplication.transition, Option.getD_some]
  rfl

private theorem activate_bob :
    kernel (some ⟨2, none, e2⟩) = PMF.pure (some ⟨1, some true, e3⟩) := by
  change (PMF.pure (.activate true : app.Command)).bind _ = _
  simp only [PMF.pure_bind, ReactiveApplication.Execution.environmentStep]
  change (((PMF.pure {(false, 0)}).map _).map _).map _ = _
  simp only [PMF.pure_map]
  rfl

private theorem bob_reacts :
    kernel (some ⟨1, some true, e3⟩) = PMF.pure (some ⟨1, none, e4⟩) := by
  change (PMF.pure (send 8)).bind _ = _
  rw [PMF.pure_bind]
  rfl

/-- Actual canonical play reaches Bob's received-message response before any inclusion. -/
theorem canonical_in_flight :
    ((app.information (PMF.pure ()) 3 scheduler).runSingleMoverBehavioralFrom
      (app.singleMover (PMF.pure ()) 3 scheduler)
      (fun who => app.encodePolicy (players who)) 5
      (app.protocol (PMF.pure ()) 3 scheduler).initHistory).map
        ExecutionProtocol.History.state = PMF.pure (some ⟨1, none, e4⟩) := by
  rw [app.run_map_state]
  change (fun law => law.bind kernel)^[5] (PMF.pure none) = _
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, PMF.pure_bind,
    setup_step, activate_alice, alice_sends, activate_bob, bob_reacts]

theorem reaction_before_inclusion :
    e4.network.pending = [⟨(false, 0), 7⟩, ⟨(true, 0), 8⟩] ∧
      e4.network.ledger = [] ∧ e4.receipts = [] ∧
      scheduler e4.environmentRecall (e4.observeEnvironment app) =
        PMF.pure (.activate false) := ⟨rfl, rfl, rfl, rfl⟩

/-- Every authored envelope appears once in submission order. -/
theorem inputs_record_submissions :
    e4.network.inputs = [⟨(false, 0), 7⟩, ⟨(true, 0), 8⟩] := rfl

/-- Selecting an own identifier cannot return that packet as foreign knowledge. -/
theorem own_packet_is_not_a_leak :
    (e2.network.learn false {(false, 0)}).leaked false = [] := rfl

theorem redundant_observation_is_inert :
    e3.network.learn true {(false, 0)} = e3.network := by
  change MessageNetwork.mk _ _ _ _ _ = MessageNetwork.mk _ _ _ _ _
  congr 1
  funext who
  cases who <;> rfl

end InteractionTests.ReactiveProtocol
