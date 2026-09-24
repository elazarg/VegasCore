/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationGame
import Vegas.Pending.ReactiveFiniteResponses
import Vegas.Pending.ReactiveServiceSelection

/-! # Native service for the selective-association game

All six events are the compilation of the shared source program. Two ambient
responses precede reserved service: Alice may offer a candidate, then Bob may
observe that first envelope and respond arbitrarily. Each later visit gives
one owner response, includes its latest event-addressed packet, and settles
any remaining event by its ordinary timeout. Openings remain player choices.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

def nativeRuntime : EventGraphRuntime nativeGraph where
  deadline event := 2 ^ event.val

def nativeLeaks : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph) :=
  fun who _ => FinDist.pure (if who = bob then {(alice, 0)} else ∅)

abbrev nativeApp := nativeRuntime.reactiveApplication nativeLeaks

def nativeInputs : nativeGraph.Inputs := sourceSetup.eventInputs (Env.empty _)
def nativeInitial : State nativeGraph := State.initial nativeInputs

/-- Two prepared candidates suffice for Bob's earlier response and one fresh
correction. The raw alphabet also retains a value of the wrong game type. -/
def nativeBounds : MessageBounds nativeGraph where
  candidateCount := 2
  values := {⟨.bool, false⟩, ⟨.bool, true⟩, ⟨.int, 0⟩}

abbrev nativeMenu := nativeBounds.rawMenu nativeRuntime nativeLeaks

def nativeOwner (event : nativeGraph.EventId) : Player :=
  if event.val = 0 ∨ event.val = 3 then alice
  else if event.val = 1 ∨ event.val = 4 then carol
  else bob

theorem native_actor (event : nativeGraph.EventId) :
    nativeGraph.actor? event = some (nativeOwner event) := by
  fin_cases event <;> rfl

def nativeVisit (event : nativeGraph.EventId) : List (ServiceInstruction nativeGraph) :=
  [.grant event, .player (nativeOwner event), .includeLatest event (nativeOwner event)] ++
    List.replicate (nativeRuntime.deadline event) .tick ++ [.expire event]

def nativePlan : List (ServiceInstruction nativeGraph) :=
  [.player alice, .player bob] ++
    (List.finRange nativeGraph.order.eventCount).flatMap nativeVisit

def nativeNetwork : nativeRuntime.NetworkPolicy nativeLeaks :=
  fun _ _ => FinDist.pure .wait

def nativeScheduler : nativeApp.Scheduler := fun history view =>
  match nativePlan[history.length]? with
  | none => FinDist.pure .wait
  | some instruction => nativeRuntime.interactionInstruction nativeLeaks nativeNetwork
      history view instruction

abbrev nativeHorizon : Nat := nativePlan.length
abbrev nativeArena := nativeMenu.protocol (FinDist.pure nativeInitial)
  nativeHorizon nativeScheduler
abbrev nativeModel := nativeMenu.information (FinDist.pure nativeInitial)
  nativeHorizon nativeScheduler

theorem native_horizon : nativeHorizon = 89 := by decide
theorem native_ticks : serviceTicks nativePlan = 63 := by decide

def aliceBindingRef : EventGraph.FieldRef nativeGraph.layout (.binding alice .bool) :=
  ⟨.inr aliceBinding, rfl⟩
def carolBindingRef : EventGraph.FieldRef nativeGraph.layout (.binding carol .bool) :=
  ⟨.inr carolBinding, rfl⟩
def bobBindingRef : EventGraph.FieldRef nativeGraph.layout (.binding bob .bool) :=
  ⟨.inr bobBinding, rfl⟩
def alicePublicationRef : EventGraph.FieldRef nativeGraph.layout (.publication .bool) :=
  ⟨.inr alicePublication, rfl⟩
def carolPublicationRef : EventGraph.FieldRef nativeGraph.layout (.publication .bool) :=
  ⟨.inr carolPublication, rfl⟩
def bobPublicationRef : EventGraph.FieldRef nativeGraph.layout (.publication .bool) :=
  ⟨.inr bobPublication, rfl⟩

def nativeResults (config : nativeGraph.Config) : Results where
  alice := (alicePublicationRef.get? config.store).getD .failure
  bob := (bobPublicationRef.get? config.store).getD .failure
  carol := (carolPublicationRef.get? config.store).getD .failure

def nativeUtility (who : Player) (state : nativeApp.ProtocolState) : ℝ :=
  state.elim 0 (fun control => utility (nativeResults control.execution.application.config) who)

end VegasTests.SelectiveAssociation
