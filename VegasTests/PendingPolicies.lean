/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedApplicationHiding
import Vegas.Game.SealedMessages
import VegasTests.PendingExecution

/-! # Policies over the shared checked message application -/

namespace VegasTests.PendingPolicies

open Interaction Interaction.MessageApplication Interaction.SealedProgram
open GameTheory.Math.Probability
open VegasTests.PendingSource VegasTests.PendingExecution

noncomputable section

abbrev Application := program.messageApplication (Value := Value)
abbrev PolicyExecution := Application.PolicyExecution
abbrev PlayerPolicy := Application.PlayerPolicy
abbrev EnvironmentPolicy := Application.EnvironmentPolicy

def applicationInitial : Application.State :=
  MessageApplication.State.initial Application ⟨IdealCommitments.empty, []⟩

def initialExecution : PolicyExecution :=
  MessageApplication.PolicyExecution.initial Application applicationInitial

def registerCommand (value : Value) : Application.PlayerCommand :=
  .privateCommand ⟨(0, value)⟩

def submitCommand : Application.PlayerCommand := .submit (.commitment 0 (0, 0))

def registeredState (value : Value) : Application.State :=
  { applicationInitial with
    application :=
      { service := (IdealCommitments.empty.sealValue 0 0 value).state, events := [] } }

def registered (value : Value) : PolicyExecution :=
  { initialExecution with
    native := registeredState value
    principalHistory := fun who =>
      if who = 0 then
        [⟨MessageApplication.State.observe Application applicationInitial 0,
          registerCommand value⟩]
      else []
    nativeTrace := [.privateCommand 0 ⟨(0, value)⟩] }

def prepared (value : Value) : PolicyExecution :=
  { registered value with
    native := { (registered value).native with pool :=
      ((registered value).native.pool.submit 0 (.commitment 0 (0, 0))).2 }
    principalHistory := fun who =>
      if who = 0 then
        (registered value).principalHistory 0 ++
          [⟨MessageApplication.State.observe Application (registered value).native 0,
            submitCommand⟩]
      else (registered value).principalHistory who
    nativeTrace := (registered value).nativeTrace ++ [.submit 0 (.commitment 0 (0, 0))] }

theorem prepared_native (value : Value) :
    program.eraseReceipts (prepared value).native = (submitCommit initial 0 0 value).2 := rfl

def sealPolicy (value : Value) : PlayerPolicy := fun history _ =>
  match history.length with
  | 0 => FinDist.pure (registerCommand value)
  | 1 => FinDist.pure submitCommand
  | _ => FinDist.pure .wait

def ownerPlayers (players : Player → PlayerPolicy) (value : Value) : Player → PlayerPolicy :=
  fun who => if who = 0 then sealPolicy value else players who

def sealedLaw (value : Value) (players : Player → PlayerPolicy)
    (environment : EnvironmentPolicy) (schedule : List (@MessageApplication.Invocation Player)) :
    FinDist PolicyExecution :=
  (MessageApplication.policyGame Application environment
    (.player 0 :: .player 0 :: schedule) applicationInitial).play
      (ownerPlayers players value)

theorem sealed_prefix (value : Value) (players : Player → PlayerPolicy)
    (environment : EnvironmentPolicy) :
    Application.runPolicies (ownerPlayers players value) environment
      [.player 0, .player 0] initialExecution = FinDist.pure (prepared value) := by
  simp [MessageApplication.runPolicies, MessageApplication.invoke, sealPolicy,
    ownerPlayers, registerCommand, submitCommand, initialExecution, registered,
    registeredState, prepared,
    MessageApplication.playerStep, MessageApplication.advance,
    MessageApplication.PlayerCommand.toAction, MessageApplication.step,
    MessageApplication.PolicyExecution.initial, MessageApplication.State.initial,
    applicationInitial, Application, SealedProgram.messageApplication]

theorem sealedLaw_eq_continuation (value : Value) (players : Player → PlayerPolicy)
    (environment : EnvironmentPolicy) (schedule : List (@MessageApplication.Invocation Player))
    (hschedule : ∀ who, MessageApplication.Invocation.player who ∈ schedule →
      who ≠ (0 : Player)) :
    sealedLaw value players environment schedule =
      Application.runPolicies players environment schedule (prepared value) := by
  simp only [sealedLaw, MessageApplication.policyGame]
  change Application.runPolicies (ownerPlayers players value) environment
    (.player 0 :: .player 0 :: schedule) initialExecution = _
  rw [show (.player 0 :: .player 0 :: schedule) = [.player 0, .player 0] ++ schedule by rfl,
    MessageApplication.runPolicies_append, sealed_prefix, FinDist.pure_bind]
  apply MessageApplication.runPolicies_congr_on_schedule Application
    (ownerPlayers players value) players environment schedule
    (prepared value)
  intro who hmem
  simp [ownerPlayers, hschedule who hmem]

theorem prepared_related (left right : Value) :
    ApplicationPolicyRelated program (0 : Player) (prepared left) (prepared right) := by
  refine ⟨⟨?_, rfl⟩, ?_, rfl⟩
  · simpa only [prepared_native, initial, SealedProgram.State.empty] using
      submitCommit_empty_related 0 0 left right
  · intro who hne
    simp [prepared, registered, hne]

theorem sealedLaw_hiding (left right : Value) (players : Player → PlayerPolicy)
    (environment : EnvironmentPolicy) (schedule : List (@MessageApplication.Invocation Player))
    (hschedule : ∀ who, MessageApplication.Invocation.player who ∈ schedule →
      who ≠ (0 : Player)) :
    (sealedLaw left players environment schedule).map (program.applicationObservations 0) =
      (sealedLaw right players environment schedule).map
        (program.applicationObservations 0) := by
  rw [sealedLaw_eq_continuation left players environment schedule hschedule,
    sealedLaw_eq_continuation right players environment schedule hschedule]
  exact runApplicationPolicies_hiding (program := program) (Value := Value)
    players environment schedule
    (prepared_related left right) hschedule

theorem sealedLaw_reachable (value : Value) (players : Player → PlayerPolicy)
    (environment : EnvironmentPolicy) (schedule : List (@MessageApplication.Invocation Player))
    (execution : PolicyExecution)
    (hmem : execution ∈ (sealedLaw value players environment schedule).support) :
    ∃ cfg : Vegas.EventGraph.Config graph,
      graph.decodeSealed (.option .bool) (program.eraseReceipts execution.native) = some cfg ∧
        Vegas.EventGraph.Reachable graph cfg := by
  obtain ⟨cfg, hdecode, hreachable, _⟩ := source.sealed_policy_source
    (.option .bool) sealedFragment
      (ownerPlayers players value) environment
      (.player 0 :: .player 0 :: schedule) execution hmem
  exact ⟨cfg, hdecode, hreachable⟩

def copyCleartext : PlayerPolicy := fun _ view =>
  match view.messages.inbox.head? with
  | some ⟨_, .cleartext _ value⟩ => FinDist.pure (.submit (.cleartext 1 value))
  | _ => FinDist.pure .wait

def deliverFirst : EnvironmentPolicy := fun _ _ => FinDist.pure (.deliver 1 (0, 0))

def disclosePolicy (value : Value) : PlayerPolicy := fun _ _ =>
  FinDist.pure (.submit (.cleartext 0 value))

def cleartextPlayers (value : Value) : Player → PlayerPolicy := fun who =>
  if who = 0 then disclosePolicy value else copyCleartext

def cleartextResponseLaw (value : Value) : FinDist PolicyExecution :=
  (MessageApplication.policyGame Application deliverFirst
    [.player 0, .environment, .player 1] applicationInitial).play
      (cleartextPlayers value)

theorem cleartextResponseLaw_sent (value : Value) :
    (cleartextResponseLaw value).map (fun execution => execution.native.pool.sent 1) =
      FinDist.pure [⟨(1, 0), Payload.cleartext 1 value⟩] := by
  simp [cleartextResponseLaw, MessageApplication.policyGame,
    MessageApplication.runPolicies, MessageApplication.invoke, deliverFirst,
    copyCleartext, disclosePolicy, cleartextPlayers, MessageApplication.environmentPolicyStep,
    MessageApplication.playerStep, MessageApplication.advance,
    MessageApplication.EnvironmentPolicyCommand.toAction,
    MessageApplication.PlayerCommand.toAction, MessageApplication.step,
    MessageApplication.PolicyExecution.initial, MessageApplication.State.initial,
    applicationInitial,
    MessageApplication.State.observe, MessageApplication.State.environmentView,
    MessagePool.observe, MessagePool.empty, MessagePool.submit, MessagePool.deliver,
    MessagePool.lookup, FinDist.pure_bind, FinDist.map_pure]

theorem cleartextResponseLaw_distinguishes (left right : Value) (hne : left ≠ right) :
    (cleartextResponseLaw left).map (fun execution => execution.native.pool.sent 1) ≠
      (cleartextResponseLaw right).map (fun execution => execution.native.pool.sent 1) := by
  rw [cleartextResponseLaw_sent, cleartextResponseLaw_sent]
  intro heq
  have hmem : [⟨(1, 0), Payload.cleartext 1 left⟩] ∈
      (FinDist.pure [⟨(1, 0), Payload.cleartext 1 left⟩] :
        FinDist (List (Message Player (Payload Player Value)))).support :=
    FinDist.mem_support_pure.mpr rfl
  have hmem' : [⟨(1, 0), Payload.cleartext 1 left⟩] ∈
      (FinDist.pure [⟨(1, 0), Payload.cleartext 1 right⟩] :
        FinDist (List (Message Player (Payload Player Value)))).support := by
    exact congrArg FinDist.support heq ▸ hmem
  have hlist := FinDist.mem_support_pure.mp hmem'
  have hpayload := congrArg Message.payload (List.cons.inj hlist).1
  cases hpayload
  exact hne rfl

end
end VegasTests.PendingPolicies

/-- info: 'Vegas.WFProgram.sealed_policy_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WFProgram.sealed_policy_source

/-- info: 'VegasTests.PendingPolicies.sealedLaw_hiding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PendingPolicies.sealedLaw_hiding
