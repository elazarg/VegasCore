/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedRelease
import Interaction.SealedControllerTrace
import Vegas.Game.SealedRelease
import Vegas.Compile.SealedSource
import VegasTests.PendingPolicies

/-! # The compiled release controller in complete native policy executions

The protected owner registers and submits from the empty state, then polls
the existing public-view opening controller. Invocation schedules may continue
to invoke that owner. Hiding concerns the first release-enabled snapshot of a
complete trace, not the observations after an opening is submitted.
-/

namespace VegasTests.PendingRelease

noncomputable section

open Interaction Interaction.SealedProgram GameTheory GameTheory.Math.Probability
open VegasTests.PendingSource VegasTests.PendingExecution VegasTests.PendingPolicies
open Interaction.MessageApplication

def release (events : List (Event Player Value)) : Bool :=
  openingReady program events 0 2

def releaseSnapshot (execution : Application.PolicyExecution) : Bool :=
  release execution.native.application.events

theorem release_requires_both (events : List (Event Player Value))
    (hrelease : release events = true) :
    done events 0 = true ∧ done events 1 = true := by
  let view : Application.View :=
    ⟨(MessagePool.empty Player (Payload Player Value)).observe 0, events, []⟩
  have hcommand := (openingCommand_ne_wait_iff_ready program 0 2 (none : Value) view).2
    hrelease
  have hprereqs := sealedFragment.openingCommand_prerequisites 0 (node 2) none view hcommand
  exact ⟨hprereqs (node 0) (by rw [node2_prereqs]; simp),
    hprereqs (node 1) (by rw [node2_prereqs]; simp)⟩

def controllerProfile (value : Value)
    (players : Profile (MessageApplication.policySignature Player Application)) :
    Profile (MessageApplication.policySignature Player Application) :=
  Profile.update players 0 (commitOpenPolicy program 0 0 2 value)

def openingProfile (value : Value)
    (players : Profile (MessageApplication.policySignature Player Application)) :
    Profile (MessageApplication.policySignature Player Application) :=
  Profile.update players 0 (openingPolicy program 0 2 value)

def controllerTraceLaw (value : Value)
    (players : Profile (MessageApplication.policySignature Player Application))
    (environment : Application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player)) :
    FinDist (Application.PolicyTrace) :=
  Application.tracePolicies (controllerProfile value players) environment
    (.player 0 :: .player 0 :: schedule) (initialExecution)

/-- The trace law is a recording of the ordinary native game, including its
post-release suffix and any further owner invocations. -/
theorem controllerTraceLaw_last (value : Value)
    (players : Profile (MessageApplication.policySignature Player Application))
    (environment : Application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player)) :
    (controllerTraceLaw value players environment schedule).map PolicyTrace.last =
      (Application.policyGame environment
        (.player 0 :: .player 0 :: schedule) applicationInitial).play
        (controllerProfile value players) :=
  Application.tracePolicies_last _ environment _ _

theorem openingTraceLaw_hiding (left right : Value)
    (players : Profile (MessageApplication.policySignature Player Application))
    (environment : Application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player)) :
    ((Application.tracePolicies (openingProfile left players)
      environment schedule (prepared left)).map (PolicyTrace.firstRelease releaseSnapshot)).map
        (program.applicationObservations 0) =
      ((Application.tracePolicies (openingProfile right players)
        environment schedule (prepared right)).map (PolicyTrace.firstRelease releaseSnapshot)).map
          (program.applicationObservations 0) := by
  apply tracePolicies_hiding_beforeRelease
  · intro who hne
    simp only [openingProfile, Profile.update_of_ne _ _ hne]
  · simpa only [openingProfile, Profile.update_same, WaitsBeforeRelease,
      release, openingReady] using
      openingPolicy_waitsBefore program 0 2 left
  · simpa only [openingProfile, Profile.update_same, WaitsBeforeRelease,
      release, openingReady] using
      openingPolicy_waitsBefore program 0 2 right
  · exact prepared_related left right

theorem controllerTraceLaw_firstRelease (value : Value)
    (players : Profile (MessageApplication.policySignature Player Application))
    (environment : Application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player)) :
    (controllerTraceLaw value players environment schedule).map
        (PolicyTrace.firstRelease releaseSnapshot) =
      (Application.tracePolicies (openingProfile value players)
        environment schedule (prepared value)).map (PolicyTrace.firstRelease releaseSnapshot) := by
  have hregister : Application.invoke (controllerProfile value players) environment
      initialExecution (.player 0) = FinDist.pure (registered value) := by
    simp [MessageApplication.invoke, controllerProfile, Profile.update_same, commitOpenPolicy,
      initialExecution, registered, registeredState, registerCommand,
      MessageApplication.playerStep, MessageApplication.advance,
      MessageApplication.PlayerCommand.toAction, MessageApplication.step,
      MessageApplication.PolicyExecution.initial, MessageApplication.State.initial,
      applicationInitial, Application, SealedProgram.messageApplication]
  have hsubmit : Application.invoke (controllerProfile value players) environment
      (registered value) (.player 0) = FinDist.pure (prepared value) := by
    simp [MessageApplication.invoke, controllerProfile, Profile.update_same, commitOpenPolicy,
      registered, prepared, submitCommand,
      MessageApplication.playerStep, MessageApplication.advance,
      MessageApplication.PlayerCommand.toAction, MessageApplication.step]
  unfold controllerTraceLaw
  rw [Application.tracePolicies_firstRelease_cons]
  simp only [show releaseSnapshot initialExecution = false from rfl,
    Bool.false_eq_true, ↓reduceIte, hregister, FinDist.pure_bind]
  rw [Application.tracePolicies_firstRelease_cons]
  simp only [show releaseSnapshot (registered value) = false from rfl,
    Bool.false_eq_true, ↓reduceIte, hsubmit, FinDist.pure_bind]
  rw [controllerProfile, tracePolicies_commitOpen_eq_opening_of_two_le program environment
    schedule (prepared value) players 0 0 2 value (by simp [prepared, registered])]
  rfl

/-- Empty-state controller runs have the same observations at the first
compiled release boundary for every fixed schedule, including owner polls.
Both full executions continue after the compared snapshot. -/
theorem controllerTraceLaw_hiding (left right : Value)
    (players : Profile (MessageApplication.policySignature Player Application))
    (environment : Application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player)) :
    ((controllerTraceLaw left players environment schedule).map
      (PolicyTrace.firstRelease releaseSnapshot)).map (program.applicationObservations 0) =
      ((controllerTraceLaw right players environment schedule).map
        (PolicyTrace.firstRelease releaseSnapshot)).map (program.applicationObservations 0) := by
  rw [controllerTraceLaw_firstRelease, controllerTraceLaw_firstRelease]
  exact openingTraceLaw_hiding left right players environment schedule

/-- Every cutoff is a genuine policy execution prefix of the compiled checked
source, not a fabricated state in a stopped runtime. -/
theorem controllerTraceLaw_cut_reachable (value : Value)
    (players : Profile (MessageApplication.policySignature Player Application))
    (environment : Application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (trace : Application.PolicyTrace)
    (htrace : trace ∈ (controllerTraceLaw value players environment schedule).support) :
    ∃ cfg : Vegas.EventGraph.Config graph,
      graph.decodeSealed (.option .bool)
        (program.eraseReceipts (trace.firstRelease releaseSnapshot).native) = some cfg ∧
        Vegas.EventGraph.Reachable graph cfg := by
  obtain ⟨front, _suffix, _hsplit, hcut, _⟩ := Application.tracePolicies_firstRelease_split
    (controllerProfile value players) environment releaseSnapshot
      (.player 0 :: .player 0 :: schedule) initialExecution trace htrace
  obtain ⟨cfg, hdecode, hreachable, _⟩ := source.sealed_policy_source
    (.option .bool) sealedFragment (controllerProfile value players) environment front
      (trace.firstRelease releaseSnapshot) hcut
  exact ⟨cfg, hdecode, hreachable⟩

end

end VegasTests.PendingRelease

/-- info: 'Interaction.SealedProgram.tracePolicies_hiding_beforeRelease' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedProgram.tracePolicies_hiding_beforeRelease

/-- info: 'VegasTests.PendingRelease.controllerTraceLaw_hiding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PendingRelease.controllerTraceLaw_hiding

/-- info: 'Vegas.EventGraph.SealedFragment.openingCommand_prerequisites' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.openingCommand_prerequisites
