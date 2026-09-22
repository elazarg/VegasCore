/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicies
import GameTheory.Core.UtilitySimulation

/-! # The message pool is a coalition channel

Nature draws a secret, the first principal alone observes it, and a player is
paid for guessing it. The base game offers no way to learn the draw, so every
base profile is worth one half.

The host runs the same draw through the generic message application. Its
`handle` rejects every message, so no payload ever reaches application state:
the channel is the pool itself. The first principal submits a message carrying
the secret, the wire delivers it before any inclusion, and the second principal
reads it out of its inbox and guesses. That pair is worth one.

`GameTheory.GameForm.UtilitySimulation.isEmpty_of_grandCoalitionValue` then rules out every
coalition certificate relating the base game to this host, whatever the
strategy translation. This is the concrete form of the abstract channel in
`GameTheory.GameForm.CoalitionWitness`: an ordinary message pool, with
pre-inclusion delivery, implements exactly that channel.

Scope: only the coalition half is checked here. That a lone deviator gains
nothing against compiled opponents is exhibited abstractly in
`GameTheory.GameForm.CoalitionWitness.unilateralSimulation`, and for the Vegas
runtime it is the content of the proved unilateral laws. This file does not
repeat it for the host.
-/

namespace InteractionTests.CoalitionChannel

open Interaction GameTheory GameTheory.Math.Probability

noncomputable section

abbrev Principal := Fin 2

inductive Payload where
  | bit (value : Bool)
  deriving DecidableEq

inductive PrivateCommand where
  | guess (value : Bool)

inductive EnvironmentCommand where
  | noop

structure Application where
  secret : Bool
  guess : Option Bool
  deriving DecidableEq

/-- What a principal knows about the secret. -/
structure PlayerView where
  secret : Option Bool
  deriving DecidableEq

def fair : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num) (FinDist.pure false) (FinDist.pure true)

def privateStep (state : Application) (who : Principal) :
    PrivateCommand → Application
  | .guess value =>
      if who = 1 ∧ state.guess.isNone then { state with guess := some value } else state

def environmentStep (state : Application) : EnvironmentCommand → FinDist Application
  | .noop => FinDist.pure state

/-- Every message is rejected, so no payload reaches application state. -/
def handle (_ : Application) (_ : Message Principal Payload) : Option Application := none

/-- Only the first principal observes the secret. -/
def observe (state : Application) (who : Principal) : PlayerView :=
  ⟨if who = 0 then some state.secret else none⟩

def channel : MessageApplication Principal where
  Application := Application
  Payload := Payload
  PrivateCommand := PrivateCommand
  EnvironmentCommand := EnvironmentCommand
  PlayerView := PlayerView
  EnvironmentView := Unit
  privateStep := privateStep
  submitStep := fun state _ _ => state
  environmentStep := environmentStep
  handle := handle
  observePlayer := observe
  observeEnvironment := fun _ => ()

def initialState (secret : Bool) : channel.State :=
  MessageApplication.State.initial channel ⟨secret, none⟩

/-- The wire delivers the first principal's message before any inclusion. -/
def environmentPolicy : channel.EnvironmentPolicy :=
  fun _ _ => FinDist.pure (.deliver 1 (0, 0))

/-- Signal, deliver, guess. -/
def schedule : List (@MessageApplication.Invocation Principal) :=
  [.player 0, .environment, .player 1]

/-- Nature draws the secret before the host runs, as a source setup does. -/
def hostGame : GameForm Principal where
  sig := MessageApplication.policySignature Principal channel
  play players := fair.bind fun secret =>
    MessageApplication.runPolicies channel players environmentPolicy schedule
      (MessageApplication.PolicyExecution.initial channel (initialState secret))

def hostUtility (execution : channel.PolicyExecution) (_ : Principal) : ℝ :=
  if execution.native.application.guess = some execution.native.application.secret then 1 else 0

/-- The base game: the same draw, guessed without any observation. -/
abbrev baseGame : GameForm Principal where
  sig := { Strategy := fun _ => Bool, Outcome := Bool × Bool }
  play profile := fair.map fun secret => (secret, profile 1)

def baseUtility (outcome : Bool × Bool) (_ : Principal) : ℝ :=
  if outcome.1 = outcome.2 then 1 else 0

/-- A guess that cannot depend on the draw is right half the time. -/
theorem base_expect (profile : Profile baseGame.sig) (who : Principal) :
    (baseGame.play profile).expect (fun outcome => baseUtility outcome who) = 1 / 2 := by
  cases h : profile 1 <;>
    norm_num [fair, baseUtility, FinDist.expect_map, FinDist.expect_mix, h]

/-- The first principal writes the secret onto the wire. -/
def signalPolicy : channel.PlayerPolicy :=
  fun _ view => FinDist.pure <|
    match view.application.secret with
    | some value => .submit (.bit value)
    | none => .wait

/-- The second principal reads its inbox and guesses what it finds. -/
def copyPolicy : channel.PlayerPolicy :=
  fun _ view => FinDist.pure <|
    match view.messages.inbox with
    | message :: _ => match message.payload with
      | .bit value => .privateCommand (.guess value)
    | [] => .wait

def collusion : Profile hostGame.sig :=
  fun who => if who = 0 then signalPolicy else copyPolicy

/-- The pair always guesses the secret, so the coalition is worth one. -/
theorem collusion_expect (who : Principal) :
    (hostGame.play collusion).expect (fun execution => hostUtility execution who) = 1 := by
  change FinDist.expect (fair.bind fun secret =>
      MessageApplication.runPolicies channel collusion environmentPolicy schedule
        (MessageApplication.PolicyExecution.initial channel (initialState secret)))
    (fun execution => hostUtility execution who) = 1
  rw [FinDist.expect_bind, fair, FinDist.expect_mix]
  simp [schedule, MessageApplication.runPolicies, MessageApplication.invoke,
    environmentPolicy, collusion, signalPolicy, copyPolicy, MessageApplication.playerStep,
    MessageApplication.environmentPolicyStep, MessageApplication.advance,
    MessageApplication.step, MessageApplication.State.initial, MessageApplication.State.observe,
    MessageApplication.PolicyExecution.initial, MessageApplication.PlayerCommand.toAction,
    MessageApplication.EnvironmentPolicyCommand.toAction, channel, observe, privateStep,
    initialState, MessagePool.submit, MessagePool.deliver, MessagePool.observe,
    MessagePool.empty, MessagePool.lookup, MessageApplication.includePending, hostUtility]

/-- No coalition certificate relates the base game to the host, for any strategy
translation. The pool carries the secret across a coalition that the base game
cannot correlate at all. -/
theorem isEmpty_coalitionSimulation :
    IsEmpty (GameForm.UtilitySimulation baseGame hostGame baseUtility hostUtility
      (GameTheory.nonemptyGroups Principal)) :=
  GameForm.UtilitySimulation.isEmpty_of_grandCoalitionValue Finset.univ_nonempty
    (fun _ => false) 0 collusion (1 / 2)
    (fun profile => le_of_eq (base_expect profile 0))
    (by rw [collusion_expect]; norm_num)

end

end InteractionTests.CoalitionChannel
