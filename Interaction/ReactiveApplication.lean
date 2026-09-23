/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageNetwork
import GameTheory.Math.Probability.FinDist

/-! # One optional transmission per player activation

An application supplies atomic submission and inclusion semantics. A player's
choice retains private memory and may submit or replay one envelope. Only the
public envelope and broadcaster enter the network input history. The scheduler
can activate a player again after observing that output.
-/

namespace Interaction

open GameTheory.Math.Probability

structure ReactiveApplication (Principal : Type) where
  State : Type
  Payload : Type
  Submission : Type
  Memory : Type
  EnvironmentCommand : Type
  LocalObservation : Type
  PublicObservation : Type
  packet : Submission → Payload
  submit : State → Principal → Submission → State
  handle : State → Message Principal Payload → Option State
  environment : State → EnvironmentCommand → FinDist State
  observePlayer : State → Principal → LocalObservation
  observePublic : State → PublicObservation

namespace ReactiveApplication

variable {Principal : Type} (app : ReactiveApplication Principal)

inductive Transmission where
  | submit (submission : app.Submission)
  | replay (id : MessageId Principal)

structure Action where
  memory : app.Memory
  transmission : Option app.Transmission

structure PlayerView where
  messages : MessageNetwork.PlayerView Principal app.Payload
  application : app.LocalObservation
  receipts : List (MessageId Principal × Bool)

structure PlayerEntry where
  beforeView : app.PlayerView
  action : app.Action
  emitted : Option (Message Principal app.Payload)

structure EnvironmentView where
  network : MessageNetwork Principal app.Payload
  application : app.PublicObservation
  receipts : List (MessageId Principal × Bool)

inductive Command where
  | activate (who : Principal)
  | deliver (who : Principal) (id : MessageId Principal)
  | include (id : MessageId Principal)
  | application (command : app.EnvironmentCommand)
  | wait

structure EnvironmentEntry where
  beforeView : app.EnvironmentView
  command : app.Command

structure Execution where
  application : app.State
  network : MessageNetwork Principal app.Payload
  receipts : List (MessageId Principal × Bool)
  recall : Principal → List app.PlayerEntry
  environmentRecall : List app.EnvironmentEntry

def Execution.initial (state : app.State) : app.Execution :=
  ⟨state, .empty, [], fun _ => [], []⟩

def Execution.observe (execution : app.Execution) (who : Principal) : app.PlayerView :=
  ⟨execution.network.observe who, app.observePlayer execution.application who, execution.receipts⟩

def Execution.observeEnvironment (execution : app.Execution) : app.EnvironmentView :=
  ⟨execution.network, app.observePublic execution.application, execution.receipts⟩

abbrev Policy := List app.PlayerEntry → app.PlayerView → FinDist app.Action
abbrev Scheduler := List app.EnvironmentEntry → app.EnvironmentView → FinDist app.Command

variable [DecidableEq Principal]

/-- Application submission and its envelope are one transition. The emitted
packet is part of the player's own recall; private material never enters the network. -/
def Execution.respond (execution : app.Execution) (who : Principal) (action : app.Action) :
    app.Execution :=
  let (state, emitted, network) := match action.transmission with
    | none => (execution.application, none, execution.network)
    | some (.submit submission) =>
        let (envelope, network) := execution.network.submit who (app.packet submission)
        (app.submit execution.application who submission, some envelope, network)
    | some (.replay id) =>
        let (emitted, network) := execution.network.replay who id
        (execution.application, emitted, network)
  { execution with
    application := state
    network := network
    recall := fun observer => if observer = who then execution.recall who ++
      [⟨execution.observe app who, action, emitted⟩] else execution.recall observer }

def Execution.includePending (execution : app.Execution) (id : MessageId Principal) :
    app.Execution :=
  let (envelope, network) := execution.network.includePending id
  match envelope with
  | none => { execution with network := network }
  | some envelope =>
      let result := app.handle execution.application envelope
      { execution with
        network := network
        application := result.getD execution.application
        receipts := execution.receipts ++ [(id, result.isSome)] }

noncomputable def Execution.environmentStep (execution : app.Execution) (command : app.Command) :
    FinDist app.Execution :=
  let law := match command with
    | .activate _ | .wait => FinDist.pure execution
    | .deliver who id => FinDist.pure
        { execution with network := execution.network.deliver who id }
    | .include id => FinDist.pure (execution.includePending app id)
    | .application command => (app.environment execution.application command).map fun state =>
        { execution with application := state }
  law.map fun next => { next with environmentRecall := execution.environmentRecall ++
    [⟨execution.observeEnvironment app, command⟩] }

end ReactiveApplication
end Interaction
