/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveRuntime
import Interaction.ReactivePublication

/-! # Reserved service with one owner activation

A network opportunity can activate any player, include a packet, or wait.
Activation samples private observations using a separate rule. Those samples
are absent from scheduler state and recall.
Application grants, sampling, clock ticks, and expiry remain controlled by the
service contract. Each strategic visit reserves one owner activation followed
by network opportunities and event-addressed inclusion. There is no reaction
roster and no private preparation phase.
Each envelope can be included at most once, including when its call is rejected.
Players may rebroadcast it; retrying a call requires a fresh envelope.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

inductive NetworkChoice (Player : Type) where
  | activate (who : Player)
  | include (id : MessageId Player)
  | wait

def NetworkChoice.command (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
    NetworkChoice Player → (runtime.reactiveApplication leaks).Command
  | .activate who => .activate who
  | .include id => .include id
  | .wait => .wait

abbrev NetworkPolicy (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :=
  List (runtime.reactiveApplication leaks).EnvironmentEntry →
    (runtime.reactiveApplication leaks).EnvironmentView → FinDist (NetworkChoice Player)

def interactionVisit (networkTurns : Nat) (event : graph.EventId) :
    List (ServiceInstruction graph) :=
  [.grant event] ++ (match graph.actor? event with
    | none => []
    | some owner => [.player owner] ++ List.replicate networkTurns .wire ++
        [.includeLatest event owner]) ++ [.sample event]

def interactionEpoch (chosen : ServiceOrder graph) (networkTurns : Nat) :
    List (ServiceInstruction graph) :=
  chosen.val.flatMap (interactionVisit networkTurns) ++ [.tick] ++
    (List.finRange graph.order.eventCount).map .expire

/-- Selection is by event and authenticated author, excluding spent identifiers.
Replays retain the envelope author and can affect pending order. -/
def reactiveLatest (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (event : graph.EventId) (owner : Player)
    (view : (runtime.reactiveApplication leaks).EnvironmentView) :
      (runtime.reactiveApplication leaks).Command :=
  match view.network.pending.reverse.find? (fun message =>
      message.sender = owner ∧ message.payload.call.event? graph = some event ∧
        view.Unpublished (runtime.reactiveApplication leaks) message.id) with
  | none => .wait
  | some message => .include message.id

def interactionInstruction (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (network : runtime.NetworkPolicy leaks)
    (history : List (runtime.reactiveApplication leaks).EnvironmentEntry)
    (view : (runtime.reactiveApplication leaks).EnvironmentView) :
    ServiceInstruction graph → FinDist (runtime.reactiveApplication leaks).Command
  | .player who => FinDist.pure (.activate who)
  | .wire => (network history view).map (fun choice =>
      (runtime.reactiveApplication leaks).atMostOnceCommand view (choice.command runtime leaks))
  | .grant event => FinDist.pure (.application (.grant event))
  | .includeLatest event owner => FinDist.pure (runtime.reactiveLatest leaks event owner view)
  | .sample event => FinDist.pure (.application (.executeSample event))
  | .tick => FinDist.pure (.application .advanceClock)
  | .expire event => FinDist.pure (.application (.expire event))

/-- A fixed service order is a concrete scheduler instance. Its position is
recovered from its own command recall, which advances once per scheduler choice,
including activations. Player responses do not consume another service step. -/
def interactionScheduler (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (chosen : ServiceOrder graph)
    (networkTurns : Nat) (network : runtime.NetworkPolicy leaks) :
    (runtime.reactiveApplication leaks).Scheduler :=
  fun history view =>
    let epoch := interactionEpoch chosen networkTurns
    match epoch[history.length % epoch.length]? with
    | none => FinDist.pure .wait
    | some instruction => runtime.interactionInstruction leaks network history view instruction

def interactionHorizon (runtime : EventGraphRuntime graph)
    (chosen : ServiceOrder graph)
    (networkTurns : Nat) : Nat :=
  runtime.serviceEpochs * (interactionEpoch chosen networkTurns).length

end Vegas.EventGraphRuntime

-- ReactiveBindingService and ReactiveDisclosureService prove full wire-block
-- realization under prescribed-owner packet integrity. Conflicting packets
-- from earlier deviations by that owner require a separate continuation analysis.
