/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveRuntime

/-! # Reserved service with one owner activation

A network opportunity can activate any player, deliver, include, or wait.
Application grants, sampling, clock ticks, and expiry remain controlled by the
service contract. Each strategic visit reserves one owner activation followed
by network opportunities and event-addressed inclusion. There is no reaction
roster and no private preparation phase.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

inductive NetworkChoice (Player : Type) where
  | activate (who : Player)
  | deliver (who : Player) (id : MessageId Player)
  | include (id : MessageId Player)
  | wait

def NetworkChoice.command (runtime : EventGraphRuntime graph) :
    NetworkChoice Player → runtime.reactiveApplication.Command
  | .activate who => .activate who
  | .deliver who id => .deliver who id
  | .include id => .include id
  | .wait => .wait

abbrev NetworkPolicy (runtime : EventGraphRuntime graph) :=
  List runtime.reactiveApplication.EnvironmentEntry →
    runtime.reactiveApplication.EnvironmentView → FinDist (NetworkChoice Player)

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

/-- Selection is by event and authenticated author, independent of unrelated
traffic. Replays retain the envelope author and can affect pending order. -/
def reactiveLatest (runtime : EventGraphRuntime graph) (event : graph.EventId) (owner : Player)
    (view : runtime.reactiveApplication.EnvironmentView) : runtime.reactiveApplication.Command :=
  match view.network.pending.reverse.find? (fun message =>
      message.sender = owner ∧ message.payload.event? graph = some event) with
  | none => .wait
  | some message => .include message.id

def interactionInstruction (runtime : EventGraphRuntime graph) (network : runtime.NetworkPolicy)
    (history : List runtime.reactiveApplication.EnvironmentEntry)
    (view : runtime.reactiveApplication.EnvironmentView) :
    ServiceInstruction graph → FinDist runtime.reactiveApplication.Command
  | .player who => FinDist.pure (.activate who)
  | .wire => (network history view).map (NetworkChoice.command runtime)
  | .grant event => FinDist.pure (.application (.grant event))
  | .includeLatest event owner => FinDist.pure (runtime.reactiveLatest event owner view)
  | .sample event => FinDist.pure (.application (.executeSample event))
  | .tick => FinDist.pure (.application .advanceClock)
  | .expire event => FinDist.pure (.application (.expire event))

/-- A fixed service order is a concrete scheduler instance. Its position is
recovered from its own command recall, which advances once per scheduler choice,
including activations. Player responses do not consume another service step. -/
def interactionScheduler (runtime : EventGraphRuntime graph) (chosen : ServiceOrder graph)
    (networkTurns : Nat) (network : runtime.NetworkPolicy) :
    runtime.reactiveApplication.Scheduler :=
  fun history view =>
    let epoch := interactionEpoch chosen networkTurns
    match epoch[history.length % epoch.length]? with
    | none => FinDist.pure .wait
    | some instruction => runtime.interactionInstruction network history view instruction

def interactionHorizon (runtime : EventGraphRuntime graph) (chosen : ServiceOrder graph)
    (networkTurns : Nat) : Nat :=
  runtime.serviceEpochs * (interactionEpoch chosen networkTurns).length

end Vegas.EventGraphRuntime

-- OPEN OBLIGATION: Reactive prescribed-packet protection
-- The canonical schedule and completion bound are checked in
-- ReactiveServiceEvaluation and ReactiveServiceCompletion. Prove that the
-- service realizes each compiled decision with the required outcome law,
-- including reactions and replay before reserved inclusion.
-- ReactivePacketIntegrity rules out conflicting packets under a prescribed
-- owner and event; acceptance and retention until inclusion remain to prove.
