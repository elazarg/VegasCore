/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseCountServiceReference
import Vegas.Pending.PhaseSeedScheduler
import Vegas.Pending.ReactiveBindingFrameStep

/-! # Physical event-private service on original counted histories -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseService

open EventGraph Interaction GameTheory.Protocol.ExecutionProtocol

variable {Player LocalSeed RestSeed : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)

local notation "app" => phaseApplication runtime leaks
local notation "Seeds" => RestSeed × (PhaseSeedAddress graph → LocalSeed)
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds

/-- An accepting receipt for this original physical binding. Both inputs and
receipts are retained through normalization, rollback and exhausted restore. -/
def BindingAccepted (coordinate : CommitAttemptEvent graph) (owner : Player)
    (execution : (app).Execution) : Prop :=
  ∃ message ∈ execution.network.inputs,
    message.sender = owner ∧ message.payload.attempt = coordinate.attempt ∧
      message.payload.packet.call.event? graph = some coordinate.event ∧
        (message.id, true) ∈ execution.receipts

end Vegas.EventGraphRuntime.PhaseService
