/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseCountServiceReference
import Vegas.Pending.PhaseResolutionPersistence
import Vegas.Pending.PhaseCountUniqueness

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

/-- Original coordinate-relative emission clocks remain recoverable after
the namespace retires. Transport identifiers are not part of this word. -/
def bindingEmissionClocks (coordinate : CommitAttemptEvent graph) (owner : Player)
    (execution : (app).Execution) : List Nat :=
  (PhaseSeedScheduler.localInput runtime leaks coordinate owner execution.environmentRecall
    (execution.observeEnvironment app)).emissions.map Prod.fst


/-- An accepting receipt for this original physical binding. Both inputs and
receipts are retained through normalization, rollback and exhausted restore. -/
def BindingAccepted (coordinate : CommitAttemptEvent graph) (owner : Player)
    (execution : (app).Execution) : Prop :=
  ∃ message ∈ execution.network.inputs,
    message.sender = owner ∧ message.payload.attempt = coordinate.attempt ∧
      message.payload.packet.call.event? graph = some coordinate.event ∧
        (message.id, true) ∈ execution.receipts

/-- Among actual counted binding histories, resolved success depends only on
the original local seed and relative emission clocks. Exact inclusion times,
foreign traffic, private results and transport identifiers may differ. -/
def PrivateBindingSuccess (seedLaw : PMF Seeds) (family : Seeds → (app).Scheduler) : Prop :=
  ∀ firstSeeds ∈ seedLaw.support, ∀ secondSeeds ∈ seedLaw.support,
    ∀ (first second : (app).Control),
    ((menu).protocol initial horizon (family firstSeeds)).Trace (some first) →
    ((menu).protocol initial horizon (family secondSeeds)).Trace (some second) →
    ∀ (coordinate : PhaseSeedAddress graph) owner payload,
    graph.outputLayout coordinate.1.event = .binding owner payload →
    coordinate.1.Resolved first.execution.application →
    coordinate.1.Resolved second.execution.application →
    firstSeeds.2 coordinate = secondSeeds.2 coordinate →
    bindingEmissionClocks runtime leaks coordinate.1 owner first.execution =
      bindingEmissionClocks runtime leaks coordinate.1 owner second.execution →
    (BindingAccepted runtime leaks coordinate.1 owner first.execution ↔
      BindingAccepted runtime leaks coordinate.1 owner second.execution)

end Vegas.EventGraphRuntime.PhaseService
