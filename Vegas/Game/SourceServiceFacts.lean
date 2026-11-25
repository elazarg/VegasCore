module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.RevealService
public import Vegas.Pending.RecordedCall
public import Vegas.Pending.ExecutionFacts
public import Vegas.EventGraph.SolitaryEvent
public import Vegas.Pending.ReactiveSignedCommitments
public import Vegas.Pending.ReactiveEventStability
public import Vegas.Pending.ReactiveAssociationEvidence
public import Vegas.Pending.ReactivePacketEvidence
public import Vegas.Pending.ReactiveStateInvariant
public import Vegas.Pending.ReactiveSubmissionRecall
public import Vegas.Pending.EventCommandFrame
public import Interaction.ReactiveProvenance
public import Interaction.ReactiveMessageIdentity
public import Interaction.ReactiveAllocation
public import Interaction.ReactiveReceipts

@[expose] public section

/-! # Raw initialized service-history facts

Readiness, fixed binding meanings, authentic evidence, recall and packet identities follow
from the native operations at every initialized history. They require no reserved schedule,
source policy, factorization or successful public guards.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))

/-- The initial native law is the image of the existing typed setup inputs. -/
theorem serviceInitialLaw_eq_inputs :
    serviceInitialLaw setup deps =
      (setup.initialLaw.map setup.eventInputs).map
        (EventGraphRuntime.State.initial (graph := serviceGraph setup deps)) := by
  rw [PMF.map_comp]
  rfl

/-- Every initialized raw history supplies these facts under arbitrary responses and scheduler. -/
theorem legalFacts (horizon : Nat)
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (control : (serviceApplication setup deps duration leaks).Control)
    (trace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialLaw setup deps) horizon scheduler).Trace (some control)) :
    LegalFacts (serviceTimeouts setup deps duration) leaks control.execution := by
  rw [serviceInitialLaw_eq_inputs setup] at trace
  exact EventGraphRuntime.legalFacts _ leaks _ horizon scheduler control trace

/-- A pending authentic envelope names a submission already retained in its
sender's recall. It can therefore be attributed before an inclusion attempt. -/
theorem eventRecorded_of_pending
    {horizon : Nat} {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {control : (serviceApplication setup deps duration leaks).Control}
    (trace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialLaw setup deps) horizon scheduler).Trace (some control))
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (message : Message Player (WitnessedPacket (serviceGraph setup deps)))
    (member : message ∈ control.execution.network.pending)
    (sender : message.sender = owner)
    (named : message.payload.call.event? (serviceGraph setup deps) = some event) :
    (eventRecorded (serviceTimeouts setup deps duration)) leaks
      (control.execution.logs owner) event = true := by
  rw [serviceInitialLaw_eq_inputs setup] at trace
  exact EventGraphRuntime.eventRecorded_of_pending _ leaks trace owner event message member sender
    named

section SolitaryWaiting
variable {setup}

/-- Before its deadline, no environment command changes the unique ready owned
configuration when the network has no call from that owner naming that event. -/
theorem environment_waiting_config (timeouts : EventTimeouts setup.informationGraph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    (execution next : (application setup timeouts leaks).Execution)
    (command : (application setup timeouts leaks).Command)
    (event : setup.informationGraph.EventId) (owner : Player)
    (ready : execution.application.config.cut.Ready event)
    (owned : setup.informationGraph.actor? event = some owner)
    (within : execution.application.WithinDeadline timeouts event)
    (quiescent : ∀ query, ¬ execution.application.AutomaticReady query)
    (safe : ∀ message ∈ execution.network.pending, message.sender = owner →
      message.payload.call.event? setup.informationGraph ≠ some event)
    (reached : next ∈
      (execution.environmentStep (application setup timeouts leaks) command).support) :
    next.application.config = execution.application.config :=
  environment_waiting_config_of_solitary timeouts leaks execution next command event
    (setup.informationGraph.sequentialize_solitary event) owner ready owned within quiescent safe
    reached

end SolitaryWaiting

end Vegas
