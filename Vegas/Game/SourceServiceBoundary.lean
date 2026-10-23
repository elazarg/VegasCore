/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceCalendarState
import Vegas.Game.SourceServiceMenu
import Vegas.Game.ServiceRoster
import Interaction.ReactiveSubmissionSerial
import Vegas.Pending.ReactiveAssociationEvidence
import Vegas.Pending.ReactiveServiceOpportunity
import Vegas.Game.SourceServiceCheckpoint
import Vegas.Pending.ReactiveBindingTranscript

/-! # Operational boundaries for the complete source syntax

These are facts about the existing source configuration and native execution.
The registry, accepted handles and candidate catalogue may change at each
source step. Public serial accounting and actual own-response counts are
recorded alongside semantic store agreement. There is no belief, equilibrium,
or observation-factorization premise.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- A completed service prefix, including its dynamic private catalogues and
all native communication memory. Pending and privately known packets are
already public at this boundary. -/
structure ServiceBoundary (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player) (initial : State L setup.context)
    {Γ : SourceCtx Player L} (source : Config Player L Γ)
    (refs : ContextRefs (graph setup).layout Γ) (rank : Nat)
    (execution : (application setup leaks).Execution) : Prop
    extends SourceCheckpoint setup source refs rank execution.application.config where
  invariant : EventGraphRuntime.State.Invariant (graph := graph setup)
    (setup.eventInputs initial) execution.application
  binding : execution.application.BindingInvariant
  prepared : ∀ who, execution.application.PreparedPrefix who
  represented : execution.application.CandidatesRepresented
  acceptedRecorded : execution.application.AcceptedRecorded
  recall : execution.InputRecall (application setup leaks)
  serialRecall : execution.SerialRecall (application setup leaks)
  published : execution.network.Satisfies fun message =>
    message.id ∈ execution.network.ledger.map Message.id
  serials : execution.network.SerialsBeforeNext
  accounted : ∀ who, execution.network.nextSerial who =
    Message.distinctAuthoredCount execution.network.ledger who
  counts : ∀ who, (execution.recall who).length =
    (((List.finRange (graph setup).order.eventCount).take rank).flatMap rosters).count who
  unsent : ∀ who event, rank ≤ event.val →
    (runtime setup).eventRecorded leaks (execution.recall who) event = false
  clock : execution.application.clock = clockAt rank
  timely : ∀ event, event.val = rank → ((graph setup).actor? event).isSome = true →
    execution.application.WithinDeadline (runtime setup) event

/-- Readiness is derived from the actual completed prefix, including chance
and dynamically allocated commitment events. -/
theorem ServiceBoundary.ready {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {initial : State L setup.context}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (boundary : ServiceBoundary setup leaks rosters initial source refs rank execution)
    (event : (graph setup).EventId) (atRank : event.val = rank) :
    execution.application.config.cut.Ready event :=
  (ready_iff_rank setup _ rank boundary.ordered event).mpr atRank

/-- Passive sampling retains every boundary fact, while keeping its actual
known-envelope updates and environment record in the execution. -/
theorem ServiceBoundary.sampledActivation {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {initial : State L setup.context}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (boundary : ServiceBoundary setup leaks rosters initial source refs rank execution)
    (who : Player) (sample : Finset (MessageId Player)) :
    ServiceBoundary setup leaks rosters initial source refs rank
      (execution.sampledActivation (application setup leaks) who sample) :=
  { boundary with
    published := boundary.published.learn who sample
    serials := boundary.serials.learn who sample }

end Vegas
