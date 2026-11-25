module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.CallSettlement
public import Vegas.Game.SourceServiceFacts
public import Vegas.Pending.RecordedCall
public import Vegas.Pending.ReactiveServiceConditions
public import Vegas.Pending.ReactiveGraphSteps
public import Vegas.Pending.EventCommandFrame
public import Vegas.Pending.ExclusionInvariant
public import Vegas.Pending.PublicFailureEvidence
public import Interaction.ReactiveReceipts

@[expose] public section

/-! # Protected-call settlement in the native runtime

An acceptable call sent within its protected inclusion window is accepted
when its owner emits no other packet for the event. The event cannot expire
or complete through a different packet first.
Authentic guard rejection produces an accepting receipt and the source's
declared failure result. Other commands may advance independent owners and
drain automatic events. Same-owner readiness and active-owner preservation
keep the protected event unfinished until its own inclusion.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))

/-- **A settled protected call keeps its event within the deadline.** While the
event of a recorded settled fresh call is unfinished, protected inclusion has
not yet run out, so the event has not passed its deadline. -/
theorem FreshCall.withinDeadline
    {horizon : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {bound : (serviceGraph setup deps).EventId → Nat}
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (owned : (serviceGraph setup deps).actor? event = some owner)
    {control : (serviceApplication setup deps duration leaks).Control}
    (trace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialLaw setup deps) horizon scheduler).Trace (some control))
    (inclusion : ProtectedInclusionAt (serviceTimeouts setup deps duration)
      leaks control.execution bound)
    (earlier : List (serviceApplication setup deps duration leaks).PlayerEntry)
    (entry : (serviceApplication setup deps duration leaks).PlayerEntry)
    (later : List (serviceApplication setup deps duration leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (serviceGraph setup deps)))
    (split : control.execution.logs owner = earlier ++ entry :: later)
    (call : FreshCall (serviceTimeouts setup deps duration) leaks owner event bound entry message)
    (sole : ∀ other ∈ earlier ++ later, ¬ EmitsOtherFor (serviceTimeouts setup deps duration) leaks
      other event message.id)
    (settled : Settled
      (serviceTimeouts setup deps duration) leaks event message.id control.execution)
    (unfinished : event ∉ control.execution.application.config.cut.completed) :
    control.execution.application.WithinDeadline (serviceTimeouts setup deps duration) event := by
  rw [serviceInitialLaw_eq_inputs setup] at trace
  exact EventGraphRuntime.FreshCall.withinDeadline _ leaks owner event owned trace inclusion earlier
    entry later message split call sole settled unfinished

/-- The settlement invariant holds at every legal history. -/
theorem settlesFreshCalls_history {horizon : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {bound : (serviceGraph setup deps).EventId → Nat}
    (inclusion : ProtectedInclusion (serviceTimeouts setup deps duration) leaks
        (serviceInitialLaw setup deps) horizon scheduler bound)
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (ownerSolitary : (serviceGraph setup deps).OwnerSolitary event)
    (owned : (serviceGraph setup deps).actor? event = some owner) :
    ∀ {state}
        (_trace :
            ((serviceApplication setup deps duration leaks).protocol (serviceInitialLaw setup deps)
            horizon scheduler).Trace state), ReactiveApplication.serviceInvariant
        (SettlesFreshCalls
          (serviceTimeouts setup deps duration) leaks owner event bound) state := by
  intro state trace
  rw [serviceInitialLaw_eq_inputs setup] at trace inclusion
  exact EventGraphRuntime.settlesFreshCalls_history _ leaks inclusion owner event ownerSolitary
    owned trace

/-- **Timeliness of an acceptable fresh call.** Under the contract's protected
inclusion an owner's fresh call for its ready event, sent while an inclusion within
`bound` slots lands before the deadline and acceptable on the view it saw,
with no other identifier of its own emitted by the owner for the event, is accepted once the
bound has passed; and the event completes only through it, so it is neither
rejected nor preceded by expiry. -/
theorem prescribed_packet_settles {horizon : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {bound : (serviceGraph setup deps).EventId → Nat}
    (inclusion : ProtectedInclusion (serviceTimeouts setup deps duration) leaks
        (serviceInitialLaw setup deps) horizon scheduler bound)
    {control : (serviceApplication setup deps duration leaks).Control}
    (trace :
        ((serviceApplication setup deps duration leaks).protocol (serviceInitialLaw setup deps)
        horizon scheduler).Trace (some control))
    (event : (serviceGraph setup deps).EventId) (owner : Player)
    (ownerSolitary : (serviceGraph setup deps).OwnerSolitary event)
    (owned : (serviceGraph setup deps).actor? event = some owner)
    (earlier later : List (serviceApplication setup deps duration leaks).PlayerEntry)
    (entry : (serviceApplication setup deps duration leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (serviceGraph setup deps)))
    (split : control.execution.logs owner = earlier ++ entry :: later)
    (call : FreshCall (serviceTimeouts setup deps duration) leaks owner event bound entry message)
    (sole : ∀ other ∈ earlier ++ later,
      ¬ EmitsOtherFor (serviceTimeouts setup deps duration) leaks other event message.id) :
    (entry.beforeView.application.publicView.clock + bound event <
        control.execution.application.clock →
      (message.id, true) ∈ control.execution.receipts) ∧
      (event ∈ control.execution.application.config.cut.completed →
        (message.id, true) ∈ control.execution.receipts) := by
  have settled := settlesFreshCalls_history setup leaks inclusion owner event ownerSolitary
    owned trace
    earlier entry later message split call sole
  refine ⟨fun late => ?_, settled.1⟩
  by_cases finished : event ∈ control.execution.application.config.cut.completed
  · exact settled.1 finished
  · obtain ⟨accepted, receipt⟩ := inclusion control trace event owner owned earlier
      later entry message split call.emitted call.authored call.addressed call.ready sole
      finished late
    exact settled.2.1 accepted receipt


end Vegas
