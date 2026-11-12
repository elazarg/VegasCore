module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketCanonicalPermits
public import Vegas.Game.SourceServiceCanonicalAcceptance
public import Vegas.Game.SourceServiceFreshCall
public import Vegas.Pending.ReactiveAsyncContract

@[expose] public section

/-! # Unique packets at bounded one-packet histories

The bounded count rule permits at most one own identifier per event. Consequently,
no other recalled response emits a different packet for the event of an already
recorded own packet, independently of scheduler choices and other players.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)} {mode : EventGraph.ExecutionMode}
  {duration : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

section OnePacket

variable [Fintype Player] {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  (bounds : MessageBounds (graph setup))

/-- **One packet per event.** At a history of the one-packet game of the
supplied runtime, under any scheduler, no entry of a player's recall emits a
packet for an event other than a given own packet for that event. -/
theorem onePacket_not_emitsOtherFor {horizon : Nat}
    {scheduler : (application setup timeouts leaks).Scheduler} {control : (application setup
      timeouts leaks).Control}
    (trace : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (message : Message Player (WitnessedPacket (graph setup)))
    (member : message ∈ (application setup timeouts leaks).outputs (control.execution.logs who))
    (named : message.payload.call.event? (graph setup) = some event)
    (entry : (application setup timeouts leaks).PlayerEntry) (_ : entry ∈ control.execution.logs
      who) :
    ¬ EmitsOtherFor timeouts leaks entry event message.id := by
  rintro ⟨other, emitted, sender, otherNamed, different⟩
  have rawTrace : ((application setup timeouts leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have clean := (bounds.onePacketMenu_countClean timeouts leaks scheduler).history
    (initialLaw setup) horizon (fun state _ => (countClean_initial timeouts) leaks state)
    trace
  have recalled := clean.1
  have signed := signedCommitments_history timeouts leaks (initialLaw setup)
    (serviceInitialLaw_initialized setup) horizon scheduler rawTrace
  -- Both packets are inputs of the network, signed by `who`.
  have messageSender : message.sender = who := by
    obtain ⟨recorded, recordedMember, recordedEmitted⟩ := List.mem_filterMap.mp member
    exact (signed.emissions who recorded recordedMember message recordedEmitted).1
  have otherMember : other ∈ (application setup timeouts leaks).outputs (control.execution.logs
    who) :=
    List.mem_filterMap.mpr ⟨entry, by assumption, emitted⟩
  have inputOf (packet : Message Player (WitnessedPacket (graph setup)))
      (output : packet ∈ (application setup timeouts leaks).outputs (control.execution.logs who)) :
      packet ∈ control.execution.network.inputs := by
    rw [← recalled.1 who] at output
    exact (List.mem_filter.mp output).1
  have otherSender : other.sender = who := sender.trans messageSender
  have serials : other.id.2 ≠ message.id.2 := by
    intro same
    apply different
    exact Prod.ext (otherSender.trans messageSender.symm) same
  -- The later of the two packets is not first for the event.
  have firstFor (packet earlierPacket : Message Player (WitnessedPacket (graph setup)))
      (packetInput : packet ∈ control.execution.network.inputs)
      (earlierInput : earlierPacket ∈ control.execution.network.inputs)
      (sameSender : earlierPacket.sender = packet.sender)
      (lower : earlierPacket.id.2 < packet.id.2) :
      earlierPacket.payload.call.event? (graph setup) ≠
        packet.payload.call.event? (graph setup) := by
    have permitted := (countPermits_eq_true_iff _ _).mp (clean.2 packet packetInput)
    exact permitted.2.2 earlierPacket ⟨earlierInput, sameSender, lower⟩
  rcases Nat.lt_or_gt_of_ne serials with lower | higher
  · exact firstFor message other (inputOf message member) (inputOf other otherMember)
      (otherSender.trans messageSender.symm) lower (otherNamed.trans named.symm)
  · exact firstFor other message (inputOf other otherMember) (inputOf message member)
      (messageSender.trans otherSender.symm) higher (named.trans otherNamed.symm)

end OnePacket

end Vegas
