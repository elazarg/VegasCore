/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketEventSuccess
import Vegas.Game.ServiceWithheldForfeit
import Vegas.Game.ServiceRevealDecode
import Vegas.Game.OnePacketActorRecord

/-! # The owner's one packet at a binding

The one-packet menu sends no malformed packet: every transmitting response is
permitted by the count verdict, whose call check rejects a malformed packet
(`Vegas.onePacket_not_malformed`). At a history of the one-packet game whose
binding event of `who` has no accepted handle, and whose recall of `who` holds
an entry emitting the commitment of that event to a candidate, one protocol
transition installs, if anything, that candidate at the event: the owner's one
packet is the only commitment the contract can install there
(`Vegas.onePacket_accepted_new`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

omit [DecidableEq Player] in
private theorem cast_some {A B : Type} (same : A = B) (value : A) :
    cast (congrArg Option same) (some value) = some (cast same value) := by
  cases same
  rfl

omit [DecidableEq Player] in
private theorem cast_cast_symm {A B : Type} (same : A = B) (value : B) :
    cast same (cast same.symm value) = value := by
  cases same
  rfl

section OnePacketCommitment

variable [Fintype Player] (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

/-- **Only the owner's one packet can fill a vacant binding.** At a history of
the one-packet game whose binding event `event` of `who` has no accepted
handle, and whose recall of `who` holds an entry emitting the commitment of
`event` to `candidate`, one protocol transition installs, if anything, that
candidate at the event. -/
theorem onePacket_accepted_new {control next : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    {who : Player} {entry : (application setup leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))}
    (records : RecordsEntry setup leaks who entry (some control))
    (emitted : entry.emitted = some message) (sender : message.sender = who)
    {event : (graph setup).EventId} {candidate : Handle (graph setup)}
    (call : message.payload.call = .commitment event candidate)
    (owned : (graph setup).actor? event = some who)
    (vacant : control.execution.application.accepted (.inr event) = none)
    (joint : Player → Option (application setup leaks).Action)
    (reached : some next ∈ ((application setup leaks).transition (initialLaw setup) horizon
      scheduler (some control) joint).support) :
    ∀ handle, next.execution.application.accepted (.inr event) = some handle →
      handle = candidate := by
  intro installed filled
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have facts := legalFacts setup leaks horizon scheduler _ rawTrace
  have unchanged (same : next.execution.application.accepted (.inr event) =
      control.execution.application.accepted (.inr event)) : installed = candidate := by
    rw [same, vacant] at filled
    cases filled
  rcases control with ⟨remaining, current, execution⟩
  cases current with
  | some responder =>
      cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
      exact unchanged (congrFun (congrArg PublicView.accepted
        ((runtime setup).reactive_respond_application leaks execution responder _).2) _)
  | none =>
      cases remaining with
      | zero =>
          cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
          exact unchanged rfl
      | succ remaining =>
          obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
          obtain ⟨moved', supported, same⟩ := PMF.support_map .. ▸ moved
          cases Option.some.inj same
          cases command with
          | wait =>
              simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at supported
              cases (PMF.mem_support_pure_iff _ _).mp supported
              exact unchanged rfl
          | activate activated =>
              obtain ⟨updated, chosen, rfl⟩ := PMF.support_map .. ▸ supported
              obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ chosen
              exact unchanged rfl
          | application command =>
              obtain ⟨updated, chosen, rfl⟩ := PMF.support_map .. ▸ supported
              obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ chosen
              exact unchanged (congrFun
                (environmentStep_tables (runtime setup) _ _ command changed).1 _)
          | «include» id =>
              simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at supported
              cases (PMF.mem_support_pure_iff _ _).mp supported
              change (execution.includePending (application setup leaks)
                id).application.accepted (.inr event) = some installed at filled
              unfold ReactiveApplication.Execution.includePending
                MessageNetwork.includePending at filled
              cases found : execution.network.lookup id with
              | none =>
                  simp only [found] at filled
                  exact absurd (filled.symm.trans vacant) (by simp)
              | some envelope =>
                  simp only [found] at filled
                  cases acceptedEq : (application setup leaks).handle execution.application
                      envelope with
                  | none =>
                      simp only [acceptedEq, Option.getD_none] at filled
                      exact absurd (filled.symm.trans vacant) (by simp)
                  | some after =>
                      simp only [acceptedEq, Option.getD_some] at filled
                      have handled := reactiveHandle_call acceptedEq
                      rcases handle_tables_cases (runtime setup) _ _ _ handled with
                        ⟨named, chosen, payloadEq, _, acceptedTable, _⟩ | ⟨acceptedTable, _⟩
                      · change envelope.payload.call = .commitment named chosen at payloadEq
                        by_cases sameEvent : named = event
                        · subst sameEvent
                          rw [acceptedTable, Function.update_self] at filled
                          cases Option.some.inj filled
                          -- The envelope is the owner's one packet for the event.
                          have envelopeSender : envelope.sender = who := by
                            have acts := handle_sender_actor (runtime setup) _ _ _ handled named
                              (by rw [payloadEq]; rfl)
                            exact Option.some.inj (acts.symm.trans owned)
                          have pending := (includePending_found execution.network id envelope
                            found).2.1
                          obtain ⟨other, otherMember, _, _, otherEmitted, _⟩ :=
                            facts.provenance.pending envelope pending
                          rw [envelopeSender] at otherMember
                          obtain ⟨earlier, later, split⟩ := records
                          change execution.recall who = _ at split
                          have output : message ∈ (application setup leaks).outputs
                              (execution.recall who) := by
                            rw [split]
                            exact List.mem_filterMap.mpr ⟨entry, by simp, emitted⟩
                          have named' : message.payload.call.event? (graph setup) = some named := by
                            rw [call]
                            rfl
                          have sameId : envelope.id = message.id := by
                            by_contra different
                            exact onePacket_not_emitsOtherFor bounds trace who named message output
                              named' other otherMember ⟨envelope, otherEmitted,
                                envelopeSender.trans sender.symm, by rw [payloadEq]; rfl,
                                different⟩
                          rw [← facts.inputs who] at output
                          have inInputs := (List.mem_filter.mp output).1
                          have sameEnvelope : envelope = message :=
                            (facts.unique.inputs message inInputs).pending envelope pending sameId
                          rw [sameEnvelope, call] at payloadEq
                          cases payloadEq
                          rfl
                        · rw [acceptedTable, Function.update_of_ne
                            (fun same => sameEvent (Sum.inr.inj same).symm)] at filled
                          exact absurd (filled.symm.trans vacant) (by simp)
                      · rw [acceptedTable] at filled
                        exact absurd (filled.symm.trans vacant) (by simp)

/-- **The one-packet menu sends no malformed packet.** Every transmitting
response of the one-packet menu is permitted by the count verdict, whose call
check rejects a malformed packet. -/
theorem onePacket_not_malformed {who : Player}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {response : (application setup leaks).Action}
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who past view)
    {material : (application setup leaks).Submission}
    (submits : response.transmission = some material) (raw : Raw L) :
    material.call.packet ≠ .malformed raw := by
  intro malformed
  rcases ((bounds.mem_onePacketActions (runtime setup) leaks who past view response).mp
      member).2 with silent | ⟨sent, transmits, permitted⟩
  · rw [submits] at silent
    cases silent
  · rw [submits] at transmits
    cases Option.some.inj transmits
    have correct := ((countPermits_eq_true_iff _ _).mp permitted).2.1
    change CountCallCorrect _ ⟨_, ⟨material.call.packet, _, _⟩⟩ at correct
    unfold CountCallCorrect at correct
    simp only [malformed] at correct

end OnePacketCommitment

end Vegas
