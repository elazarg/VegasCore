/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCanonicalSerial

/-! # Protected actual owner decisions cannot miss

An actually recalled protected conforming call with a sole owner identifier
prevents expiry of its owned event. The proof uses actual packet provenance,
recall and protected inclusion, with arbitrary foreign responses. It covers
commitments, successful openings and explicit withholding alike.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- An actually recorded conforming protected decision call with a unique own
identifier cannot become a public missed decision. Foreign responses are unrestricted. -/
theorem owner_recorded_decision_no_miss {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {bound : (graph setup).EventId → Nat}
    (inclusion : ProtectedInclusion (runtime setup) leaks (initialLaw setup) horizon scheduler
      bound)
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (who : Player)
    (calls : OwnFreshCalls setup leaks bound control.execution who)
    (conforming : FreshCallsConform setup leaks control.execution who)
    (once : OneCallPerEvent setup leaks control.execution who)
    (atTurn : OwnSubmissionsAtTurn setup leaks control.execution who)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (recorded : (runtime setup).eventRecorded leaks (control.execution.recall who) event = true) :
    event ∉ control.execution.application.missedEvents := by
  let app := application setup leaks
  have facts := legalFacts setup leaks horizon scheduler control trace
  obtain ⟨entry, member, submitted⟩ := List.any_eq_true.mp recorded
  have named : (runtime setup).submittedEvent? leaks entry.action = some event :=
    of_decide_eq_true submitted
  obtain ⟨material, transmission⟩ : ∃ material, entry.action.transmission = some material := by
    cases sent : entry.action.transmission with
    | none => simp only [EventGraphRuntime.submittedEvent?, sent] at named; cases named
    | some material => exact ⟨material, rfl⟩
  obtain ⟨other, message, emitted, authored, addressed, submittedOther, fits⟩ :=
    calls entry member material transmission
  cases Option.some.inj (named.symm.trans submittedOther)
  have conform := conforming entry member material message transmission emitted
  have call : FreshCall setup leaks who event bound entry message := {
    fresh := ⟨material, transmission⟩
    emitted := emitted
    authored := authored
    addressed := addressed
    ready := (PublicView.ownTurn?_spec _ who event (atTurn entry member event named)).1
    fits := fits
    conforming := EventGraphRuntime.freshServiceEnvelope.acceptable (runtime setup) conform }
  obtain ⟨earlier, later, split⟩ := List.mem_iff_append.mp member
  have sole : ∀ other ∈ earlier ++ later,
      ¬ EmitsOtherFor (runtime setup) leaks other event message.id := by
    intro other inside ⟨packet, emittedOther, authorOther, addressedOther, different⟩
    have otherMember : other ∈ control.execution.recall who := by
      rw [split]
      rcases List.mem_append.mp inside with before | after
      · exact List.mem_append_left _ before
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ after)
    have output : packet ∈ app.outputs (control.execution.recall who) :=
      List.mem_filterMap.mpr ⟨other, otherMember, emittedOther⟩
    rw [← facts.inputs who] at output
    obtain ⟨issuer, issuerMember, issuerMaterial, issuerTransmission, issuerEmitted,
      issuerState, issuerKnown, issuerPacket⟩ :=
      facts.provenance.inputs packet (List.mem_filter.mp output).1
    have author : packet.sender = who := authorOther.trans authored
    rw [author] at issuerMember
    have issuerEvent : (runtime setup).submittedEvent? leaks issuer.action = some event := by
      unfold EventGraphRuntime.submittedEvent?
      rw [issuerTransmission]
      change (app.packet issuerState packet.sender issuerKnown issuerMaterial).call.event?
        (graph setup) = some event
      rw [issuerPacket]
      exact addressedOther
    exact different (once issuer issuerMember entry member event packet message issuerEvent
      named issuerEmitted emitted)
  exact (settlesFreshCalls_history setup leaks inclusion who event owned trace earlier entry
    later message split call sole).2.2.2


end Vegas
