/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDecidedCompletion
import Vegas.Game.SourceServiceFirstTurnNoMiss
import Interaction.ReactivePolicyInvariant

/-! # Operational completion of an actually recorded owner decision

For any timing, an owner following the turn-counted source policy records a
protected conforming fresh call. Its actual entry persists through subsequent
rounds, including arbitrary foreign responses. Actual packet provenance and
the owner's one-call invariant identify the original packet as the sole owner
identifier for that event.

Complete play makes every completion-stopped endpoint complete the event.
Protected inclusion then supplies an accepting receipt for that exact original
identifier, and the event has no public miss marker. This does not identify a
source action or require a first-turn decision.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private theorem recalled_call_sole {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (owner : Player) (event : (graph setup).EventId)
    (once : OneCallPerEvent setup leaks control.execution owner)
    (entry : (application setup leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup)))
    (named : (runtime setup).submittedEvent? leaks entry.action = some event)
    (emitted : entry.emitted = some message) (authored : message.sender = owner)
    (earlier later : List (application setup leaks).PlayerEntry)
    (split : control.execution.recall owner = earlier ++ entry :: later) :
    ∀ other ∈ earlier ++ later,
      ¬ EmitsOtherFor (runtime setup) leaks other event message.id := by
  let app := application setup leaks
  have facts := legalFacts setup leaks horizon scheduler control trace
  have member : entry ∈ control.execution.recall owner := by
    rw [split]
    exact List.mem_append_right _ (List.mem_cons_self)
  intro other inside ⟨packet, emittedOther, authorOther, addressedOther, different⟩
  have otherMember : other ∈ control.execution.recall owner := by
    rw [split]
    rcases List.mem_append.mp inside with before | after
    · exact List.mem_append_left _ before
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ after)
  have output : packet ∈ app.outputs (control.execution.recall owner) :=
    List.mem_filterMap.mpr ⟨other, otherMember, emittedOther⟩
  rw [← facts.inputs owner] at output
  obtain ⟨issuer, issuerMember, material, transmission, issuerEmitted,
    state, known, issued⟩ := facts.provenance.inputs packet (List.mem_filter.mp output).1
  have author : packet.sender = owner := authorOther.trans authored
  rw [author] at issuerMember
  have issuerEvent : (runtime setup).submittedEvent? leaks issuer.action = some event := by
    unfold EventGraphRuntime.submittedEvent?
    rw [transmission]
    change (app.packet state packet.sender known material).call.event? (graph setup) = some event
    rw [issued]
    exact addressedOther
  exact different (once issuer issuerMember entry member event packet message issuerEvent
    named issuerEmitted emitted)

/-- Every completion-stopped continuation accepts the exact original recorded
owner packet and leaves no public miss. Timing and foreign policies are arbitrary. -/
theorem sourceServiceTurnPolicy_recorded_decision_completion {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (players : Player → (application setup leaks).Policy) (owner : Player)
    {turns : Nat} (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (follows : players owner =
      sourceServiceTurnPolicy setup leaks bound turns timing profile owner)
    (count : Nat) (within : count ≤ horizon) (start : (application setup leaks).Execution)
    (reached : start ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some owner)
    (recorded : (runtime setup).eventRecorded leaks (start.recall owner) event = true) :
    ∃ entry ∈ start.recall owner, ∃ message,
      (runtime setup).submittedEvent? leaks entry.action = some event ∧
      FreshCall setup leaks owner event bound entry message ∧
      ∀ stopped ∈ ((application setup leaks).runUntilHorizon scheduler players
          (fun final => event ∈ final.application.config.cut.completed) horizon start).support,
        entry ∈ stopped.recall owner ∧
        event ∈ stopped.application.config.cut.completed ∧
        (message.id, true) ∈ stopped.receipts ∧
        event ∉ stopped.application.missedEvents := by
  let app := application setup leaks
  obtain ⟨entry, member, named⟩ := ((runtime setup).eventRecorded_iff leaks _ event).mp recorded
  obtain ⟨material, transmission⟩ : ∃ material, entry.action.transmission = some material := by
    cases sent : entry.action.transmission with
    | none => simp only [EventGraphRuntime.submittedEvent?, sent] at named; cases named
    | some material => exact ⟨material, rfl⟩
  obtain ⟨calls, _, _⟩ := serialFacts_roundsFrom contract players owner timing profile follows
    count within start reached
  obtain ⟨other, message, emitted, authored, addressed, submittedOther, fits⟩ :=
    calls entry member material transmission
  cases Option.some.inj (named.symm.trans submittedOther)
  have atTurn := (canonicalSlots_roundsFrom scheduler players owner timing profile follows
    count start reached).1
  have conform := sourceServiceTurnPolicy_freshServiceEnvelope scheduler players owner timing
    profile follows count start reached entry member material transmission message emitted
  have call : FreshCall setup leaks owner event bound entry message := {
    fresh := ⟨material, transmission⟩
    emitted := emitted
    authored := authored
    addressed := addressed
    ready := (PublicView.ownTurn?_spec _ owner event (atTurn entry member event named)).1
    fits := fits
    conforming := EventGraphRuntime.freshServiceEnvelope.acceptable (runtime setup) conform }
  refine ⟨entry, member, message, named, call, ?_⟩
  intro stopped supported
  have recallLength := app.roundsFrom_recall (initialLaw setup) scheduler players count start
    reached
  have startBounded : start.environmentRecall.length ≤ horizon := by omega
  obtain ⟨startTrace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
    count within start reached
  rw [← recallLength] at startTrace
  have complete := runUntilHorizon_completes contract.completes startBounded startTrace stopped
    supported
  obtain ⟨used, budget, rounds, stoppedLength⟩ := app.runUntil_runRounds scheduler players
    (fun final => event ∈ final.application.config.cut.completed)
    (horizon - start.environmentRecall.length) start stopped supported
  have stoppedBounded : stopped.environmentRecall.length ≤ horizon := by omega
  have startSupported : start ∈ (app.roundsFrom (initialLaw setup) scheduler players
      start.environmentRecall.length).support := by
    rw [recallLength]
    exact reached
  have stoppedSupported := app.roundsFrom_runUntil scheduler players (initialLaw setup)
    (fun final => event ∈ final.application.config.cut.completed)
    (horizon - start.environmentRecall.length) start stopped startSupported supported
  have retained : app.PolicyInvariant players (fun current => entry ∈ current.recall owner) := {
    respond := fun current actor response present _ =>
      app.respond_recall_mono current actor owner response present
    environment := fun current next command present moved => by
      rw [app.environmentStep_recall current next command moved]
      exact present }
  have memberStopped := retained.runRounds scheduler used start stopped member rounds
  have recordedStopped := ((runtime setup).eventRecorded_iff leaks _ event).mpr
    ⟨entry, memberStopped, named⟩
  have noMiss := sourceServiceTurnPolicy_recorded_decision_no_miss contract players owner timing
    profile follows _ stoppedBounded stopped stoppedSupported event owned recordedStopped
  obtain ⟨stoppedTrace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
    _ stoppedBounded stopped stoppedSupported
  have once := (serialFacts_roundsFrom contract players owner timing profile follows
    _ stoppedBounded stopped stoppedSupported).2.1
  obtain ⟨earlier, later, split⟩ := List.mem_iff_append.mp memberStopped
  have sole := recalled_call_sole stoppedTrace owner event once entry message named emitted authored
    earlier later split
  have accepted := (prescribed_packet_settles setup leaks contract.inclusion stoppedTrace event
    owner owned earlier later entry message split call sole).2 complete
  exact ⟨memberStopped, complete, accepted, noMiss⟩

end Vegas
