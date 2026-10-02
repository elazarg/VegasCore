/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceSettledSound

/-! # Settled packet soundness for one prescribed owner

Only the selected owner follows the turn-counted source policy. Every other
player may use arbitrary raw responses. Protected sole calls settle with the
content checked by the actual contract record, and their content persists
through later service steps. No watcher sampling or collection assumption is
used. Silent deferrals may still cause public binding omissions.
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory.Math.Probability GameTheory.Protocol Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A completed event accepts the selected owner's protected sole packet.
All conformance and once-per-event premises concern that owner alone. -/
theorem owner_packet_accepted {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {bound : (graph setup).EventId → Nat}
    (inclusion : ProtectedInclusion (runtime setup) leaks (initialLaw setup) horizon scheduler
      bound)
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (who : Player) (calls : OwnFreshCalls setup leaks bound control.execution who)
    (conform : FreshCallsConform setup leaks control.execution who)
    (once : OneCallPerEvent setup leaks control.execution who)
    (message : Message Player (WitnessedPacket (graph setup))) (authored : message.sender = who)
    (emitted : Emitted setup leaks control.execution message) (event : (graph setup).EventId)
    (named : message.payload.call.event? (graph setup) = some event)
    (completed : event ∈ control.execution.application.config.cut.completed) :
    (message.id, true) ∈ control.execution.receipts := by
  let app := application setup leaks
  have facts := legalFacts setup leaks _ _ control trace
  obtain ⟨entry, entryMember, material, transmission, entryEmitted, state, known, packet⟩ :=
    facts.provenance.inputs message emitted
  change entry ∈ control.execution.recall message.id.1 at entryMember
  change message.id.1 = who at authored
  rw [authored] at entryMember
  have fresh := conform entry entryMember material message transmission entryEmitted
  obtain ⟨freshEvent, freshNamed, readyView, owned⟩ :=
    (runtime setup).freshServiceEnvelope_owned _ message fresh
  rw [named] at freshNamed
  cases Option.some.inj freshNamed
  change (graph setup).actor? event = some message.id.1 at owned
  rw [authored] at owned
  obtain ⟨callEvent, issued, issuedEq, _, _, entryEvent, fits⟩ :=
    calls entry entryMember material transmission
  rw [entryEmitted] at issuedEq
  cases Option.some.inj issuedEq
  have callEventEq : callEvent = event := by
    rw [submittedEvent_of_issued transmission packet, named] at entryEvent
    exact Option.some.inj entryEvent.symm
  subst callEvent
  obtain ⟨earlier, later, split⟩ := List.mem_iff_append.mp entryMember
  have call : FreshCall setup leaks who event bound entry message := {
    fresh := ⟨material, transmission⟩
    emitted := entryEmitted
    authored := authored
    addressed := named
    ready := readyView
    fits := fits
    conforming := EventGraphRuntime.freshServiceEnvelope.acceptable (runtime setup) fresh }
  have sole : ∀ other ∈ earlier ++ later,
      ¬ EmitsOtherFor (runtime setup) leaks other event message.id := by
    intro other otherMember ⟨replayed, emittedOther, replayedAuthor, replayedAddressed,
      differentId⟩
    have otherRecall : other ∈ control.execution.recall who := by
      rw [split]
      rcases List.mem_append.mp otherMember with inside | inside
      · exact List.mem_append_left _ inside
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ inside)
    have output : replayed ∈ app.outputs (control.execution.recall who) :=
      List.mem_filterMap.mpr ⟨other, otherRecall, emittedOther⟩
    rw [← facts.inputs who] at output
    have replayMember := (List.mem_filter.mp output).1
    obtain ⟨issuer, issuerMember, _, issuerTransmission, issuerEmitted, _, _, issuerPacket⟩ :=
      facts.provenance.inputs replayed replayMember
    change issuer ∈ control.execution.recall replayed.id.1 at issuerMember
    change replayed.id.1 = message.id.1 at replayedAuthor
    rw [replayedAuthor, authored] at issuerMember
    have issuerEvent : (runtime setup).submittedEvent? leaks issuer.action = some event := by
      rw [submittedEvent_of_issued issuerTransmission issuerPacket]
      exact replayedAddressed
    exact differentId (once issuer issuerMember entry entryMember event _ _ issuerEvent
      entryEvent issuerEmitted entryEmitted)
  have settles : SettlesFreshCalls setup leaks who event bound control.execution :=
    settlesFreshCalls_history setup leaks inclusion who event owned trace
  exact (settles earlier entry later message split call sole).1 completed

/-- A service command preserves good content for a packet of one prescribed
owner, without any conformance premise on foreign packets. -/
theorem SettledGood.owner_environment {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {bound : (graph setup).EventId → Nat}
    (inclusion : ProtectedInclusion (runtime setup) leaks (initialLaw setup) horizon scheduler
      bound)
    {execution next : (application setup leaks).Execution}
    {command : (application setup leaks).Command} (facts : SettledFacts setup leaks execution)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support)
    {remaining : Nat}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, command.actor? (application setup leaks), next⟩))
    (who : Player) (calls : OwnFreshCalls setup leaks bound next who)
    (conform : FreshCallsConform setup leaks next who)
    (once : OneCallPerEvent setup leaks next who)
    {message : Message Player (WitnessedPacket (graph setup))} (authored : message.sender = who)
    (emitted : Emitted setup leaks execution message)
    (good : SettledGood setup leaks execution message) :
    SettledGood setup leaks next message := by
  obtain ⟨inputsEq, _, _⟩ := environmentStep_shape setup leaks execution next command reached
  have nextEmitted : Emitted setup leaks next message := by
    unfold Emitted at emitted ⊢
    rw [inputsEq]
    exact emitted
  have step := contractStep_environment (runtime setup) leaks execution next command reached
  have prefixOf := (application setup leaks).environmentStep_receipts_prefix execution next
    command reached
  obtain ⟨event, named, ⟨ready, unaccepted, pending⟩ | ⟨accepted, completed, content⟩⟩ := good
  · rcases step with ⟨configEq, _, _, _⟩ | ⟨other, otherReady, action, member⟩
    · by_cases acceptedNow : (message.id, true) ∈ next.receipts
      · obtain ⟨after, handled, applicationEq⟩ :=
          newly_accepted facts reached emitted unaccepted acceptedNow
        obtain ⟨_, acceptedEvent, acceptedNamed, _, acceptedCompleted, _⟩ :=
          accepted_inclusion execution.application after message handled
        rw [named] at acceptedNamed
        cases Option.some.inj acceptedNamed
        rw [← applicationEq, configEq] at acceptedCompleted
        exact (ready.1 acceptedCompleted).elim
      · have observationEq : next.application.publicView.observation =
            execution.application.publicView.observation := by
          change (graph setup).publicObserve next.application.config =
            (graph setup).publicObserve execution.application.config
          rw [configEq]
        exact ⟨event, named, Or.inl ⟨configEq ▸ ready, acceptedNow,
          pendingContent_congr observationEq pending⟩⟩
    · cases ready_unique _ otherReady ready
      have completedNext : event ∈ next.application.config.cut.completed := by
        rw [execution.application.config.step_cut event otherReady action
          next.application.config member]
        exact (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl)
      have acceptedNow := owner_packet_accepted inclusion trace who calls conform once message
        authored nextEmitted event named completedNext
      obtain ⟨after, handled, applicationEq⟩ :=
        newly_accepted facts reached emitted unaccepted acceptedNow
      obtain ⟨stepEvent, stepNamed, stepReady, stepAction, stepMember⟩ := handle_config_mem_step
        (runtime setup) execution.application after _ (reactiveHandle_call handled)
      have sameEvent : stepEvent = event := Option.some.inj (stepNamed.symm.trans named)
      subst stepEvent
      refine ⟨event, named, Or.inr ⟨acceptedNow, completedNext, ?_⟩⟩
      unfold settledRecord
      rw [applicationEq]
      exact settledContent_of_pending execution.application after next.receipts message event
        named stepReady stepAction stepMember pending
  · refine ⟨event, named, Or.inr ⟨prefixOf.subset accepted, step.completed_mono completed, ?_⟩⟩
    exact settledContent_step step execution.receipts next.receipts message event named
      completed content

/-- An arbitrary response preserves prior good packets of the selected owner;
only a fresh response authored by that owner needs a conformance premise. -/
theorem owner_good_response {execution : (application setup leaks).Execution}
    (facts : SettledFacts setup leaks execution) (who responder : Player)
    (response : (application setup leaks).Action)
    (prior : ∀ message, message.sender = who → Emitted setup leaks execution message →
      SettledGood setup leaks execution message)
    (fresh : responder = who → ∀ material, response.transmission = some material →
      (runtime setup).freshServiceEnvelope execution.application.publicView
        ⟨(responder, execution.network.nextSerial responder),
          (application setup leaks).packet ((application setup leaks).submit
            execution.application responder material) responder
              (execution.network.known responder) material⟩) :
    ∀ message, message.sender = who →
      Emitted setup leaks (execution.respond (application setup leaks) responder response)
        message →
      SettledGood setup leaks (execution.respond (application setup leaks) responder response)
        message := by
  let app := application setup leaks
  obtain ⟨configEq, publicEq⟩ := (runtime setup).reactive_respond_application leaks execution
    responder response
  intro message authored emitted
  rcases respond_emitted facts responder response message emitted with before |
      ⟨material, submitted, rfl⟩
  · exact (prior message authored before).respond responder response
  · have conforms := fresh authored material submitted
    obtain ⟨event, named, readyView⟩ :=
      (runtime setup).freshServiceEnvelope_ready _ _ conforms
    refine ⟨event, named, Or.inl ⟨?_, ?_, ?_⟩⟩
    · rw [configEq]
      exact (execution.application.publicView_eventReady event).mp readyView
    · rw [app.respond_receipts execution responder response]
      intro accepted
      obtain ⟨other, otherMember, same⟩ := List.mem_map.mp (facts.receipt_published accepted)
      have bound := facts.serials.ledger other otherMember
      rw [same] at bound
      exact Nat.lt_irrefl _ bound
    · exact pendingContent_congr (congrArg PublicView.observation publicEq)
        (pendingContent_of_fresh execution.application _ conforms)

/-- Every actual packet of the selected owner is either pending with stable
content or accepted with the content checked by the actual record. -/
theorem sourceServiceTurnPolicy_settledGood {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (players : Player → (application setup leaks).Policy) (who : Player)
    {turns : Nat} (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns timing profile who)
    (count : Nat) (within : count ≤ horizon) (execution : (application setup leaks).Execution)
    (reached : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support) :
    ∀ message, message.sender = who → Emitted setup leaks execution message →
      SettledGood setup leaks execution message := by
  let app := application setup leaks
  induction count generalizing execution with
  | zero =>
      obtain ⟨state, _, supported⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      cases (PMF.mem_support_pure_iff _ _).mp supported
      intro message _ emitted
      simp only [Emitted, ReactiveApplication.Execution.initial, MessageNetwork.empty] at emitted
      cases emitted
  | succ count ih =>
      have fullReached := reached
      rw [app.roundsFrom_succ (initialLaw setup) scheduler players count] at reached
      obtain ⟨prior, priorMem, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have good := ih (by omega) prior priorMem
      obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
        count (by omega) prior priorMem
      rw [show horizon - count = (horizon - (count + 1)) + 1 by omega] at trace
      have facts := settledFacts_history (initialLaw setup) horizon scheduler trace
      obtain ⟨calls, once, _⟩ := serialFacts_roundsFrom contract players who timing profile follows
        count (by omega) prior priorMem
      have conform : FreshCallsConform setup leaks prior who :=
        fun entry member material message transmission emitted =>
          sourceServiceTurnPolicy_freshServiceEnvelope scheduler players who timing profile
            follows count prior priorMem entry member material transmission message emitted
      obtain ⟨command, selected, middle, observed, effect⟩ := round_cases setup leaks moved
      obtain ⟨middleTrace⟩ := app.raw_trace_environment (initialLaw setup) horizon scheduler
        (horizon - (count + 1)) prior middle command trace selected observed
      have recallEq := app.environmentStep_recall prior middle command observed
      have callsMiddle : OwnFreshCalls setup leaks bound middle who := by
        unfold OwnFreshCalls
        rw [recallEq]
        exact calls
      have onceMiddle : OneCallPerEvent setup leaks middle who := by
        unfold OneCallPerEvent
        rw [recallEq]
        exact once
      have conformMiddle : FreshCallsConform setup leaks middle who := by
        unfold FreshCallsConform
        rw [recallEq]
        exact conform
      have middleGood : ∀ message, message.sender = who → Emitted setup leaks middle message →
          SettledGood setup leaks middle message := by
        intro message authored emitted
        have emittedBefore : Emitted setup leaks prior message := by
          unfold Emitted at emitted ⊢
          rw [← app.environmentStep_inputs prior middle command observed]
          exact emitted
        exact (good message authored emittedBefore).owner_environment contract.inclusion facts
          observed middleTrace who callsMiddle conformMiddle onceMiddle authored emittedBefore
      rcases effect with ⟨_, rfl⟩ | ⟨responder, active, response, chosen, rfl⟩
      · exact middleGood
      · apply owner_good_response (settledFacts_history (initialLaw setup) horizon scheduler
          middleTrace) who responder response middleGood
        intro same material submitted
        subst responder
        let message : Message Player (WitnessedPacket (graph setup)) :=
          ⟨(who, middle.network.nextSerial who),
            app.packet (app.submit middle.application who material) who
              (middle.network.known who) material⟩
        let entry : app.PlayerEntry := ⟨middle.observe app who, response, some message⟩
        have entryMember : entry ∈ (middle.respond app who response).recall who := by
          cases response
          cases submitted
          simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        exact sourceServiceTurnPolicy_freshServiceEnvelope scheduler players who timing profile
          follows (count + 1) _ fullReached entry entryMember material submitted message rfl

/-- Owner-local verdict soundness at every supported completed scheduler round.
No assumption constrains another player's response policy. -/
theorem sourceServiceTurnPolicy_owner_settled {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (players : Player → (application setup leaks).Policy) (who : Player)
    {turns : Nat} (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns timing profile who)
    (count : Nat) (within : count ≤ horizon) (execution : (application setup leaks).Execution)
    (reached : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support) :
    ∀ record ∈ (application setup leaks).executionTraffic execution,
      record.envelope.sender = who →
        ((runtime setup).settledRecord leaks execution).permits record.envelope = true := by
  let app := application setup leaks
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players count
    within execution reached
  have inputs := app.stateTraffic_inputs (initialLaw setup) horizon scheduler trace
  change (app.executionTraffic execution).map ReactiveApplication.TrafficRecord.envelope =
    execution.network.inputs at inputs
  intro record member authored
  have emitted : Emitted setup leaks execution record.envelope := by
    unfold Emitted
    rw [← inputs]
    exact List.mem_map.mpr ⟨record, member, rfl⟩
  exact (sourceServiceTurnPolicy_settledGood contract players who timing profile follows count
    within execution reached record.envelope authored emitted).permits

/-- The actual record at a pending activation is sound for the same owner.
Activation changes its private message sample, but not packet verdicts. -/
theorem sourceServiceTurnPolicy_owner_settled_roundSupported {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (players : Player → (application setup leaks).Policy) (who : Player)
    {turns : Nat} (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns timing profile who)
    (control : (application setup leaks).Control)
    (reached : (application setup leaks).RoundSupported (initialLaw setup) horizon scheduler
      players (some control)) :
    ∀ record ∈ (application setup leaks).executionTraffic control.execution,
      record.envelope.sender = who →
        ((runtime setup).settledRecord leaks control.execution).permits record.envelope = true := by
  obtain ⟨remaining, actor, execution⟩ := control
  cases actor with
  | none =>
      have within : execution.environmentRecall.length ≤ horizon := by
        have lengths := reached.1
        change execution.environmentRecall.length + remaining = horizon at lengths
        omega
      exact sourceServiceTurnPolicy_owner_settled contract players who timing profile follows
        _ within execution reached.2
  | some responder =>
      obtain ⟨lengthEq, count, prior, command, _, priorMem, _, active, moved⟩ := reached
      have permitted := sourceServiceTurnPolicy_owner_settled contract players who timing profile
        follows count (by omega) prior priorMem
      rw [(application setup leaks).executionTraffic_environment prior execution command moved]
      cases command with
      | activate actor =>
          have receiptsEq : execution.receipts = prior.receipts := by
            simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at moved
            obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ moved
            rfl
          have recordEq : (runtime setup).settledRecord leaks execution =
              (runtime setup).settledRecord leaks prior := by
            unfold settledRecord
            rw [activation_application setup leaks prior execution actor moved, receiptsEq]
          rw [recordEq]
          exact permitted
      | wait | «include» id | application command => cases active

end Vegas
