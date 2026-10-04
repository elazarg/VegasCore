/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceOwnerSettled
import Vegas.Game.SourceServiceRetainedSlots
import Vegas.Game.SourceServiceAudit
import Vegas.Pending.ReactiveDecisionOrigin

/-! # Actual settlement of unmarked canonical packets

Canonical responses have stable content and use one identifier per owned event.
Those facts do not require a delivery bound. A completed unmarked event has an
actual accepting owner packet, so uniqueness identifies that receipt with its
canonical packet. Earlier timely calls may have been outside their protected
inclusion window. Partial observation and private opportunity risk are allowed.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability
  GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private def packetContent (execution : (application setup leaks).Execution)
    (message : Message Player (WitnessedPacket (graph setup))) : Prop :=
  ∃ event, message.payload.call.event? (graph setup) = some event ∧
    ((execution.application.config.cut.Ready event ∧
        PendingContent setup execution.application message) ∨
      (event ∈ execution.application.config.cut.completed ∧
        ((runtime setup).settledRecord leaks execution).SettledContent message))

omit [Fintype Player] in
private theorem packetContent_respond
    {execution : (application setup leaks).Execution}
    {message : Message Player (WitnessedPacket (graph setup))}
    (content : packetContent execution message) (who : Player)
    (response : (application setup leaks).Action) :
    packetContent (execution.respond (application setup leaks) who response) message := by
  obtain ⟨configEq, publicEq⟩ := (runtime setup).reactive_respond_application leaks execution
    who response
  obtain ⟨event, named, ⟨ready, pending⟩ | ⟨completed, settled⟩⟩ := content
  · exact ⟨event, named, Or.inl ⟨configEq ▸ ready,
      pendingContent_congr (congrArg PublicView.observation publicEq) pending⟩⟩
  · refine ⟨event, named, Or.inr ⟨configEq ▸ completed, ?_⟩⟩
    unfold settledRecord at settled ⊢
    rw [publicEq, (application setup leaks).respond_receipts]
    exact settled

omit [Fintype Player] in
private theorem packetContent_environment
    {execution next : (application setup leaks).Execution}
    {command : (application setup leaks).Command}
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support)
    {message : Message Player (WitnessedPacket (graph setup))}
    (content : packetContent execution message) : packetContent next message := by
  have step := contractStep_environment (runtime setup) leaks execution next command reached
  obtain ⟨event, named, ⟨ready, pending⟩ | ⟨completed, settled⟩⟩ := content
  · rcases step with ⟨configEq, _⟩ | ⟨other, otherReady, action, supported⟩
    · have observationEq : next.application.publicView.observation =
          execution.application.publicView.observation := by
        change (graph setup).publicObserve next.application.config =
          (graph setup).publicObserve execution.application.config
        rw [configEq]
      exact ⟨event, named, Or.inl ⟨configEq ▸ ready,
        pendingContent_congr observationEq pending⟩⟩
    · cases ready_unique _ otherReady ready
      refine ⟨event, named, Or.inr ⟨?_, ?_⟩⟩
      · rw [execution.application.config.step_cut event otherReady action
          next.application.config supported]
        exact (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl)
      · exact settledContent_of_pending execution.application next.application next.receipts
          message event named otherReady action supported pending
  · exact ⟨event, named, Or.inr ⟨step.completed_mono completed,
      settledContent_step step execution.receipts next.receipts message event named completed
        settled⟩⟩

private theorem canonical_packet_facts
    (bounds : MessageBounds (graph setup)) {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} :
    ∀ {state} (_ : ((bounds.canonicalMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).Trace state),
      ReactiveApplication.serviceInvariant
        (fun execution => (∀ who, OwnFreshCalls setup leaks (fun _ => 0) execution who) ∧
          (∀ who, FreshCallsConform setup leaks execution who) ∧
          (∀ who, OneCallPerEvent setup leaks execution who) ∧
          ∀ message, Emitted setup leaks execution message → packetContent execution message)
        state
  | _, .start => trivial
  | _, .extend (source := before) prior joint legal reached => by
      let app := application setup leaks
      let menu := bounds.canonicalMenu (runtime setup) leaks
      have valid := canonical_packet_facts bounds prior
      have rawPrior := menu.toRawTrace (initialLaw setup) horizon scheduler prior
      cases before with
      | none =>
          obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ reached
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro who entry member
            cases member
          · intro who entry member
            cases member
          · intro who entry member
            cases member
          · intro message emitted
            simp only [Emitted, ReactiveApplication.Execution.initial, MessageNetwork.empty]
              at emitted
            cases emitted
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          change (∀ who, OwnFreshCalls setup leaks (fun _ => 0) execution who) ∧
            (∀ who, FreshCallsConform setup leaks execution who) ∧
            (∀ who, OneCallPerEvent setup leaks execution who) ∧
            (∀ message, Emitted setup leaks execution message → packetContent execution message)
            at valid
          cases actor with
          | some who =>
              obtain ⟨response, choice, member⟩ : ∃ response, joint who = some response ∧
                  response ∈ menu.actions who (execution.recall who)
                    (execution.observe app who) := by
                have chosen := legal.2 who
                cases selected : joint who with
                | none => rw [selected] at chosen; exact (chosen rfl).elim
                | some response =>
                    rw [selected] at chosen
                    exact ⟨response, rfl, chosen.2⟩
              obtain ⟨atTurn, slots⟩ := retainedCanonicalSlots_history bounds _ prior who
              have fresh : ∀ material, response.transmission = some material →
                  (runtime setup).freshServiceEnvelope execution.application.publicView
                    ⟨(who, execution.network.nextSerial who), app.packet
                      (app.submit execution.application who material) who
                        (execution.network.known who) material⟩ := by
                intro material submitted
                obtain ⟨event, action, turn, _, _, timely, unsent, _, decision⟩ :=
                  bounds.canonicalActions_submission (runtime setup) leaks who _ _ response
                    member material submitted
                exact canonicalServiceDecision_freshServiceEnvelope rawPrior event turn timely
                  (canonicalSlot_fresh_of_used rawPrior who atTurn slots event turn unsent)
                  action material (by rw [← decision]; exact submitted)
              have ownFacts := ownerCallFacts_respond execution who response (valid.1 who)
                (valid.2.1 who) (valid.2.2.1 who)
                (bounds.canonicalActions_firstSubmission (runtime setup) leaks who _ _ response
                  member) fresh (by
                  intro event submitted
                  cases transmitted : response.transmission with
                  | none =>
                      simp only [EventGraphRuntime.submittedEvent?, transmitted] at submitted
                      cases submitted
                  | some material =>
                      have named := submitted
                      unfold EventGraphRuntime.submittedEvent? at named
                      rw [transmitted] at named
                      exact fresh_fits _ _ event named (fresh material transmitted))
              cases (PMF.mem_support_pure_iff _ _).mp reached
              simp only [choice, Option.getD_some]
              refine ⟨fun observer => ?_, fun observer => ?_, fun observer => ?_, ?_⟩
              · by_cases same : observer = who
                · subst observer; exact ownFacts.1
                · unfold OwnFreshCalls
                  rw [app.respond_recall_other execution who observer same response]
                  exact valid.1 observer
              · by_cases same : observer = who
                · subst observer; exact ownFacts.2.1
                · unfold FreshCallsConform
                  rw [app.respond_recall_other execution who observer same response]
                  exact valid.2.1 observer
              · by_cases same : observer = who
                · subst observer; exact ownFacts.2.2
                · unfold OneCallPerEvent
                  rw [app.respond_recall_other execution who observer same response]
                  exact valid.2.2.1 observer
              · intro message emitted
                have facts := settledFacts_history (initialLaw setup) horizon scheduler rawPrior
                rcases respond_emitted facts who response message emitted with old |
                    ⟨material, submitted, rfl⟩
                · exact packetContent_respond (valid.2.2.2 message old) who response
                · have conforms := fresh material submitted
                  obtain ⟨event, named, readyView⟩ :=
                    (runtime setup).freshServiceEnvelope_ready _ _ conforms
                  obtain ⟨configEq, publicEq⟩ :=
                    (runtime setup).reactive_respond_application leaks execution who response
                  exact ⟨event, named, Or.inl ⟨configEq ▸
                    (execution.application.publicView_eventReady event).mp readyView,
                    pendingContent_congr (congrArg PublicView.observation publicEq)
                      (pendingContent_of_fresh execution.application _ conforms)⟩⟩
          | none =>
              cases remaining with
              | zero =>
                  cases (PMF.mem_support_pure_iff _ _).mp reached
                  exact valid
              | succ remaining =>
                  obtain ⟨command, _, moved⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  have recallEq := app.environmentStep_recall execution next command supported
                  refine ⟨fun who => ?_, fun who => ?_, fun who => ?_, ?_⟩
                  · unfold OwnFreshCalls
                    rw [recallEq]
                    exact valid.1 who
                  · unfold FreshCallsConform
                    rw [recallEq]
                    exact valid.2.1 who
                  · unfold OneCallPerEvent
                    rw [recallEq]
                    exact valid.2.2.1 who
                  · intro message emitted
                    have old : Emitted setup leaks execution message := by
                      unfold Emitted at emitted ⊢
                      rw [← app.environmentStep_inputs execution next command supported]
                      exact emitted
                    exact packetContent_environment supported (valid.2.2.2 message old)

/-- Every actual canonical packet of an owner with no public decision miss is
permitted by the current settled record. No protected-inclusion premise is
needed for already accepted late calls. -/
theorem sourceServiceCanonicalHistory_packets_permitted
    (bounds : MessageBounds (graph setup)) {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (control : (application setup leaks).Control)
    (trace : ((bounds.canonicalMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control)) (who : Player)
    (noMiss : control.execution.application.publicView.missedDecisionBy who = false) :
    ∀ message, message.sender = who → Emitted setup leaks control.execution message →
      ((runtime setup).settledRecord leaks control.execution).permits message = true := by
  let app := application setup leaks
  let menu := bounds.canonicalMenu (runtime setup) leaks
  have rawTrace := menu.toRawTrace (initialLaw setup) horizon scheduler trace
  have facts := legalFacts setup leaks horizon scheduler control rawTrace
  obtain ⟨_calls, conform, once, content⟩ := canonical_packet_facts bounds trace
  have initialized := rawTrace
  rw [initialLaw_eq_inputs] at initialized
  have origins := (runtime setup).completedDecisionRecall_history leaks
    (setup.initialLaw.map setup.eventInputs) horizon scheduler initialized
  intro message authored emitted
  obtain ⟨event, named, ⟨ready, _pending⟩ | ⟨completed, settled⟩⟩ := content message emitted
  · exact SettledRecord.permits_of_unsettled _ message event named fun inside =>
      ready.1 ((control.execution.application.config.history_exact event).mp inside)
  · obtain ⟨entry, member, material, transmission, issued, state, known, packet⟩ :=
      facts.provenance.inputs message emitted
    rw [authored] at member
    have fresh := conform who entry member material message transmission issued
    obtain ⟨actual, eventEq, _ready, owned⟩ :=
      (runtime setup).freshServiceEnvelope_owned _ message fresh
    rw [named] at eventEq
    cases Option.some.inj eventEq
    rw [authored] at owned
    have unmarked := (control.execution.application.publicView.missedDecisionBy_eq_false_iff
      who).mp noMiss event owned
    obtain ⟨accepted, output, acceptedAuthor, acceptedNamed, receipt⟩ :=
      origins event who owned completed unmarked
    have emittedAccepted : Emitted setup leaks control.execution accepted := by
      have input : accepted ∈ control.execution.network.inputs.filter
          (fun packet => packet.sender = who) := by
        rw [facts.inputs who]
        exact output
      exact List.mem_filter.mp input |>.1
    obtain ⟨other, otherMember, otherMaterial, otherTransmission, otherIssued, otherState,
      otherKnown, otherPacket⟩ := facts.provenance.inputs accepted emittedAccepted
    rw [acceptedAuthor] at otherMember
    have firstNamed : (runtime setup).submittedEvent? leaks entry.action = some event := by
      rw [submittedEvent_of_issued transmission packet]
      exact named
    have secondNamed : (runtime setup).submittedEvent? leaks other.action = some event := by
      rw [submittedEvent_of_issued otherTransmission otherPacket]
      exact acceptedNamed
    have identical := once who other otherMember entry member event accepted message secondNamed
      firstNamed otherIssued issued
    rw [identical] at receipt
    exact SettledRecord.permits_of_accepted _ message event named receipt settled

/-- Authentic partial sampling collects no owner charge on an actual canonical
history with no public owner miss. Private opportunity risk is unrestricted. -/
theorem sourceServiceCanonicalHistory_audit_clear
    (bounds : MessageBounds (graph setup)) {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (control : (application setup leaks).Control)
    (trace : ((bounds.canonicalMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control)) (who : Player)
    (noMiss : control.execution.application.publicView.missedDecisionBy who = false)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual) :
    TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) (some control) who = 0 := by
  let app := application setup leaks
  have permitted := sourceServiceCanonicalHistory_packets_permitted bounds control trace who
    noMiss
  have inputs := app.stateTraffic_inputs (initialLaw setup) horizon scheduler
    ((bounds.canonicalMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace)
  change (app.executionTraffic control.execution).map ReactiveApplication.TrafficRecord.envelope =
    control.execution.network.inputs at inputs
  unfold sourceServiceAudit
  rw [(runtime setup).serviceAudit_charge, noMiss]
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply app.sampledTrafficAudit_sound
  · exact authentic _
  · intro record member authored
    apply permitted record.envelope authored
    unfold Emitted
    rw [← inputs]
    exact List.mem_map.mpr ⟨record, member, rfl⟩

end Vegas
