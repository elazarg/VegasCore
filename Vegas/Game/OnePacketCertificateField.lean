/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketCanonicalAcceptance
import Vegas.Game.OnePacketFactorization

/-! # The field certified by an owned evidence request

A response of the one-packet game is normal for the effective menu, so a
request for owned evidence resolves: the envelope the response emits carries
exactly the requested fact. Every emitted token was issued from the public view
the sender saw, so the direct predecessors of its event had completed then, and
they stay completed (`Vegas.ownedRequestsEmitted_history`).

Every envelope in the network passes the count verdict. Evidence rules out a
commitment, so an envelope carrying an owned fact is an opening carrying exactly
its own certificate: it names a resolve event of the sender, with a valid token,
and the sender's own signed data binds the opened handle to the binding field of
that event. A commitment names a prepared handle of its sender that no earlier
commitment of the sender named, so two commitments never name one handle and a
prepared handle is never an initial one. A handle accepted for a binding event
was named by a commitment of its owner, and a handle accepted for an initial
binding input is that input's fixed handle. Hence the handle of an owned fact
in recall is accepted at most at the binding field of the opened event, and that
event is ready or completed (`Vegas.certificate_field`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

variable (setup leaks) in
/-- **Owned requests are emitted.** Every recalled transmission emitted an
envelope; when it requested owned evidence, the envelope carries exactly that
evidence; and the direct predecessors of the event its token names have
completed. -/
def OwnedRequestsEmitted (execution : (application setup leaks).Execution) : Prop :=
  ∀ who, ∀ recalled ∈ execution.recall who, ∀ submission,
    recalled.action.transmission = some submission →
    ∃ message, recalled.emitted = some message ∧
      (∀ fact, submission.evidence = .owned fact → message.payload.evidence = some fact) ∧
      ∀ event, message.payload.token = some ⟨event⟩ →
        (graph setup).order.predecessors event ⊆ execution.application.config.cut.completed

/-- A normal owned request resolves to its fact. -/
private theorem resolve_owned_of_normalize {who : Player}
    {candidates : CandidateSlot (graph setup) → CommitmentCandidate (Raw L)}
    {known : List (Message Player (WitnessedPacket (graph setup)))}
    {fact : OpeningFact (graph setup)}
    (normal : (EvidenceRequest.owned fact).normalize who candidates known = .owned fact) :
    (EvidenceRequest.owned fact).resolve who candidates known = some fact := by
  cases resolved : (EvidenceRequest.owned fact).resolve who candidates known with
  | none =>
      rw [EvidenceRequest.normalize, resolved] at normal
      cases normal
  | some found =>
      have selected := resolved
      simp only [EvidenceRequest.resolve] at selected
      split at selected
      · exact selected.symm ▸ rfl
      · cases selected

/-- An issued token names an event whose direct predecessors have completed. -/
private theorem predecessors_completed_of_tokenFor (state : EventGraphRuntime.State (graph setup))
    (packet : Payload (graph setup)) (event : (graph setup).EventId)
    (issued : state.publicView.tokenFor packet = some ⟨event⟩) :
    (graph setup).order.predecessors event ⊆ state.config.cut.completed := by
  unfold PublicView.tokenFor at issued
  obtain ⟨named, _, token⟩ := Option.bind_eq_some_iff.mp issued
  obtain ⟨same, complete⟩ := (state.publicView.readinessToken?_eq_some_iff named ⟨event⟩).mp token
  cases same
  intro predecessor member
  exact (state.config.history_exact predecessor).mp (complete predecessor member)

/-- A configuration step keeps completed events completed. -/
private theorem completed_of_configStep {before after : (graph setup).Config}
    (step : ConfigStep setup before after) {event : (graph setup).EventId}
    (completed : event ∈ before.cut.completed) : event ∈ after.cut.completed := by
  rcases step with same | ⟨other, ready, action, member⟩
  · rw [same]
    exact completed
  · rw [before.step_cut other ready action after member, EventOrder.Cut.mem_complete]
    exact Or.inr completed

variable (leaks) in
/-- Owned requests stay emitted along every environment step. -/
theorem ownedRequestsEmitted_environment
    (execution next : (application setup leaks).Execution)
    (command : (application setup leaks).Command)
    (valid : OwnedRequestsEmitted setup leaks execution)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support) :
    OwnedRequestsEmitted setup leaks next := by
  have step := environmentStep_configStep setup leaks execution next command reached
  intro who recalled member submission sent
  rw [(application setup leaks).environmentStep_recall execution next command reached] at member
  obtain ⟨message, emitted, evidence, token⟩ := valid who recalled member submission sent
  exact ⟨message, emitted, evidence, fun event named predecessor completed =>
    completed_of_configStep step (token event named completed)⟩

variable [Fintype Player] (bounds : MessageBounds (graph setup))

/-- Owned requests stay emitted along every one-packet response. -/
theorem ownedRequestsEmitted_respond (execution : (application setup leaks).Execution)
    (valid : OwnedRequestsEmitted setup leaks execution) (who : Player)
    (action : (application setup leaks).Action)
    (member : action ∈ (bounds.onePacketMenu (runtime setup) leaks).actions who
      (execution.recall who) (execution.observe (application setup leaks) who)) :
    OwnedRequestsEmitted setup leaks (execution.respond (application setup leaks) who action) := by
  let app := application setup leaks
  have configEq := ((runtime setup).reactive_respond_application leaks execution who action).1
  intro observer recalled entryMember submission sent
  rw [respond_recall (runtime setup) leaks] at entryMember
  split at entryMember
  · rename_i same
    subst same
    rcases List.mem_append.mp entryMember with old | new
    · obtain ⟨message, emitted, evidence, token⟩ := valid observer recalled old submission sent
      exact ⟨message, emitted, evidence, fun event named => by
        rw [configEq]
        exact token event named⟩
    · obtain rfl := List.mem_singleton.mp new
      rcases action with ⟨transmission⟩
      change transmission = some submission at sent
      subst sent
      have normal := ((bounds.menu_mem (runtime setup) leaks observer _ _ _).mp
        ((bounds.mem_onePacketActions (runtime setup) leaks observer _ _ _).mp member).1).2
      have normalEvidence := congrArg (fun response : app.Action =>
        response.transmission.map WitnessedSubmission.evidence) normal
      simp only [ReactiveApplication.SubmissionNormalization.action,
        Option.map_some] at normalEvidence
      refine ⟨_, rfl, fun fact owned => ?_, fun event named => ?_⟩
      · have request := Option.some.inj normalEvidence
        change submission.evidence.normalize observer (submission.call.candidateAfter observer
          (fun slot => execution.application.candidates.lookup (observer, slot)))
            (ReactiveApplication.ResponseMenu.knownPackets (execution.recall observer)
              (execution.observe app observer)) = submission.evidence at request
        rw [owned] at request
        have resolved := resolve_owned_of_normalize request
        change (submission.emit (submitStep (submission.call.register execution.application
          observer) observer submission.call.packet) observer
            (execution.network.known observer)).evidence = some fact
        rw [WitnessedSubmission.emit_eq_resolve, owned,
          funext (submission.call.candidateAfter_eq observer execution.application)]
        exact resolved
      · rw [configEq]
        apply predecessors_completed_of_tokenFor execution.application submission.call.packet
        rw [← reactiveApplication_packet_token (runtime setup) leaks execution.application observer
          (execution.network.known observer) submission]
        exact named
  · obtain ⟨message, emitted, evidence, token⟩ :=
      valid observer recalled entryMember submission sent
    exact ⟨message, emitted, evidence, fun event named => by
      rw [configEq]
      exact token event named⟩

/-- **Owned requests are emitted along every history** of the one-packet game. -/
theorem ownedRequestsEmitted_history {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control)) :
    OwnedRequestsEmitted setup leaks control.execution :=
  (show (bounds.onePacketMenu (runtime setup) leaks).ServiceInvariant scheduler
      (OwnedRequestsEmitted setup leaks) from
    { respond := fun execution who action valid member =>
        ownedRequestsEmitted_respond bounds execution valid who action member
      environment := fun execution next command valid _ reached =>
        ownedRequestsEmitted_environment leaks execution next command valid reached }).history
    (initialLaw setup) horizon (fun _ _ _ _ member => (List.not_mem_nil member).elim) trace

/-- Along every history of the one-packet game, every packet a player recalls
emitting is in the network. -/
theorem output_mem_inputs_of_trace {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    (who : Player) (packet : Message Player (WitnessedPacket (graph setup)))
    (output : packet ∈ (application setup leaks).outputs (control.execution.recall who)) :
    packet ∈ control.execution.network.inputs := by
  have clean := (bounds.onePacketMenu_countClean (runtime setup) leaks scheduler).history
    (initialLaw setup) horizon (fun state _ => (runtime setup).countClean_initial leaks state)
    trace
  rw [← clean.1.1 who] at output
  exact (List.mem_filter.mp output).1

/-- **Commitments name fresh prepared handles of their sender.** Along every
history of the one-packet game, a commitment in the network names a prepared
handle of its sender that no earlier packet of the sender named. -/
theorem commitment_facts_of_trace {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    (packet : Message Player (WitnessedPacket (graph setup)))
    (input : packet ∈ control.execution.network.inputs) (named : (graph setup).EventId)
    (candidate : Handle (graph setup))
    (call : packet.payload.call = .commitment named candidate) :
    candidate.1 = packet.sender ∧ (∃ serial, candidate.2 = .prepared serial) ∧
      ∀ other, EarlierOwnPacket control.execution.network.inputs packet other →
        ∀ named', other.payload.call ≠ .commitment named' candidate := by
  have clean := (bounds.onePacketMenu_countClean (runtime setup) leaks scheduler).history
    (initialLaw setup) horizon (fun state _ => (runtime setup).countClean_initial leaks state)
    trace
  have correct := ((countPermits_eq_true_iff _ _).mp (clean.2 packet input)).2.1
  unfold CountCallCorrect at correct
  rw [call] at correct
  exact ⟨correct.2.2.1, correct.2.2.2.1, correct.2.2.2.2⟩

/-- **Commitments never share a handle.** Along every history of the one-packet
game, two commitments in the network never name one handle for two events. -/
theorem commitment_unique_of_trace {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    (first : Message Player (WitnessedPacket (graph setup)))
    (firstInput : first ∈ control.execution.network.inputs)
    (second : Message Player (WitnessedPacket (graph setup)))
    (secondInput : second ∈ control.execution.network.inputs)
    (firstEvent secondEvent : (graph setup).EventId) (candidate : Handle (graph setup))
    (firstCall : first.payload.call = .commitment firstEvent candidate)
    (secondCall : second.payload.call = .commitment secondEvent candidate) :
    firstEvent = secondEvent := by
  have clean := (bounds.onePacketMenu_countClean (runtime setup) leaks scheduler).history
    (initialLaw setup) horizon (fun state _ => (runtime setup).countClean_initial leaks state)
    trace
  obtain ⟨firstOwner, _, firstFresh⟩ :=
    commitment_facts_of_trace bounds trace first firstInput firstEvent candidate firstCall
  obtain ⟨secondOwner, _, secondFresh⟩ :=
    commitment_facts_of_trace bounds trace second secondInput secondEvent candidate secondCall
  have sameSender : first.sender = second.sender := firstOwner.symm.trans secondOwner
  rcases lt_trichotomy first.id.2 second.id.2 with lower | same | higher
  · exact absurd firstCall (secondFresh first ⟨firstInput, sameSender, lower⟩ firstEvent)
  · have nodup := (clean.1.2.2 second.sender) ▸ List.nodup_range
    have equal : first = second := List.inj_on_of_nodup_map nodup
      (List.mem_filter.mpr ⟨firstInput, by simpa using sameSender⟩)
      (List.mem_filter.mpr ⟨secondInput, by simp⟩) same
    subst equal
    rw [firstCall] at secondCall
    cases secondCall
    rfl
  · exact absurd secondCall
      (firstFresh second ⟨secondInput, sameSender.symm, higher⟩ secondEvent)

/-- **The field certified by an owned evidence request.** Along every history of
the one-packet game, a recalled transmission requesting owned evidence opens a
resolve event that is ready or completed, and the requested handle is accepted,
if at all, only at the binding field of that event. -/
theorem certificate_field {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    (sender : Player) (recalled : (application setup leaks).PlayerEntry)
    (member : recalled ∈ control.execution.recall sender)
    (submission : (application setup leaks).Submission)
    (sent : recalled.action.transmission = some submission)
    (fact : OpeningFact (graph setup)) (owned : submission.evidence = .owned fact) :
    ∃ event owner payload binding checks outputEq codeEq,
      nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq ∧
      (control.execution.application.config.cut.Ready event ∨
        event ∈ control.execution.application.config.cut.completed) ∧
      ∀ field, control.execution.application.accepted field = some fact.handle →
        field = binding.field := by
  let inputs := control.execution.network.inputs
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have clean := (bounds.onePacketMenu_countClean (runtime setup) leaks scheduler).history
    (initialLaw setup) horizon (fun state _ => (runtime setup).countClean_initial leaks state)
    trace
  have signed := signedCommitments_history (runtime setup) leaks (initialLaw setup)
    (serviceInitialLaw_initialized setup) horizon scheduler rawTrace
  obtain ⟨message, emitted, evidence, issued⟩ :=
    ownedRequestsEmitted_history bounds trace sender recalled member submission sent
  have carried := evidence fact owned
  have inputOf := output_mem_inputs_of_trace bounds trace
  have messageInput : message ∈ inputs :=
    inputOf sender message (List.mem_filterMap.mpr ⟨recalled, member, emitted⟩)
  have commitmentFacts := commitment_facts_of_trace bounds trace
  have commitmentUnique := commitment_unique_of_trace bounds trace
  have permitted : CountPermits inputs message :=
    (countPermits_eq_true_iff _ _).mp (clean.2 message messageInput)
  have correct := permitted.2.1
  have tokenValid := permitted.1
  unfold CountCallCorrect at correct
  cases call : message.payload.call with
  | malformed raw =>
      rw [call] at correct
      exact correct.elim
  | commitment named candidate =>
      rw [call] at correct
      rw [correct.2.1] at carried
      cases carried
  | opening event candidate raw =>
      rw [call] at correct
      obtain ⟨certified, resolveFacts⟩ := correct
      have factEq : fact = ⟨candidate, raw⟩ := by
        simpa only [certifiedOpening, call, carried, decide_eq_true_eq] using certified
      subst factEq
      cases view : nodeView (graph setup) event with
      | bind | sample =>
          rw [view] at resolveFacts
          exact resolveFacts.elim
      | resolve owner payload binding checks outputEq codeEq =>
          rw [view] at resolveFacts
          obtain ⟨_, _, signedBinding⟩ := resolveFacts
          refine ⟨event, owner, payload, binding, checks, outputEq, codeEq, view, ?_, ?_⟩
          · obtain ⟨tokenEvent, named, tokenEq⟩ :=
              (WitnessedPacket.tokenValid_iff _).mp tokenValid
            rw [call] at named
            cases named
            have predecessors := issued event tokenEq
            by_cases done : event ∈ control.execution.application.config.cut.completed
            · exact Or.inr done
            · exact Or.inl ⟨done, predecessors⟩
          · intro field accepted
            cases field with
            | inl input =>
                have initialSlot := signed.inputHandles input candidate accepted
                cases bindingField : binding.field with
                | inl bound =>
                    rw [bindingField] at signedBinding
                    change candidate = _ at signedBinding
                    rw [signedBinding] at initialSlot
                    cases initialSlot
                    rfl
                | inr bound =>
                    rw [bindingField] at signedBinding
                    obtain ⟨other, ⟨otherInput, _, _⟩, otherCall⟩ := signedBinding
                    obtain ⟨_, ⟨serial, prepared⟩, _⟩ :=
                      commitmentFacts other otherInput bound candidate otherCall
                    rw [prepared] at initialSlot
                    cases initialSlot
            | inr accepting =>
                obtain ⟨committed, output, committedCall⟩ :=
                  signed.acceptedSigned accepting candidate accepted
                have committedInput := inputOf _ committed output
                obtain ⟨_, ⟨serial, prepared⟩, _⟩ :=
                  commitmentFacts committed committedInput accepting candidate committedCall
                cases bindingField : binding.field with
                | inl bound =>
                    rw [bindingField] at signedBinding
                    change candidate = _ at signedBinding
                    rw [signedBinding] at prepared
                    cases prepared
                | inr bound =>
                    rw [bindingField] at signedBinding
                    obtain ⟨other, ⟨otherInput, _, _⟩, otherCall⟩ := signedBinding
                    rw [commitmentUnique committed committedInput other otherInput accepting bound
                      candidate committedCall otherCall]

end Vegas
