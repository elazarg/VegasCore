module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketRevealStep
public import Vegas.Pending.ReactivePolicyFacts

@[expose] public section

/-! # The offered opening at a reveal is the canonical disclosure

Along every history of the supplied runtime, at a reveal of the player's turn,
when the canonical disclosure transmits, it opens the accepted handle of the
revealed binding at the binding's stored value, a handle the player owns and
whose candidate opens to that value (`Vegas.disclosure_transmits_form`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {horizon : Nat} {scheduler : (application setup timeouts leaks).Scheduler}

/-- **The transmitting disclosure.** Along every history of the supplied runtime,
at a reveal owned by the player, a transmitting canonical disclosure opens the
accepted handle of the revealed binding, owned by the player and openable to
the binding's stored value. -/
theorem disclosure_transmits_form {control : (application setup timeouts leaks).Control}
    (trace : ((application setup timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace
      (some control))
    (who : Player) (event : (graph setup).EventId)
    {payload : L.Ty} {binding : EventGraph.FieldRef (graph setup).layout (.binding who payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks}
    (node : nodeView (graph setup) event = .resolve who payload binding checks outputEq codeEq)
    (material : (application setup timeouts leaks).Submission)
    (sends : ((canonicalServiceDecision timeouts) leaks who (control.execution.logs who)
      (control.execution.observe (application setup timeouts leaks) who) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)).transmission =
        some material) :
    ∃ (handle : Handle (graph setup)) (value : L.Val payload),
      control.execution.application.accepted binding.field = some handle ∧ handle.1 = who ∧
      control.execution.application.candidates.lookup handle = .openable ⟨payload, value⟩ ∧
      reactiveResolutionPacket who event payload binding checks outputEq
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
        (control.execution.observe (application setup timeouts leaks) who).application =
          some (.opening event handle ⟨payload, value⟩) := by
  have facts := legalFacts setup leaks horizon scheduler control trace
  have active := (canonicalServiceDecision_active timeouts) leaks who
    (control.execution.logs who) (control.execution.observe (application setup timeouts leaks) who)
    event _ material sends
  rcases reactiveResolutionPacket_shape who event payload binding checks outputEq
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
      (control.execution.observe (application setup timeouts leaks) who).application with
    ⟨handle, raw, packet⟩ | silent
  · obtain ⟨_, _, _, value, stored, accepted, owned, rawEq⟩ :=
      reactiveResolutionPacket_opening_spec who event payload binding checks outputEq _
        (control.execution.observe (application setup timeouts leaks) who).application
        event handle raw packet
    subst rawEq
    change binding.get? ((graph setup).playerStore who
      control.execution.application.config.store) = some (.success value) at stored
    rw [EventGraph.FieldRef.get?_playerStore binding who _ rfl] at stored
    obtain ⟨provenance, acceptedProvenance, _, openable⟩ :=
      facts.binding.success_provenance binding value stored
    have same : provenance = handle := Option.some.inj (acceptedProvenance.symm.trans accepted)
    subst same
    exact ⟨provenance, value, acceptedProvenance, owned, openable, packet⟩
  · exfalso
    simp only [EventGraphRuntime.canonicalServiceDecision,
      EventGraphRuntime.canonicalReactiveDecision, ite_eq_right active, node, silent,
      Option.map_none, ReactiveApplication.SubmissionNormalization.action] at sends
    cases sends

/-- A resolved opening fact holds at the state: an owned fact opens the
player's own candidate, and a forwarded fact is sound evidence of the
network. -/
theorem resolved_fact_holds {control : (application setup timeouts leaks).Control}
    (trace : ((application setup timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace
      (some control))
    (who : Player) (request : EvidenceRequest (graph setup)) (fact : OpeningFact (graph setup))
    (resolved : request.resolve who
      (control.execution.observe (application setup timeouts leaks) who).application.candidates
      (ReactiveApplication.ResponseMenu.knownPackets (control.execution.logs who)
        (control.execution.observe (application setup timeouts leaks) who)) = some fact) :
    control.execution.application.candidates.lookup fact.handle = .openable fact.raw := by
  classical
  have facts := legalFacts setup leaks horizon scheduler control trace
  cases request with
  | none => cases resolved
  | owned owned =>
      simp only [EvidenceRequest.resolve] at resolved
      split_ifs at resolved with available
      obtain rfl := Option.some.inj resolved
      obtain ⟨owner, openable⟩ := available
      have handleEq : owned.handle = (who, owned.handle.2) := Prod.ext owner rfl
      rw [handleEq]
      exact openable
  | forward id =>
      simp only [EvidenceRequest.resolve, EvidenceRequest.forwardedEvidence] at resolved
      obtain ⟨message, found, carried⟩ := Option.bind_eq_some_iff.mp resolved
      have member : message ∈ ReactiveApplication.ResponseMenu.knownPackets
          (control.execution.logs who)
          (control.execution.observe (application setup timeouts leaks) who) :=
        List.mem_of_find?_eq_some found
      have knownEq : ReactiveApplication.ResponseMenu.knownPackets (control.execution.logs who)
          (control.execution.observe (application setup timeouts leaks) who) =
          control.execution.network.known who :=
        ((application setup timeouts leaks).known_from_recall control.execution who
          facts.inputs).symm
      rw [knownEq, (application setup timeouts leaks).known_from_recall control.execution who
        facts.inputs] at member
      have sound : ∀ held ∈ message.payload.evidence.toList,
          held.Holds control.execution.application := by
        rcases List.mem_append.mp member with front | ledger
        · rcases List.mem_append.mp front with output | leaked
          · rw [← facts.inputs who] at output
            exact facts.evidence.inputs message (List.mem_filter.mp output).1
          · exact facts.evidence.leaked who message leaked
        · exact facts.evidence.ledger message ledger
      exact sound fact (by rw [carried]; simp)

/-- **The normal form of the disclosure.** A transmitting canonical disclosure
is the opening of its handle at its value, with the canonical certificate of
that opening. -/
theorem disclosure_normal_form {control : (application setup timeouts leaks).Control}
    (trace : ((application setup timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace
      (some control))
    (who : Player) (event : (graph setup).EventId)
    {payload : L.Ty} {binding : EventGraph.FieldRef (graph setup).layout (.binding who payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks}
    (node : nodeView (graph setup) event = .resolve who payload binding checks outputEq codeEq)
    (material : (application setup timeouts leaks).Submission)
    (sends : ((canonicalServiceDecision timeouts) leaks who (control.execution.logs who)
      (control.execution.observe (application setup timeouts leaks) who) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)).transmission =
        some material) :
    ∃ (handle : Handle (graph setup)) (value : L.Val payload),
      control.execution.application.accepted binding.field = some handle ∧ handle.1 = who ∧
      control.execution.application.candidates.lookup handle = .openable ⟨payload, value⟩ ∧
      (canonicalServiceDecision timeouts) leaks who (control.execution.logs who)
          (control.execution.observe (application setup timeouts leaks) who) event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true) =
        ⟨some ⟨⟨.opening event handle ⟨payload, value⟩, none⟩,
          EvidenceRequest.canonical (ReactiveApplication.ResponseMenu.knownPackets
            (control.execution.logs who)
            (control.execution.observe (application setup timeouts leaks) who))
            (some ⟨handle, ⟨payload, value⟩⟩)⟩⟩ := by
  classical
  have active := (canonicalServiceDecision_active timeouts) leaks who
    (control.execution.logs who) (control.execution.observe (application setup timeouts leaks) who)
    event _ material sends
  obtain ⟨handle, value, accepted, owner, openable, packetEq⟩ :=
    disclosure_transmits_form (timeouts := timeouts) trace who event node material sends
  refine ⟨handle, value, accepted, owner, openable, ?_⟩
  have verified : (control.execution.observe (application setup timeouts leaks)
    who).application.candidates
      handle.2 = .openable ⟨payload, value⟩ := by
    change control.execution.application.candidates.lookup (who, handle.2) = _
    rw [show (who, handle.2) = handle from Prod.ext owner.symm rfl]
    exact openable
  unfold EventGraphRuntime.canonicalServiceDecision
  simp only [EventGraphRuntime.canonicalReactiveDecision, ite_eq_right active, node, packetEq,
    Option.map_some]
  rw [disclosureSubmission_normalize_opening who _ event handle _ owner verified]
  simp only [ReactiveApplication.SubmissionNormalization.action,
    EventGraphRuntime.reactiveNormalization, WitnessedSubmission.normalizeReactive,
    disclosureSubmission, Submission.normalizeReactive_none, EvidenceRequest.normalize,
    EvidenceRequest.resolve, Submission.candidateAfter, owner, verified, and_self,
    ↓reduceIte]

variable [Fintype Player] {bounds : MessageBounds (graph setup)}

/-- **The offered opening is the disclosure.** Along every history of the
one-packet game, at a reveal of the player's turn, when its canonical
disclosure transmits, every transmission naming the reveal that the one-packet
menu offers is that disclosure: the count verdict certifies its opening and
signs its handle by the player's single commitment for the binding, which is
the accepted handle, and the certificate opens that handle to its stored
value. -/
theorem onePacket_opening_eq_disclosure {control : (application setup timeouts leaks).Control}
    (trace : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    {payload : L.Ty} {binding : EventGraph.FieldRef (graph setup).layout (.binding who payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks}
    (node : nodeView (graph setup) event = .resolve who payload binding checks outputEq codeEq)
    (disclosed : (application setup timeouts leaks).Submission)
    (sendsDisclosure : ((canonicalServiceDecision timeouts) leaks who
      (control.execution.logs who) (control.execution.observe (application setup timeouts leaks)
        who)
      event (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)).transmission =
        some disclosed)
    (response : (application setup timeouts leaks).Action)
    (member : response ∈ bounds.onePacketActions timeouts leaks who
      (control.execution.logs who) (control.execution.observe (application setup timeouts leaks)
        who))
    (material : (application setup timeouts leaks).Submission)
    (sends : response.transmission = some material)
    (named : material.call.packet.event? (graph setup) = some event) :
    response = (canonicalServiceDecision timeouts) leaks who (control.execution.logs who)
      (control.execution.observe (application setup timeouts leaks) who) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true) := by
  classical
  have rawTrace : ((application setup timeouts leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have facts := legalFacts setup leaks horizon scheduler control rawTrace
  have recalled := (countRecall_history timeouts) leaks rawTrace
  have clean := (bounds.onePacketMenu_countClean timeouts leaks scheduler).history
    (initialLaw setup) horizon (fun state _ => (countClean_initial timeouts) leaks state) trace
  have signed := signedCommitments_history timeouts leaks (initialLaw setup)
    (serviceInitialLaw_initialized setup) horizon scheduler rawTrace
  obtain ⟨handle, value, accepted, owner, openable, disclosureEq⟩ :=
    disclosure_normal_form (timeouts := timeouts) rawTrace who event node disclosed sendsDisclosure
  rw [disclosureEq]
  obtain ⟨effective, permitted⟩ := (bounds.mem_onePacketActions timeouts leaks who _ _
    response).mp member
  have normal := ((reactiveNormalization timeouts) leaks).menu_normal
    (bounds.rawMenu timeouts leaks) who _ _ response effective
  have verdict : CountPermits ((application setup timeouts leaks).outputs (control.execution.logs
    who))
      ((localEnvelope timeouts) leaks who (control.execution.logs who)
        (control.execution.observe (application setup timeouts leaks) who) material) := by
    rcases permitted with silent | ⟨other, otherSends, counted⟩
    · rw [sends] at silent
      cases silent
    · rw [sends] at otherSends
      cases Option.some.inj otherSends
      exact (countPermits_eq_true_iff _ _).mp counted
  have correct := verdict.2.1
  unfold CountCallCorrect at correct
  have callEq : ((localEnvelope timeouts) leaks who (control.execution.logs who)
      (control.execution.observe (application setup timeouts leaks) who) material).payload.call =
      material.call.packet := rfl
  rw [callEq] at correct
  -- The packet opens a candidate at the reveal.
  obtain ⟨candidate, raw, packetIs⟩ : ∃ candidate raw,
      material.call.packet = .opening event candidate raw := by
    revert correct named
    cases material.call.packet with
    | malformed => intro _ correct; exact correct.elim
    | commitment other selected =>
        intro named correct
        obtain rfl := Option.some.inj named
        have owned := correct.1
        unfold bindingOwnedBy at owned
        rw [outputEq] at owned
        cases owned
    | opening other selected raw =>
        intro named _
        obtain rfl := Option.some.inj named
        exact ⟨selected, raw, rfl⟩
  rw [packetIs] at correct
  obtain ⟨certified, resolves⟩ := correct
  rw [node] at resolves
  obtain ⟨_, _, signedBinding⟩ := resolves
  -- The certificate resolves to the opened fact.
  obtain ⟨_, _, _, token, envelopeEq⟩ := (certifiedOpening_iff _).mp certified
  have resolvedEq : material.evidence.resolve who
      (material.call.candidateAfter who
        (control.execution.observe (application setup timeouts leaks) who).application.candidates)
      (ReactiveApplication.ResponseMenu.knownPackets (control.execution.logs who)
        (control.execution.observe (application setup timeouts leaks) who)) = some ⟨candidate, raw⟩
          := by
    have evidence := congrArg WitnessedPacket.evidence envelopeEq
    have call := congrArg WitnessedPacket.call envelopeEq
    change material.call.packet = _ at call
    rw [packetIs] at call
    cases call
    exact evidence
  have afterEq : material.call.candidateAfter who
      (control.execution.observe (application setup timeouts leaks) who).application.candidates =
      (control.execution.observe (application setup timeouts leaks) who).application.candidates
        := by
    funext query
    unfold Submission.candidateAfter
    rw [packetIs]
  rw [afterEq] at resolvedEq
  have holds := resolved_fact_holds (timeouts := timeouts) rawTrace who material.evidence _
    resolvedEq
  -- The signed candidate is the accepted handle.
  have candidateEq : candidate = handle := by
    unfold SignedBinding at signedBinding
    cases fieldEq : binding.field with
    | inl input =>
        rw [fieldEq] at signedBinding accepted
        have initialHandle := signed.inputHandles input handle accepted
        rw [signedBinding]
        exact Prod.ext owner.symm initialHandle.symm
    | inr bindingEvent =>
        rw [fieldEq] at signedBinding accepted
        obtain ⟨other, ⟨otherOutput, otherSender, _⟩, otherCall⟩ := signedBinding
        obtain ⟨message, messageOutput, messageCall⟩ :=
          signed.acceptedSigned bindingEvent handle accepted
        rw [owner] at messageOutput
        by_cases same : other = message
        · subst same
          rw [otherCall] at messageCall
          exact (Payload.commitment.inj messageCall).2
        · exfalso
          have otherInput : other ∈ control.execution.network.inputs := by
            rw [← recalled.1 who] at otherOutput
            exact (List.mem_filter.mp otherOutput).1
          have messageInput : message ∈ control.execution.network.inputs := by
            rw [← recalled.1 who] at messageOutput
            exact (List.mem_filter.mp messageOutput).1
          have messageSender : message.sender = who := by
            rw [← recalled.1 who] at messageOutput
            simpa using (List.mem_filter.mp messageOutput).2
          have otherSenderWho : other.sender = who := otherSender
          have idNe : other.id ≠ message.id := fun idEq =>
            same ((facts.unique.inputs message messageInput).inputs other otherInput idEq)
          have serialNe : other.id.2 ≠ message.id.2 := fun serialEq =>
            idNe (Prod.ext (otherSenderWho.trans messageSender.symm) serialEq)
          rcases Nat.lt_or_gt_of_ne serialNe with earlier | later
          · have fresh := ((countPermits_eq_true_iff _ _).mp
              (clean.2 message messageInput)).2.2
            apply fresh other ⟨otherInput, otherSenderWho.trans messageSender.symm, earlier⟩
            rw [otherCall, messageCall]
            rfl
          · have fresh := ((countPermits_eq_true_iff _ _).mp (clean.2 other otherInput)).2.2
            apply fresh message ⟨messageInput, messageSender.trans otherSenderWho.symm, later⟩
            rw [otherCall, messageCall]
            rfl
  subst candidateEq
  have rawEq : raw = ⟨payload, value⟩ := by
    have both := holds.symm.trans openable
    cases both
    rfl
  subst rawEq
  -- The offered response is its own normal form.
  rcases response with ⟨transmission⟩
  change transmission = some material at sends
  subst sends
  have materialNormal := congrArg ReactiveApplication.Action.transmission normal
  change some (material.normalizeReactive who
    (control.execution.observe (application setup timeouts leaks) who).application
    (ReactiveApplication.ResponseMenu.knownPackets (control.execution.logs who)
      (control.execution.observe (application setup timeouts leaks) who))) = some material
    at materialNormal
  rw [← Option.some.inj materialNormal]
  simp only [WitnessedSubmission.normalizeReactive, Submission.normalizeReactive, packetIs,
    openingEffective, EvidenceRequest.normalize, afterEq, resolvedEq, ↓reduceIte]

/-- **A resolving disclosure is canonical.** Along every history of the
one-packet game, when the player's canonical disclosure transmits at its
pending reveal, it is canonical. -/
theorem disclosureCanonical_of_resolves {control : (application setup timeouts leaks).Control}
    (trace : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player)
    (resolves : DisclosureResolves setup timeouts leaks who (control.execution.logs who)
      (control.execution.observe (application setup timeouts leaks) who)) :
    DisclosureCanonical setup timeouts leaks bounds who (control.execution.logs who)
      (control.execution.observe (application setup timeouts leaks) who) := by
  intro event pending owner payload binding checks outputEq codeEq node
  have transmits := resolves event pending owner payload binding checks outputEq codeEq node
  refine ⟨transmits, fun response member material sends named => ?_⟩
  obtain ⟨_, _, owned, _⟩ := pendingEvent_spec (timeouts := timeouts) (setup := setup) pending
  have ownerEq : owner = who :=
    Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
  subst ownerEq
  obtain ⟨disclosed, sendsDisclosure⟩ := Option.ne_none_iff_exists'.mp transmits
  exact onePacket_opening_eq_disclosure (timeouts := timeouts) trace owner event node disclosed
    sendsDisclosure response
    member material sends named

end Vegas
