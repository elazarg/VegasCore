/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketRevealStep

/-! # The offered opening at a reveal is the canonical disclosure

Along every history of the default runtime, at a reveal of the player's turn,
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
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {horizon : Nat} {scheduler : (application setup leaks).Scheduler}

/-- **The transmitting disclosure.** Along every history of the default runtime,
at a reveal owned by the player, a transmitting canonical disclosure opens the
accepted handle of the revealed binding, owned by the player and openable to
the binding's stored value. -/
theorem disclosure_transmits_form {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (who : Player) (event : (graph setup).EventId)
    {payload : L.Ty} {binding : EventGraph.FieldRef (graph setup).layout (.binding who payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks}
    (node : nodeView (graph setup) event = .resolve who payload binding checks outputEq codeEq)
    (material : (application setup leaks).Submission)
    (sends : ((runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)).transmission =
        some material) :
    ∃ (handle : Handle (graph setup)) (value : L.Val payload),
      control.execution.application.accepted binding.field = some handle ∧ handle.1 = who ∧
      control.execution.application.candidates.lookup handle = .openable ⟨payload, value⟩ ∧
      reactiveResolutionPacket who event payload binding checks outputEq
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
        (control.execution.observe (application setup leaks) who).application =
          some (.opening event handle ⟨payload, value⟩) := by
  have facts := legalFacts setup leaks horizon scheduler control trace
  -- The canonical decision transmits exactly when the resolution packet exists.
  have packetSome : ∃ packet, reactiveResolutionPacket who event payload binding checks outputEq
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
      (control.execution.observe (application setup leaks) who).application = some packet := by
    cases sent : reactiveResolutionPacket who event payload binding checks outputEq
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
        (control.execution.observe (application setup leaks) who).application with
    | some packet => exact ⟨packet, rfl⟩
    | none =>
        exfalso
        unfold EventGraphRuntime.canonicalServiceDecision at sends
        simp only [EventGraphRuntime.canonicalReactiveDecision, node, sent, Option.map_none]
          at sends
        cases sends
  obtain ⟨packet, sent⟩ := packetSome
  have original := sent
  have discloses : (cast (congrArg EventGraph.EventField.Action outputEq)
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true) : Bool) = true := by
    simp
  unfold reactiveResolutionPacket at sent
  simp only [discloses, ↓reduceIte] at sent
  split at sent
  · rename_i value resolved
    split at sent
    · rename_i handle accepted
      split at sent
      · rename_i owned
        cases sent
        -- The stored binding is the resolved value's binding.
        have stored : binding.get? control.execution.application.config.store =
            some (.success value) := by
          have bound := resolved
          unfold EventGraph.EventCode.resolveOutput? at bound
          rw [← EventGraph.FieldRef.get?_playerStore binding who _ rfl]
          change (do
            let bound ← binding.get? ((graph setup).playerStore who
              control.execution.application.config.store)
            let accepted ← EventGraph.GuardCheck.allAccepted? checks
              ((graph setup).playerStore who control.execution.application.config.store)
              (if true then bound else .failure)
            pure (if accepted then (if true then bound else .failure) else .failure)) =
              some (.success value) at bound
          cases readBinding : binding.get? ((graph setup).playerStore who
              control.execution.application.config.store) with
          | none =>
              rw [readBinding] at bound
              cases bound
          | some result =>
              rw [readBinding] at bound
              simp only [Option.bind_eq_bind, Option.bind_some, ↓reduceIte] at bound
              cases acceptedCheck : EventGraph.GuardCheck.allAccepted? checks
                  ((graph setup).playerStore who control.execution.application.config.store)
                  result with
              | none =>
                  rw [acceptedCheck] at bound
                  cases bound
              | some isAccepted =>
                  rw [acceptedCheck] at bound
                  cases isAccepted
                  · simp at bound
                  · simpa using bound
        obtain ⟨provenance, acceptedProvenance, _, openable⟩ :=
          facts.binding.success_provenance binding value stored
        have same : provenance = handle := by
          have := acceptedProvenance.symm.trans accepted
          exact Option.some.inj this
        subst same
        exact ⟨provenance, value, acceptedProvenance, owned, openable, original⟩
      · cases sent
    · cases sent
  · cases sent
  · cases sent

/-- A resolved opening fact holds at the state: an owned fact opens the
player's own candidate, and a forwarded fact is sound evidence of the
network. -/
theorem resolved_fact_holds {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (who : Player) (request : EvidenceRequest (graph setup)) (fact : OpeningFact (graph setup))
    (resolved : request.resolve who
      (control.execution.observe (application setup leaks) who).application.candidates
      (ReactiveApplication.ResponseMenu.knownPackets (control.execution.recall who)
        (control.execution.observe (application setup leaks) who)) = some fact) :
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
          (control.execution.recall who)
          (control.execution.observe (application setup leaks) who) :=
        List.mem_of_find?_eq_some found
      have knownEq : ReactiveApplication.ResponseMenu.knownPackets (control.execution.recall who)
          (control.execution.observe (application setup leaks) who) =
          control.execution.network.known who :=
        ((application setup leaks).known_from_recall control.execution who facts.inputs).symm
      rw [knownEq, (application setup leaks).known_from_recall control.execution who
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
theorem disclosure_normal_form {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (who : Player) (event : (graph setup).EventId)
    {payload : L.Ty} {binding : EventGraph.FieldRef (graph setup).layout (.binding who payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks}
    (node : nodeView (graph setup) event = .resolve who payload binding checks outputEq codeEq)
    (material : (application setup leaks).Submission)
    (sends : ((runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)).transmission =
        some material) :
    ∃ (handle : Handle (graph setup)) (value : L.Val payload),
      control.execution.application.accepted binding.field = some handle ∧ handle.1 = who ∧
      control.execution.application.candidates.lookup handle = .openable ⟨payload, value⟩ ∧
      (runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
          (control.execution.observe (application setup leaks) who) event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true) =
        ⟨some ⟨⟨.opening event handle ⟨payload, value⟩, none⟩,
          EvidenceRequest.canonical (ReactiveApplication.ResponseMenu.knownPackets
            (control.execution.recall who)
            (control.execution.observe (application setup leaks) who))
            (some ⟨handle, ⟨payload, value⟩⟩)⟩⟩ := by
  classical
  obtain ⟨handle, value, accepted, owner, openable, packetEq⟩ :=
    disclosure_transmits_form trace who event node material sends
  refine ⟨handle, value, accepted, owner, openable, ?_⟩
  have verified : (control.execution.observe (application setup leaks) who).application.candidates
      handle.2 = .openable ⟨payload, value⟩ := by
    change control.execution.application.candidates.lookup (who, handle.2) = _
    rw [show (who, handle.2) = handle from Prod.ext owner.symm rfl]
    exact openable
  unfold EventGraphRuntime.canonicalServiceDecision
  simp only [EventGraphRuntime.canonicalReactiveDecision, node, packetEq, Option.map_some]
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
theorem onePacket_opening_eq_disclosure {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    {payload : L.Ty} {binding : EventGraph.FieldRef (graph setup).layout (.binding who payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks}
    (node : nodeView (graph setup) event = .resolve who payload binding checks outputEq codeEq)
    (disclosed : (application setup leaks).Submission)
    (sendsDisclosure : ((runtime setup).canonicalServiceDecision leaks who
      (control.execution.recall who) (control.execution.observe (application setup leaks) who)
      event (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)).transmission =
        some disclosed)
    (response : (application setup leaks).Action)
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who
      (control.execution.recall who) (control.execution.observe (application setup leaks) who))
    (material : (application setup leaks).Submission)
    (sends : response.transmission = some material)
    (named : material.call.packet.event? (graph setup) = some event) :
    response = (runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true) := by
  classical
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have facts := legalFacts setup leaks horizon scheduler control rawTrace
  have recalled := (runtime setup).countRecall_history leaks rawTrace
  have clean := (bounds.onePacketMenu_countClean (runtime setup) leaks scheduler).history
    (initialLaw setup) horizon (fun state _ => (runtime setup).countClean_initial leaks state) trace
  have signed := signedCommitments_history (runtime setup) leaks (initialLaw setup)
    (serviceInitialLaw_initialized setup) horizon scheduler rawTrace
  obtain ⟨handle, value, accepted, owner, openable, disclosureEq⟩ :=
    disclosure_normal_form rawTrace who event node disclosed sendsDisclosure
  rw [disclosureEq]
  obtain ⟨effective, permitted⟩ := (bounds.mem_onePacketActions (runtime setup) leaks who _ _
    response).mp member
  have normal := ((runtime setup).reactiveNormalization leaks).menu_normal
    (bounds.rawMenu (runtime setup) leaks) who _ _ response effective
  have verdict : CountPermits ((application setup leaks).outputs (control.execution.recall who))
      ((runtime setup).localEnvelope leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) material) := by
    rcases permitted with silent | ⟨other, otherSends, counted⟩
    · rw [sends] at silent
      cases silent
    · rw [sends] at otherSends
      cases Option.some.inj otherSends
      exact (countPermits_eq_true_iff _ _).mp counted
  have correct := verdict.2.1
  unfold CountCallCorrect at correct
  have callEq : ((runtime setup).localEnvelope leaks who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) material).payload.call =
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
        (control.execution.observe (application setup leaks) who).application.candidates)
      (ReactiveApplication.ResponseMenu.knownPackets (control.execution.recall who)
        (control.execution.observe (application setup leaks) who)) = some ⟨candidate, raw⟩ := by
    have evidence := congrArg WitnessedPacket.evidence envelopeEq
    have call := congrArg WitnessedPacket.call envelopeEq
    change material.call.packet = _ at call
    rw [packetIs] at call
    cases call
    exact evidence
  have afterEq : material.call.candidateAfter who
      (control.execution.observe (application setup leaks) who).application.candidates =
      (control.execution.observe (application setup leaks) who).application.candidates := by
    funext query
    unfold Submission.candidateAfter
    rw [packetIs]
  rw [afterEq] at resolvedEq
  have holds := resolved_fact_holds rawTrace who material.evidence _ resolvedEq
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
    (control.execution.observe (application setup leaks) who).application
    (ReactiveApplication.ResponseMenu.knownPackets (control.execution.recall who)
      (control.execution.observe (application setup leaks) who))) = some material
    at materialNormal
  rw [← Option.some.inj materialNormal]
  simp only [WitnessedSubmission.normalizeReactive, Submission.normalizeReactive, packetIs,
    openingEffective, EvidenceRequest.normalize, afterEq, resolvedEq, ↓reduceIte]

variable (setup leaks) in
/-- **The disclosure resolves.** At a pending reveal of a player, its canonical
disclosure transmits. -/
def DisclosureResolves (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) : Prop :=
  ∀ event, pendingEvent setup leaks who (some (past, view)) = some event →
    ∀ owner payload (binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload))
      checks outputEq codeEq,
      nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq →
      ((runtime setup).canonicalServiceDecision leaks who past view event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)).transmission ≠
        none

/-- **A resolving disclosure is canonical.** Along every history of the
one-packet game, when the player's canonical disclosure transmits at its
pending reveal, it is canonical. -/
theorem disclosureCanonical_of_resolves {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player)
    (resolves : DisclosureResolves setup leaks who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who)) :
    DisclosureCanonical setup leaks bounds who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) := by
  intro event pending owner payload binding checks outputEq codeEq node
  have transmits := resolves event pending owner payload binding checks outputEq codeEq node
  refine ⟨transmits, fun response member material sends named => ?_⟩
  obtain ⟨_, _, owned, _⟩ := pendingEvent_spec (setup := setup) pending
  have ownerEq : owner = who :=
    Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
  subst ownerEq
  obtain ⟨disclosed, sendsDisclosure⟩ := Option.ne_none_iff_exists'.mp transmits
  exact onePacket_opening_eq_disclosure trace owner event node disclosed sendsDisclosure response
    member material sends named

end Vegas
