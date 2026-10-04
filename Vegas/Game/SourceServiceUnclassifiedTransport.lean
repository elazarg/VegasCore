/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceResolutionComplement
import Vegas.Pending.ReactiveBindingGuardedStep
import Vegas.Pending.ReactiveBindingRiskRecall
import Vegas.Pending.ReactiveMissingBindingTransport

/-! # Actual uncharged certificate transport through typed binding repair

An unclassified effective response at a clear original input requests only a
certificate justified by an actual successful typed binding, or no certificate.
The successful-binding frame preserves that certificate without preserving every
private raw capability. Charged and recorded responses remain separate.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Actual legal paired traces determine the original clear flag. Outside the
charged public-packet and recalled-response classes, typed success provenance
then gives the same certificate and full effective response after repair. No
original risk-menu trace or preservation of all raw capabilities is required. -/
theorem sourceServiceUnclassified_response_transport
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (original repaired : (application setup leaks).Execution) (who : Player)
    (memory : BindingMemory (runtime setup) leaks)
    (frame : memory.Frame (runtime setup) leaks who original repaired)
    (leftTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨leftRemaining, some who, original⟩))
    (rightTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨rightRemaining, some who, repaired⟩))
    (clear : (runtime setup).serviceRisk leaks bound who (repaired.recall who)
      (repaired.observe (application setup leaks) who) = false)
    (response : (application setup leaks).Action)
    (effective : response ∈ (bounds.menu (runtime setup) leaks).actions who
      (original.recall who) (original.observe (application setup leaks) who))
    (notPacket : ¬ auditableServiceResponse setup leaks who (original.recall who)
      (original.observe (application setup leaks) who) response)
    (notRecorded : ¬ recordedServiceResponse setup leaks (original.recall who) response) :
    let app := application setup leaks
    response ∈ (bounds.menu (runtime setup) leaks).actions who (repaired.recall who)
        (repaired.observe app who) ∧
      (original.respond app who response).network = (repaired.respond app who response).network ∧
      ∀ material, response.transmission = some material →
        app.packet (app.submit original.application who material) who
          (original.network.known who) material =
        app.packet (app.submit repaired.application who material) who
          (repaired.network.known who) material := by
  classical
  let app := application setup leaks
  have rawRight := rightTrace
  have leftFacts := legalFacts setup leaks horizon scheduler _ leftTrace
  have rightFacts := legalFacts setup leaks horizon scheduler _ rawRight
  have records := frame.submissionRiskRecords (runtime setup) leaks leftTrace rawRight
  have leftClear : (runtime setup).serviceRisk leaks bound who (original.recall who)
      (original.observe app who) = false :=
    ((runtime setup).serviceRisk_congr leaks bound who (original.recall who) (repaired.recall who)
      (original.observe app who) (repaired.observe app who) rfl frame.publicView records).trans
        clear
  have leftKnown : ReactiveApplication.ResponseMenu.knownPackets (original.recall who)
      (original.observe app who) = original.network.known who :=
    (app.known_from_recall original who leftFacts.inputs).symm
  have resolved (material : app.Submission) (transmission : response.transmission = some material) :
      material.evidence.resolve who
        (material.call.candidateAfter who (fun slot =>
          original.application.candidates.lookup (who, slot))) (original.network.known who) =
      material.evidence.resolve who
        (material.call.candidateAfter who (fun slot =>
          repaired.application.candidates.lookup (who, slot))) (repaired.network.known who) := by
    have responseEq : response = ⟨some material⟩ := by
      cases response with
      | mk transmitted => cases transmission; rfl
    rw [responseEq] at effective notPacket notRecorded
    obtain ⟨event, named, owned, ready, turn, _, fits⟩ := unclassifiedSubmission_opportunity
      bound original who leftTrace leftClear material notPacket notRecorded
    let message : Message Player (WitnessedPacket (graph setup)) :=
      ⟨(who, original.network.nextSerial who), app.packet
        (app.submit original.application who material) who (original.network.known who) material⟩
    have notAuditable : ¬ AuditableServicePacket setup original.application.publicView who
        message := by
      intro classified
      apply notPacket
      refine ⟨material, rfl, ?_⟩
      rw [localServiceEnvelope_actual setup leaks leftTrace who material]
      exact classified
    have content : ¬ SignedContentBreach message := fun bad => notAuditable (Or.inl bad)
    have compatible : message.payload.call.MatchesNode := by
      by_contra incompatible
      exact notAuditable (Or.inr (Or.inr (Or.inl incompatible)))
    have normal : material.normalizeReactive who (app.observePlayer original.application who)
        (original.network.known who) = material := by
      have fixed := ((bounds.menu_mem (runtime setup) leaks who _ _ _).mp effective).2
      have same := Option.some.inj (congrArg ReactiveApplication.Action.transmission fixed)
      change material.normalizeReactive who (app.observePlayer original.application who)
        (ReactiveApplication.ResponseMenu.knownPackets (original.recall who)
          (original.observe app who)) = material at same
      rw [leftKnown] at same
      exact same
    have noEvidence (empty : message.payload.evidence = none) :
        material.evidence = .none := by
      have evidenceNormal := congrArg WitnessedSubmission.evidence normal
      change material.evidence.normalize who
        (material.call.candidateAfter who (app.observePlayer original.application who).candidates)
        (original.network.known who) = material.evidence at evidenceNormal
      have actual : material.evidence.resolve who
          (material.call.candidateAfter who (app.observePlayer original.application who).candidates)
          (original.network.known who) = none := by
        change (material.emit (app.submit original.application who material) who
          (original.network.known who)).evidence = none at empty
        rw [WitnessedSubmission.emit_eq_resolve] at empty
        change material.evidence.resolve who
          (fun slot => (app.submit original.application who material).candidates.lookup
            (who, slot)) (original.network.known who) = none at empty
        have candidates : (fun slot =>
            (app.submit original.application who material).candidates.lookup (who, slot)) =
            material.call.candidateAfter who
              (app.observePlayer original.application who).candidates :=
          funext (material.call.candidateAfter_eq who original.application)
        rwa [candidates] at empty
      simpa only [EvidenceRequest.normalize, actual, EvidenceRequest.canonical] using
        evidenceNormal.symm
    cases called : message.payload.call with
    | malformed raw =>
        change message.payload.call.event? (graph setup) = some event at named
        rw [called] at named
        cases named
    | commitment addressed candidate =>
        have empty : message.payload.evidence = none := by
          by_contra present
          exact content (Or.inr (Or.inr (Or.inl ⟨addressed, candidate, called, present⟩)))
        rw [noEvidence empty]
        rfl
    | withhold addressed =>
        have empty : message.payload.evidence = none := by
          by_contra present
          exact content (Or.inr (Or.inl ⟨addressed, called, present⟩))
        rw [noEvidence empty]
        rfl
    | opening addressed candidate raw =>
        have sameEvent : addressed = event := by
          have actualNamed := named
          change message.payload.call.event? (graph setup) = some event at actualNamed
          rw [called] at actualNamed
          exact Option.some.inj actualNamed
        subst addressed
        cases node : nodeView (graph setup) event with
        | sample payload law outputEq codeEq =>
            simp only [Payload.MatchesNode, called, node] at compatible
        | bind actor payload outputEq codeEq =>
            simp only [Payload.MatchesNode, called, node] at compatible
        | resolve actor payload binding checks outputEq codeEq =>
            have actorEq := nodeView_resolve_actor outputEq codeEq
            rw [owned] at actorEq
            cases Option.some.inj actorEq
            have permitted := unclassifiedResolutionSubmission_conforms original who leftTrace
              event payload binding checks outputEq codeEq node turn ready fits.withinDeadline
                material named notPacket
            have casesResolution := (runtime setup).service_resolution_response leaks bounds
              original who leftFacts.evidence leftFacts.binding leftFacts.inputs event payload
                binding checks outputEq codeEq node material named effective permitted
            rcases casesResolution with withheld | ⟨value, stored, resolvedOutput, decided⟩
            · rw [(runtime setup).serviceDecision_resolution_false leaks who (original.recall who)
                (original.observe app who) event who payload binding checks outputEq codeEq node]
                at withheld
              have callEq := congrArg (fun action : app.Action =>
                action.transmission.map (fun submission => submission.call.packet)) withheld
              change some material.call.packet = some (.withhold event) at callEq
              have actualCall : material.call.packet = .opening event candidate raw := called
              rw [actualCall] at callEq
              cases Option.some.inj callEq
            · obtain ⟨_, selected, associated, _, selectedOwner, leftFixed, rightFixed⟩ :=
                frame.successful_opening leftFacts.binding rightFacts.binding binding value stored
              have physical := (runtime setup).serviceDecision_successful_opening leaks original
                leftFacts.inputs who event payload binding checks outputEq codeEq node selected
                  value associated selectedOwner leftFixed resolvedOutput
              have materialEq := Option.some.inj
                (congrArg ReactiveApplication.Action.transmission (decided.trans physical))
              have rightMaterial := materialEq.trans
                (frame.normalized_opening_eq event selected ⟨payload, value⟩ selectedOwner leftFixed
                  rightFixed)
              have leftLocal : original.application.candidates.lookup (who, selected.2) =
                  .openable ⟨payload, value⟩ := by
                simpa only [← selectedOwner, Prod.mk.eta] using leftFixed
              have rightLocal : repaired.application.candidates.lookup (who, selected.2) =
                  .openable ⟨payload, value⟩ := by
                simpa only [← selectedOwner, Prod.mk.eta] using rightFixed
              have originalResolved : material.evidence.resolve who
                  (material.call.candidateAfter who (fun slot =>
                    original.application.candidates.lookup (who, slot)))
                  (original.network.known who) = some ⟨selected, ⟨payload, value⟩⟩ := by
                rw [materialEq]
                simp only [disclosureSubmission, WitnessedSubmission.normalizeReactive,
                  Submission.normalizeReactive_none, Submission.candidateAfter_opening]
                change ((EvidenceRequest.owned ⟨selected, ⟨payload, value⟩⟩).normalize who
                  (fun slot => original.application.candidates.lookup (who, slot))
                  (original.network.known who)).resolve who
                    (fun slot => original.application.candidates.lookup (who, slot))
                    (original.network.known who) = _
                rw [EvidenceRequest.resolve_normalize]
                simp only [EvidenceRequest.resolve, selectedOwner, leftLocal, and_self, ↓reduceIte]
              have repairedResolved : material.evidence.resolve who
                  (material.call.candidateAfter who (fun slot =>
                    repaired.application.candidates.lookup (who, slot)))
                  (repaired.network.known who) = some ⟨selected, ⟨payload, value⟩⟩ := by
                rw [rightMaterial]
                simp only [disclosureSubmission, WitnessedSubmission.normalizeReactive,
                  Submission.normalizeReactive_none, Submission.candidateAfter_opening]
                change ((EvidenceRequest.owned ⟨selected, ⟨payload, value⟩⟩).normalize who
                  (fun slot => repaired.application.candidates.lookup (who, slot))
                  (repaired.network.known who)).resolve who
                    (fun slot => repaired.application.candidates.lookup (who, slot))
                    (repaired.network.known who) = _
                rw [EvidenceRequest.resolve_normalize]
                simp only [EvidenceRequest.resolve, selectedOwner, rightLocal, and_self, ↓reduceIte]
              exact originalResolved.trans repairedResolved.symm
  exact (runtime setup).effectiveResponse_resolved_transport leaks bounds who original repaired
    leftFacts.inputs rightFacts.inputs frame.network frame.publicView frame.slots response resolved
      effective

end Vegas
