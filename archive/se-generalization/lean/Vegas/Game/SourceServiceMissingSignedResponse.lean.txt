/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceSignedExclusion
import Vegas.Game.SourceServiceAuditableCollection
import Vegas.Game.SourceServiceRiskPrefix
import Vegas.Pending.ReactiveBindingContinuation
import Vegas.Pending.ReactiveBindingFrame
import Vegas.Pending.ReactiveMissingBindingTransport

/-! # A signed response at a clear repaired input

A private binding implementation reconstructs the original input from its
actual recall and shadow. An effective original response has the same literal
envelope at the repaired input, because normalization cannot manufacture a
certificate from an added capability. If that envelope is a signed breach and
the repaired history is still clear and legal, the response is excluded there.

For an opening or a commitment that actually discloses evidence, the clear
retained input consequently selects its legal fallback before emission and
leaves the shadow unchanged. Expanded inputs copy effective commitments and
their actual signed breach. One shared draw gives the original full effective
invocation and the actual retained implementation law. This does not establish
a whole-policy splice, future zero collection or a utility comparison.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A clear legal repaired prefix has not copied an earlier owner signed
breach. The actual common network transfers this fact to the original RAW
prefix, even though its private unusable binding was excluded by the risk menu.
An unfinished current record is allowed. -/
theorem sourceServiceMissing_clear_no_prior_signed
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (original : (application setup leaks).Execution)
    (repaired : (application setup leaks).Control) (who : Player)
    (memory : BindingMemory (runtime setup) leaks)
    (frame : memory.Frame (runtime setup) leaks who original repaired.execution)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some repaired))
    (clear : (runtime setup).persistentServiceRisk leaks bound who
      (repaired.execution.recall who)
      (repaired.execution.observe (application setup leaks) who) = false) :
    ∀ message ∈ original.network.inputs, message.sender = who → ¬ SignedContentBreach message := by
  let app := application setup leaks
  obtain ⟨_, conform, _, _⟩ := riskPacketFacts_history bounds bound contract repaired trace who
    clear
  have rawTrace := (bounds.riskMenu (runtime setup) leaks bound).toRawTrace (initialLaw setup)
    horizon scheduler trace
  have facts := legalFacts setup leaks horizon scheduler repaired rawTrace
  intro message member authored breach
  rw [frame.network] at member
  obtain ⟨entry, entryMember, material, transmission, emitted, _, _, _⟩ :=
    facts.provenance.inputs message member
  change entry ∈ repaired.execution.recall message.id.1 at entryMember
  change message.id.1 = who at authored
  rw [authored] at entryMember
  exact breach.not_freshServiceEnvelope (runtime setup) entry.beforeView.application.publicView
    (conform entry entryMember material message transmission emitted)

/-- The original signed envelope is reconstructed by the private implementation,
and its actual clear repaired risk input excludes the proposed response. The
original history is RAW; it need not be a legal risk-menu history. -/
theorem sourceServiceMissing_signedResponse_unavailable
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (original repaired : (application setup leaks).Execution) (who : Player)
    (memory : BindingMemory (runtime setup) leaks)
    (frame : memory.Frame (runtime setup) leaks who original repaired)
    (leftTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨leftRemaining, some who, original⟩))
    (rightTrace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup)
      horizon scheduler).Trace (some ⟨rightRemaining, some who, repaired⟩))
    (clear : (runtime setup).serviceRisk leaks bound who (repaired.recall who)
      (repaired.observe (application setup leaks) who) = false)
    (preserved : ∀ slot raw, original.application.candidates.lookup (who, slot) = .openable raw →
      repaired.application.candidates.lookup (who, slot) = .openable raw)
    (response : (application setup leaks).Action)
    (effective : response ∈ (bounds.menu (runtime setup) leaks).actions who
      (original.recall who) (original.observe (application setup leaks) who))
    (material : (application setup leaks).Submission)
    (transmission : response.transmission = some material)
    (breach : SignedContentBreach
      ⟨(who, original.network.nextSerial who), (application setup leaks).packet
        ((application setup leaks).submit original.application who material) who
          (original.network.known who) material⟩) :
    SignedContentBreach (localServiceEnvelope setup leaks who
      (memory.restoreRecall (runtime setup) leaks (repaired.recall who))
      (memory.shadow.inputView (runtime setup) leaks
        (repaired.observe (application setup leaks) who)) material) ∧
      response ∉ bounds.riskActions (runtime setup) leaks bound who (repaired.recall who)
        (repaired.observe (application setup leaks) who) := by
  let app := application setup leaks
  have rawRight := (bounds.riskMenu (runtime setup) leaks bound).toRawTrace
    (initialLaw setup) horizon scheduler rightTrace
  have leftRecall := app.history_inputRecall (initialLaw setup) horizon scheduler leftTrace
  have rightRecall := app.history_inputRecall (initialLaw setup) horizon scheduler rawRight
  have transported := (runtime setup).effectiveResponse_openable_transport leaks bounds who
    original repaired leftRecall rightRecall frame.network frame.publicView frame.slots preserved
      response effective
  have packetEq := transported.2.2 material transmission
  have serialEq : original.network.nextSerial who = repaired.network.nextSerial who :=
    congrArg (fun network : MessageNetwork Player (WitnessedPacket (graph setup)) =>
      network.nextSerial who) frame.network
  have rightBreach : SignedContentBreach
      ⟨(who, repaired.network.nextSerial who), app.packet
        (app.submit repaired.application who material) who (repaired.network.known who)
          material⟩ := by
    rw [serialEq, packetEq] at breach
    exact breach
  refine ⟨?_, signedContentBreach_risk_excluded bounds bound repaired who rightTrace clear
    response material transmission rightBreach⟩
  rw [frame.past, frame.observed, localServiceEnvelope_actual setup leaks leftTrace who material]
  exact breach

/-- An excluded signed opening takes the existing legal fallback before the
repaired implementation emits it. No candidate or completion shadow changes.
The fallback itself cannot emit a signed breach at this clear legal input. -/
theorem sourceServiceMissing_signedOpening_fallback
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (original repaired : (application setup leaks).Execution) (who : Player)
    (memory : BindingMemory (runtime setup) leaks)
    (frame : memory.Frame (runtime setup) leaks who original repaired)
    (leftTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨leftRemaining, some who, original⟩))
    (rightTrace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup)
      horizon scheduler).Trace (some ⟨rightRemaining, some who, repaired⟩))
    (clear : (runtime setup).serviceRisk leaks bound who (repaired.recall who)
      (repaired.observe (application setup leaks) who) = false)
    (preserved : ∀ slot raw, original.application.candidates.lookup (who, slot) = .openable raw →
      repaired.application.candidates.lookup (who, slot) = .openable raw)
    (response : (application setup leaks).Action)
    (effective : response ∈ (bounds.menu (runtime setup) leaks).actions who
      (original.recall who) (original.observe (application setup leaks) who))
    (material : (application setup leaks).Submission)
    (transmission : response.transmission = some material)
    (event : (graph setup).EventId) (candidate : Handle (graph setup)) (raw : Raw L)
    (opened : material.call.packet = .opening event candidate raw)
    (breach : SignedContentBreach
      ⟨(who, original.network.nextSerial who), (application setup leaks).packet
        ((application setup leaks).submit original.application who material) who
          (original.network.known who) material⟩) :
    let app := application setup leaks
    let menu := bounds.riskMenu (runtime setup) leaks bound
    let fallback := (menu.nonempty who (repaired.recall who) (repaired.observe app who)).choose
    memory.retainedResponse (runtime setup) leaks menu who
        (repaired.recall who, repaired.observe app who) response = (fallback, memory.shadow) ∧
      ∀ submitted, fallback.transmission = some submitted →
        ¬ SignedContentBreach ⟨(who, repaired.network.nextSerial who), app.packet
          (app.submit repaired.application who submitted) who (repaired.network.known who)
            submitted⟩ := by
  classical
  intro app menu fallback
  have absent := (sourceServiceMissing_signedResponse_unavailable bounds bound original repaired
    who memory frame leftTrace rightTrace clear preserved response effective material transmission
      breach).2
  change response ∉ menu.actions who (repaired.recall who) (repaired.observe app who) at absent
  have inert : memory.repairResponse (runtime setup) leaks who (repaired.observe app who)
      response = (response, memory.shadow) := by
    apply memory.repairResponse_noncommitment (runtime setup) leaks who _ response
    intro submitted same addressed handle called
    have equal := Option.some.inj (transmission.symm.trans same)
    subst submitted
    rw [opened] at called
    cases called
  refine ⟨?_, ?_⟩
  · simp only [BindingMemory.retainedResponse, absent, ↓reduceIte, inert]
    rfl
  · intro submitted same bad
    exact signedContentBreach_risk_excluded bounds bound repaired who rightTrace clear fallback
      submitted same bad (menu.nonempty who _ _).choose_spec

omit [Fintype Player] in
private theorem evidenceRequest_repair_inert
    (memory : BindingMemory (runtime setup) leaks) (who : Player)
    (view : (application setup leaks).PlayerView)
    (response : (application setup leaks).Action)
    (material : (application setup leaks).Submission)
    (transmission : response.transmission = some material)
    (requested : material.evidence ≠ .none) :
    memory.repairResponse (runtime setup) leaks who view response = (response, memory.shadow) := by
  rcases response with ⟨chosen⟩
  change chosen = some material at transmission
  subst chosen
  rcases material with ⟨call, request⟩
  cases request with
  | none => exact False.elim (requested rfl)
  | owned | forward =>
      rcases call with ⟨packet, opening⟩
      cases packet with
      | commitment event candidate =>
          rcases candidate with ⟨author, slot⟩
          cases slot <;> rfl
      | opening | withhold | malformed => rfl

/-- A commitment's actual disclosed evidence makes its original envelope a
signed breach. The real retained implementation falls back at a clear legal
repaired input and copies at an expanded input. The fallback need not emit the
same packet; neither a response frame nor renewed collection is asserted there.
Only effective original membership is used, not original risk-menu support. -/
theorem sourceServiceMissing_signedCommitment_response
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (original repaired : (application setup leaks).Execution) (who : Player)
    (memory : BindingMemory (runtime setup) leaks)
    (frame : memory.Frame (runtime setup) leaks who original repaired)
    (leftTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨leftRemaining, some who, original⟩))
    (rightTrace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup)
      horizon scheduler).Trace (some ⟨rightRemaining, some who, repaired⟩))
    (preserved : ∀ slot raw, original.application.candidates.lookup (who, slot) = .openable raw →
      repaired.application.candidates.lookup (who, slot) = .openable raw)
    (response : (application setup leaks).Action)
    (effective : response ∈ (bounds.menu (runtime setup) leaks).actions who
      (original.recall who) (original.observe (application setup leaks) who))
    (material : (application setup leaks).Submission)
    (transmission : response.transmission = some material)
    (event : (graph setup).EventId) (candidate : Handle (graph setup))
    (committed : material.call.packet = .commitment event candidate)
    (evidence : ((application setup leaks).packet
      ((application setup leaks).submit original.application who material) who
        (original.network.known who) material).evidence ≠ none) :
    let app := application setup leaks
    let menu := bounds.riskMenu (runtime setup) leaks bound
    let message : Message Player (WitnessedPacket (graph setup)) :=
      ⟨(who, original.network.nextSerial who), app.packet
        (app.submit original.application who material) who (original.network.known who) material⟩
    let changed := memory.retainedResponse (runtime setup) leaks menu who
      (repaired.recall who, repaired.observe app who) response
    let fallback := (menu.nonempty who (repaired.recall who) (repaired.observe app who)).choose
    SignedContentBreach message ∧
      (⟨original.application.publicView, original.network.ledger, message⟩ : app.TrafficRecord) ∈
        app.executionTraffic (original.respond app who response) ∧
      (((runtime setup).serviceRisk leaks bound who (repaired.recall who)
            (repaired.observe app who) = false ∧
          changed = (fallback, memory.shadow) ∧
          ∀ submitted, fallback.transmission = some submitted →
            ¬ SignedContentBreach ⟨(who, repaired.network.nextSerial who), app.packet
              (app.submit repaired.application who submitted) who (repaired.network.known who)
                submitted⟩) ∨
        ((runtime setup).serviceRisk leaks bound who (repaired.recall who)
            (repaired.observe app who) = true ∧
          changed = memory.copyResponse (runtime setup) leaks who (repaired.observe app who)
            response ∧
          changed.1 = response ∧
          SignedContentBreach ⟨(who, repaired.network.nextSerial who), app.packet
            (app.submit repaired.application who material) who (repaired.network.known who)
              material⟩)) := by
  classical
  intro app menu message changed fallback
  have called : message.payload.call = .commitment event candidate :=
    (material.emit_call _ _ _).trans committed
  have breach : SignedContentBreach message :=
    Or.inr (Or.inr (Or.inl ⟨event, candidate, called, evidence⟩))
  have actual : response = ⟨some material⟩ := by
    rcases response with ⟨chosen⟩
    exact congrArg ReactiveApplication.Action.mk transmission
  have traffic := (runtime setup).signed_response_traffic leaks original who material leftTrace
  rw [← actual] at traffic
  have requested : material.evidence ≠ .none := by
    intro absent
    apply evidence
    change (material.emit (app.submit original.application who material) who
      (original.network.known who)).evidence = none
    rw [WitnessedSubmission.emit_eq_resolve, absent]
    rfl
  have inert := evidenceRequest_repair_inert memory who (repaired.observe app who) response
    material transmission requested
  refine ⟨breach, traffic, ?_⟩
  cases risky : (runtime setup).serviceRisk leaks bound who (repaired.recall who)
      (repaired.observe app who) with
  | false =>
      have absent := (sourceServiceMissing_signedResponse_unavailable bounds bound original
        repaired who memory frame leftTrace rightTrace risky preserved response effective material
          transmission breach).2
      change response ∉ menu.actions who (repaired.recall who) (repaired.observe app who) at absent
      refine Or.inl ⟨rfl, ?_, ?_⟩
      · simp only [changed, BindingMemory.retainedResponse, absent, ↓reduceIte, inert]
        rfl
      · intro submitted same bad
        exact signedContentBreach_risk_excluded bounds bound repaired who rightTrace risky fallback
          submitted same bad (menu.nonempty who _ _).choose_spec
  | true =>
      have rawRight := (bounds.riskMenu (runtime setup) leaks bound).toRawTrace
        (initialLaw setup) horizon scheduler rightTrace
      have leftRecall := app.history_inputRecall (initialLaw setup) horizon scheduler leftTrace
      have rightRecall := app.history_inputRecall (initialLaw setup) horizon scheduler rawRight
      have transported := (runtime setup).effectiveResponse_openable_transport leaks bounds who
        original repaired leftRecall rightRecall frame.network frame.publicView frame.slots
          preserved response effective
      have admitted : response ∈ menu.actions who (repaired.recall who)
          (repaired.observe app who) := by
        change response ∈ bounds.riskActions (runtime setup) leaks bound who _ _
        rw [bounds.riskActions_of_risk (runtime setup) leaks bound who _ _ risky]
        exact transported.1
      have same : changed = memory.copyResponse (runtime setup) leaks who
          (repaired.observe app who) response := by
        simp only [changed, BindingMemory.retainedResponse, admitted, ↓reduceIte]
      have paired := transported.2.2 material transmission
      have serial : original.network.nextSerial who = repaired.network.nextSerial who :=
        congrArg (fun network : MessageNetwork Player (WitnessedPacket (graph setup)) =>
          network.nextSerial who) frame.network
      have rightBreach : SignedContentBreach ⟨(who, repaired.network.nextSerial who), app.packet
          (app.submit repaired.application who material) who (repaired.network.known who)
            material⟩ := by
        dsimp only [message] at breach
        rw [serial, paired] at breach
        exact breach
      refine Or.inr ⟨rfl, same, ?_, rightBreach⟩
      rw [same]
      exact memory.copyResponse_action (runtime setup) leaks who _ response

/-- The actual full effective owner law and the membership-aware retained
implementation share one draw at reconstructed input. At a selected commitment
that really discloses evidence, support identifies its original traffic and the
actual clear fallback or expanded copied response. No original risk-menu law or
frame after fallback is assumed. Other effective response constructors are left
unclassified by this local signed-commitment result. -/
theorem sourceServiceMissing_signedCommitment_invoke_coupling
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (original repaired : (application setup leaks).Execution) (who : Player)
    (memory : BindingMemory (runtime setup) leaks)
    (frame : memory.Frame (runtime setup) leaks who original repaired)
    (leftTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨leftRemaining, some who, original⟩))
    (rightTrace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup)
      horizon scheduler).Trace (some ⟨rightRemaining, some who, repaired⟩))
    (preserved : ∀ slot raw, original.application.candidates.lookup (who, slot) = .openable raw →
      repaired.application.candidates.lookup (who, slot) = .openable raw)
    (players : Player → (application setup leaks).Policy)
    (reference : List (application setup leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall who).length)
    (effective : ∀ response ∈ (players who (original.recall who)
      (original.observe (application setup leaks) who)).support,
      response ∈ (bounds.menu (runtime setup) leaks).actions who (original.recall who)
        (original.observe (application setup leaks) who)) :
    let app := application setup leaks
    let menu := bounds.riskMenu (runtime setup) leaks bound
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks menu who reference
      (players who)
    let fallback := (menu.nonempty who (repaired.recall who) (repaired.observe app who)).choose
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = app.invoke players who original ∧
      coupling.map Prod.snd = strategy.resume who players (some who) repaired memory ∧
      ∀ next ∈ coupling.support,
        ∃ response ∈ (players who (original.recall who) (original.observe app who)).support,
          let changed := memory.retainedResponse (runtime setup) leaks menu who
            (repaired.recall who, repaired.observe app who) response
          next = (original.respond app who response,
            repaired.respond app who changed.1,
            ⟨changed.2, memory.responses ++
              [(memory.shadow.inputView (runtime setup) leaks (repaired.observe app who),
                response)]⟩) ∧
          ∀ material, response.transmission = some material →
            ∀ event candidate, material.call.packet = .commitment event candidate →
              (app.packet (app.submit original.application who material) who
                (original.network.known who) material).evidence ≠ none →
              let message : Message Player (WitnessedPacket (graph setup)) :=
                ⟨(who, original.network.nextSerial who), app.packet
                  (app.submit original.application who material) who
                    (original.network.known who) material⟩
              SignedContentBreach message ∧
                (⟨original.application.publicView, original.network.ledger, message⟩ :
                  app.TrafficRecord) ∈ app.executionTraffic next.1 ∧
                (((runtime setup).serviceRisk leaks bound who (repaired.recall who)
                    (repaired.observe app who) = false ∧
                  next.2.1 = repaired.respond app who fallback ∧
                  next.2.2.shadow = memory.shadow ∧
                  ∀ submitted, fallback.transmission = some submitted →
                    ¬ SignedContentBreach ⟨(who, repaired.network.nextSerial who), app.packet
                      (app.submit repaired.application who submitted) who
                        (repaired.network.known who) submitted⟩) ∨
                  ((runtime setup).serviceRisk leaks bound who (repaired.recall who)
                    (repaired.observe app who) = true ∧
                    next.2.1 = repaired.respond app who response ∧
                    next.1.network = next.2.1.network)) := by
  classical
  intro app menu strategy fallback
  let law := players who (original.recall who) (original.observe app who)
  let changed (response : app.Action) := memory.retainedResponse (runtime setup) leaks menu who
    (repaired.recall who, repaired.observe app who) response
  let updated (response : app.Action) : BindingMemory (runtime setup) leaks :=
    ⟨(changed response).2, memory.responses ++
      [(memory.shadow.inputView (runtime setup) leaks (repaired.observe app who), response)]⟩
  let coupling := law.map fun response =>
    (original.respond app who response, repaired.respond app who (changed response).1,
      updated response)
  have retainedLaw := BindingMemory.retainedImplementation_respond (runtime setup) leaks menu who
    reference (players who) memory (repaired.recall who) (repaired.observe app who) started
  rw [frame.past, frame.observed] at retainedLaw
  refine ⟨coupling, ?_, ?_, ?_⟩
  · simp only [coupling, PMF.map_comp]
    rfl
  · simp only [coupling, PMF.map_comp, ReactiveApplication.Implementation.resume, ↓reduceIte]
    change law.map _ = (strategy.respond memory
      (repaired.recall who, repaired.observe app who)).map _
    rw [retainedLaw, PMF.map_comp]
    apply map_congr_on_support law
    intro response _chosen
    dsimp only [Function.comp_def, Prod.snd, updated]
    rw [frame.observed]
  · intro next member
    obtain ⟨response, chosen, rfl⟩ := PMF.support_map .. ▸ member
    refine ⟨response, chosen, rfl, ?_⟩
    intro material transmission event candidate committed evidence message
    have split := sourceServiceMissing_signedCommitment_response bounds bound original repaired
      who memory frame leftTrace rightTrace preserved response (effective response chosen) material
        transmission event candidate committed evidence
    refine ⟨split.1, split.2.1, ?_⟩
    rcases split.2.2 with clear | expanded
    · refine Or.inl ⟨clear.1, ?_, ?_, clear.2.2⟩
      · change repaired.respond app who (changed response).1 = repaired.respond app who fallback
        rw [show changed response = (fallback, memory.shadow) from clear.2.1]
      · change (changed response).2 = memory.shadow
        rw [show changed response = (fallback, memory.shadow) from clear.2.1]
    · have same : (changed response).1 = response := expanded.2.2.1
      refine Or.inr ⟨expanded.1, ?_, ?_⟩
      · change repaired.respond app who (changed response).1 = repaired.respond app who response
        rw [same]
      · change (original.respond app who response).network =
          (repaired.respond app who (changed response).1).network
        rw [same]
        have rawRight := (bounds.riskMenu (runtime setup) leaks bound).toRawTrace
          (initialLaw setup) horizon scheduler rightTrace
        exact ((runtime setup).effectiveResponse_openable_transport leaks bounds who original
          repaired (app.history_inputRecall (initialLaw setup) horizon scheduler leftTrace)
            (app.history_inputRecall (initialLaw setup) horizon scheduler rawRight) frame.network
            frame.publicView frame.slots preserved response (effective response chosen)).2.1

end Vegas
