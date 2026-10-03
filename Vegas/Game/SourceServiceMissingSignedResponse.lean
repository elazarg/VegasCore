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

For an opening, the retained implementation consequently selects its legal
fallback before emission and leaves the shadow unchanged. This identifies a
real local replacement point. It does not establish a whole-policy splice,
future zero collection, or a utility comparison after risk has opened.
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

end Vegas
