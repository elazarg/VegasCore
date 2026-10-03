/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceAuditableCollection
import Vegas.Game.SourceServiceRecordedCollection
import Vegas.Pending.ReactiveServiceOpening

/-! # Retained resolution responses outside the charged classes

A chosen response cannot supply an arbitrary readiness token: the emitter
uses the token issued by the current public state.
Outside the public packet and recalled-duplicate classifiers, that token names
an unrecorded ready owned opportunity with protected deadline time. At a
resolution node the public checks and actual evidence invariants reduce every
effective response to a retained decision. Private binding material is separate.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- The actual emitter, not a hypothetical signed envelope, supplies a ready
owned opportunity outside the packet classifier. Clear risk and own recalled
actions then establish the unrecorded protected deadline gate. -/
theorem unclassifiedSubmission_opportunity
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    (bound : (graph setup).EventId → Nat)
    (execution : (application setup leaks).Execution) (who : Player)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (clear : (runtime setup).serviceRisk leaks bound who (execution.recall who)
      (execution.observe (application setup leaks) who) = false)
    (material : (application setup leaks).Submission)
    (notPacket : ¬ auditableServiceResponse setup leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) ⟨some material⟩)
    (notRecorded : ¬ recordedServiceResponse setup leaks (execution.recall who) ⟨some material⟩) :
    ∃ event, material.call.packet.event? (graph setup) = some event ∧
      (graph setup).actor? event = some who ∧ execution.application.config.cut.Ready event ∧
      execution.application.publicView.ownTurn? who = some event ∧
      (runtime setup).eventRecorded leaks (execution.recall who) event = false ∧
      execution.application.publicView.InclusionFitsDeadline (runtime setup) bound event := by
  classical
  let app := application setup leaks
  let message : Message Player (WitnessedPacket (graph setup)) :=
    ⟨(who, execution.network.nextSerial who), app.packet
      (app.submit execution.application who material) who (execution.network.known who) material⟩
  have notAuditable : ¬ AuditableServicePacket setup execution.application.publicView who
      message := by
    intro classified
    apply notPacket
    refine ⟨material, rfl, ?_⟩
    rw [localServiceEnvelope_actual setup leaks trace who material]
    exact classified
  have valid : message.payload.tokenValid = true := by
    by_contra notValid
    have invalid : message.payload.tokenValid = false := Bool.eq_false_iff.mpr notValid
    exact notAuditable (Or.inr (Or.inl (Or.inl invalid)))
  obtain ⟨event, named, token⟩ := (WitnessedPacket.tokenValid_iff message.payload).mp valid
  have owned : (graph setup).actor? event = some who := by
    by_contra foreign
    exact notAuditable (Or.inr (Or.inl (Or.inr ⟨event, named, foreign⟩)))
  have unfinished : event ∉ execution.application.config.cut.completed := by
    intro completed
    apply notAuditable
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨event, named, fun uncompleted =>
      uncompleted ((execution.application.config.history_exact event).mpr completed)⟩)))
  have ready : execution.application.config.cut.Ready event :=
    ⟨unfinished, packet_token_issued execution.application who (execution.network.known who)
      material ⟨event⟩ token⟩
  have readyView := (execution.application.publicView_eventReady event).mpr ready
  have turn : execution.application.publicView.ownTurn? who = some event :=
    PublicView.ownTurn?_of_ownTurn _ who event ⟨readyView, owned, fun other otherReady _ =>
      ready_unique _ ((execution.application.publicView_eventReady other).mp otherReady) ready⟩
  have unrecorded : (runtime setup).eventRecorded leaks (execution.recall who) event = false := by
    apply Bool.eq_false_iff.mpr
    intro recorded
    exact notRecorded ⟨event, recorded, named⟩
  exact ⟨event, named, owned, ready, turn, unrecorded,
    (runtime setup).serviceRisk_clear_protected_opportunity leaks bound who (execution.recall who)
      (execution.observe app who) event rfl turn unrecorded clear⟩

variable [Fintype Player]

omit [Fintype Player] in
/-- Public packet complements at an actual ready timely resolution establish
conformance. The signed certificate, token and association are checked rather
than supplied as a fresh-envelope premise. -/
theorem unclassifiedResolutionSubmission_conforms
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    (execution : (application setup leaks).Execution) (who : Player)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (event : (graph setup).EventId) (payload : L.Ty)
    (binding : FieldRef (graph setup).layout (.binding who payload))
    (checks : List (GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks)
    (node : nodeView (graph setup) event = .resolve who payload binding checks outputEq codeEq)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.publicView.WithinDeadline (runtime setup) event)
    (material : (application setup leaks).Submission)
    (named : material.call.packet.event? (graph setup) = some event)
    (notPacket : ¬ auditableServiceResponse setup leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) ⟨some material⟩) :
    (runtime setup).freshServiceEnvelope execution.application.publicView
      ⟨(who, execution.network.nextSerial who), (application setup leaks).packet
        ((application setup leaks).submit execution.application who material) who
          (execution.network.known who) material⟩ := by
  classical
  let app := application setup leaks
  let message : Message Player (WitnessedPacket (graph setup)) :=
    ⟨(who, execution.network.nextSerial who), app.packet
      (app.submit execution.application who material) who
        (execution.network.known who) material⟩
  have notAuditable : ¬ AuditableServicePacket setup execution.application.publicView who
      message := by
    intro classified
    apply notPacket
    refine ⟨material, rfl, ?_⟩
    rw [localServiceEnvelope_actual setup leaks trace who material]
    exact classified
  have content : ¬ SignedContentBreach message := fun bad => notAuditable (Or.inl bad)
  have compatible : message.payload.call.MatchesNode := by
    by_contra incompatible
    exact notAuditable (Or.inr (Or.inr (Or.inl incompatible)))
  have token : message.payload.token = some ⟨event⟩ := by
    exact (runtime setup).reactiveApplication_packet_token leaks execution.application who
      (execution.network.known who) material |>.trans
        (execution.application.publicView_tokenFor_of_ready material.call.packet event
          named ready)
  have permitted : (runtime setup).freshServiceEnvelope execution.application.publicView
      message := by
    have packetNamed : message.payload.call.event? (graph setup) = some event := named
    cases called : message.payload.call with
    | malformed raw =>
        rw [called] at packetNamed
        cases packetNamed
    | commitment addressed candidate =>
        rw [called] at packetNamed
        have addressedEq : addressed = event := Option.some.inj packetNamed
        subst addressed
        simp only [Payload.MatchesNode, called, node] at compatible
    | withhold addressed =>
        rw [called] at packetNamed
        have addressedEq : addressed = event := Option.some.inj packetNamed
        subst addressed
        have empty : message.payload.evidence = none := by
          by_contra present
          exact content (Or.inr (Or.inl ⟨event, called, present⟩))
        simp only [freshServiceEnvelope, called, node]
        exact ⟨(execution.application.publicView_eventReady event).mpr ready,
          timely, empty, token, rfl⟩
    | opening addressed candidate raw =>
        rw [called] at packetNamed
        have addressedEq : addressed = event := Option.some.inj packetNamed
        subst addressed
        have certified : certifiedOpening message.payload = true := by
          by_contra notCertified
          have uncertified := Bool.eq_false_iff.mpr notCertified
          exact content (Or.inr (Or.inr (Or.inr
            ⟨event, candidate, raw, called, uncertified⟩)))
        have publicChecks : ¬ (execution.application.publicView.openingGuardsAccepted
            message.payload = false ∨ candidate.1 ≠ who ∨
              execution.application.publicView.accepted binding.field ≠ some candidate) :=
          by
            intro bad
            apply notAuditable
            refine Or.inr (Or.inr (Or.inr (Or.inr ⟨event, turn,
              Or.inr ⟨candidate, raw, called, ?_⟩⟩)))
            simpa only [node] using bad
        have guarded : execution.application.publicView.openingGuardsAccepted
            message.payload = true := by
          by_contra rejected
          exact publicChecks (Or.inl (Bool.eq_false_iff.mpr rejected))
        have handleOwner : candidate.1 = who := by
          by_contra foreign
          exact publicChecks (Or.inr (Or.inl foreign))
        have associated : execution.application.publicView.accepted binding.field =
            some candidate := by
          by_contra absent
          exact publicChecks (Or.inr (Or.inr absent))
        have rawType : raw.ty = payload := by
          have guards := guarded
          simp only [PublicView.openingGuardsAccepted, called, node] at guards
          cases typed : raw.as? payload with
          | none => simp only [typed, Option.any_none, Bool.false_eq_true] at guards
          | some value =>
              rcases raw with ⟨kind, input⟩
              unfold Raw.as? at typed
              split at typed
              · assumption
              · cases typed
        simp only [freshServiceEnvelope, called, node]
        exact ⟨(execution.application.publicView_eventReady event).mpr ready,
          timely, certified, guarded, rfl, handleOwner, associated, rawType,
          token⟩
  exact permitted

/-- At an actual ready resolution, an effective response outside the packet
and recalled-duplicate classes is retained. The conformance premise is derived
from public classifier complements and legal trace facts rather than assumed. -/
theorem unclassifiedResolution_retained
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    (execution : (application setup leaks).Execution) (who : Player)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (clear : (runtime setup).serviceRisk leaks bound who (execution.recall who)
      (execution.observe (application setup leaks) who) = false)
    (event : (graph setup).EventId) (payload : L.Ty)
    (binding : FieldRef (graph setup).layout (.binding who payload))
    (checks : List (GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks)
    (node : nodeView (graph setup) event = .resolve who payload binding checks outputEq codeEq)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (response : (application setup leaks).Action)
    (available : response ∈ (bounds.menu (runtime setup) leaks).actions who (execution.recall who)
      (execution.observe (application setup leaks) who))
    (notPacket : ¬ auditableServiceResponse setup leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) response)
    (notRecorded : ¬ recordedServiceResponse setup leaks (execution.recall who) response) :
    response ∈ bounds.riskActions (runtime setup) leaks bound who (execution.recall who)
      (execution.observe (application setup leaks) who) := by
  classical
  let app := application setup leaks
  let view := execution.observe app who
  let menu := bounds.riskMenu (runtime setup) leaks bound
  have rawTrace := menu.toRawTrace (initialLaw setup) horizon scheduler trace
  have facts := legalFacts setup leaks horizon scheduler _ rawTrace
  rw [bounds.riskActions_of_clear (runtime setup) leaks bound who _ _ clear]
  cases response with
  | mk transmission =>
      cases transmission with
      | none => exact bounds.silence_canonical (runtime setup) leaks who _ _
      | some material =>
          obtain ⟨other, named, owned, ready, selected, unrecorded, fits⟩ :=
            unclassifiedSubmission_opportunity bound execution who rawTrace clear material
              notPacket notRecorded
          have same : other = event := Option.some.inj (selected.symm.trans turn)
          subst other
          have permitted := unclassifiedResolutionSubmission_conforms execution who rawTrace
            event payload binding checks outputEq codeEq node turn ready fits.withinDeadline
              material named notPacket
          have decided := (runtime setup).service_resolution_response leaks bounds execution who
            facts.evidence facts.binding facts.inputs event payload binding checks outputEq codeEq
              node material named available permitted
          have noBind : ∀ owner kind bindOutput bindCode,
              nodeView (graph setup) event ≠ .bind owner kind bindOutput bindCode := by
            intro owner kind bindOutput bindCode
            rw [node]
            intro same
            cases same
          have retain (choice : Bool)
              (responseEq : (⟨some material⟩ : app.Action) = (runtime setup).serviceDecision leaks
                who (execution.recall who) view event
                  (cast (congrArg EventField.Action outputEq.symm) choice)) :
              (⟨some material⟩ : app.Action) ∈ bounds.canonicalActions (runtime setup) leaks who
                (execution.recall who) view := by
            have canonical := (runtime setup).canonicalServiceDecision_eq_of_not_bind leaks who
              (execution.recall who) view event
                (cast (congrArg EventField.Action outputEq.symm) choice) noBind
            rw [← canonical] at responseEq
            rw [responseEq]
            apply bounds.canonical_decision_retained (runtime setup) leaks who _ _ event _ turn
              owned ((execution.application.publicView_eventReady event).mpr ready)
              fits.withinDeadline unrecorded
            · simp only [MessageBounds.canonicalChoices, node]
              exact Finset.mem_image.mpr ⟨choice, Finset.mem_univ _, rfl⟩
            · rw [← responseEq]
              exact available
          rcases decided with withheld | ⟨value, _, _, opened⟩
          · exact retain false withheld
          · exact retain true opened

end Vegas
