/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterDecisionData
import Vegas.Compile.EventGraphResolutionFields
import Vegas.Pending.RevealEvidence
import Interaction.ReactiveMessageIdentity

/-! # Fresh roster openings carry newly issued certificates

The source consumes each commitment exactly once. Before its first opening in
the current phase, no earlier public envelope can carry that handle's certificate.
The raw owned request is therefore already the effective response representative.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem rosterOpening?_binding (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (who : Player) (event : (graph setup).EventId)
    (view : (application setup leaks).PlayerView) (candidate : Handle (graph setup)) (raw : Raw L)
    (opening : rosterOpening? setup leaks who event view = some (candidate, raw)) :
    ∃ field, ((graph setup).nodes event).resolutionField? = some field ∧
      view.application.publicView.accepted field = some candidate := by
  unfold rosterOpening? at opening
  cases node : nodeView (graph setup) event with
  | sample => simp only [node] at opening; cases opening
  | bind => simp only [node] at opening; cases opening
  | resolve owner payload binding checks outputEq codeEq =>
      simp only [node] at opening
      split at opening
      · cases opening
      · cases opening
      · obtain ⟨actual, associated, opening⟩ := Option.bind_eq_some_iff.mp opening
        split at opening
        · cases opening
        · have same := (Prod.mk.inj (Option.some.inj opening)).1
          subst actual
          refine ⟨binding.field, ?_, associated⟩
          have selected := EventGraph.EventCode.resolutionField?_cast outputEq
            ((graph setup).nodes event)
          rw [codeEq] at selected
          exact selected.symm

theorem PublicCheckpoint.unresolved_evidence
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {initial : State L setup.context} {Γ : SourceCtx Player L}
    {source : Config Player L Γ} {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (checkpoint : PublicCheckpoint setup leaks initial source refs rank execution)
    (event : (graph setup).EventId) (unfinished : rank ≤ event.val)
    (field : (graph setup).Field)
    (resolves : ((graph setup).nodes event).resolutionField? = some field)
    (candidate : Handle (graph setup))
    (associated : execution.application.accepted field = some candidate)
    (message : Message Player (WitnessedPacket (graph setup)))
    (published : message ∈ execution.network.ledger) (raw : Raw L) :
    message.payload.evidence ≠ some ⟨candidate, raw⟩ := by
  have absent : event ∉
      ((graph setup).publicObserve execution.application.config).completionOrder := by
    intro member
    have completed := (execution.application.config.history_exact event).mp member
    have earlier := (checkpoint.ordered.2 event).mp completed
    omega
  have ledger : execution.network.ledger = publicationLedger execution.application.accepted
      ((graph setup).publicObserve execution.application.config) := by
    rw [checkpoint.accepted]
    exact checkpoint.ledger
  exact publicationLedger_unresolved_evidence execution.application.accepted
    checkpoint.binding.accepted_injective (resolution_field_injective setup.program)
    ((graph setup).publicObserve execution.application.config) event absent field resolves
    candidate associated message (ledger ▸ published) raw

variable [Fintype Player]

/-- At every legal retained decision a fresh opening is already normalized.
All prerequisites follow from actual source and network history. -/
theorem roster_fresh_normal
    (setup : Setup (Player := Player) (L := L)) [setup.FiniteInitialLaw]
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((rosterMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (active : control.actor = some who)
    (action : (application setup leaks).Action)
    (fresh : rosterFresh? setup leaks rosters who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) = some action) :
    ((runtime setup).reactiveNormalization leaks).action who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) action = action := by
  let app := application setup leaks
  let menu := rosterMenu setup leaks bounds rosters
  let profile : BehavioralProfile setup.program :=
    fun owner => RevealOnly.uniformPolicy owner setup.program reveals
  obtain ⟨event, slot, phaseStart, prior, sample, initial, state, selected, initialSupport,
      related, _, startReady, offset, serials, published, reached, activated,
      unchanged, _⟩ :=
    roster_decision_phase setup leaks bounds rosters network reveals openable
      who control trace active
  obtain ⟨sentEvent, candidate, raw, sentTurn, ownedEvent, opening, rfl, absent⟩ :=
    rosterFresh?_shape setup leaks rosters who _ _ action fresh
  have sentReady := (PublicView.ownTurn?_spec _ who sentEvent sentTurn).1
  change control.execution.application.publicView.EventReady sentEvent at sentReady
  rw [unchanged] at sentReady
  cases (soleReady_of_ready setup phaseStart.application startReady).2 sentEvent sentReady
  have data := owner_choices_at_prefix setup leaks bounds profile who initial initialSupport
    setup.program reveals profile (ContextRefs.initial setup.context (outputLayout setup.program))
    (Revelations.initial setup.context) (outputEmbedding setup.program)
    (initialRefsBefore setup.program) 0 (CompiledPolicySuffix.whole setup.program profile)
    event.val event.isLt state phaseStart related event (by omega) ownedEvent startReady
  obtain ⟨expected, expectedRaw, priorOpening, owned, valid, _, _⟩ := data.2.2
  have same := rosterOpening?_application_eq setup leaks who event control.execution phaseStart
    unchanged
  rw [opening, priorOpening] at same
  cases Option.some.inj same
  have covered : ∀ player past view response,
      response ∈ (menu.uniformResponses player past view).support →
        response ∈ rosterActions setup leaks bounds rosters player past view := by
    intro player past view response supported
    exact (menu.uniformResponses_support player past view response).mp supported
  obtain ⟨chosen, frame, _, recorded, _⟩ := roster_window_posterior setup leaks bounds rosters
    phaseStart event who (soleReady_of_ready setup phaseStart.application startReady)
      ownedEvent candidate raw
    priorOpening owned valid (offset who) serials
    published menu.uniformResponses covered network ((rosters event).take slot)
    (roster_count_before selected).le prior reached
  rw [activated] at absent
  change ∀ entry ∈ (prior.recall who).drop (rosterOffset setup rosters who event),
    entry.action ≠ (runtime setup).windowOpening leaks event candidate raw at absent
  have unopened : chosen = none := by
    cases chosen with
    | none => rfl
    | some slot =>
        obtain ⟨entry, member, emitted⟩ := recorded.mp rfl
        exact False.elim (absent entry member emitted)
  have clean := frame.before_published (runtime setup) leaks who event candidate raw
    (rosterOffset setup rosters who event) chosen _ phaseStart prior
    (by simp only [unopened, openingPassed, Option.any_none])
  have currentClean : control.execution.network.Satisfies fun message =>
      message.id ∈ control.execution.network.ledger.map Message.id := by
    rw [activated]
    exact clean.learn who sample
  have ledger : control.execution.network.ledger = phaseStart.network.ledger := by
    rw [activated]
    exact frame.ledger
  have rawTrace := menu.toRawTrace (initialLaw setup) (rosterPlan setup rosters).length
    (rosterScheduler setup leaks rosters network) trace
  have unique := app.uniqueIds_history (rosterScheduler setup leaks rosters network)
    (initialLaw setup) (rosterPlan setup rosters).length control rawTrace
  have recall := app.history_inputRecall (initialLaw setup) (rosterPlan setup rosters).length
    (rosterScheduler setup leaks rosters network) rawTrace
  obtain ⟨context, source, refs, checkpoint⟩ := related.checkpoint setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (Revelations.initial setup.context) (outputRef setup.program) 0 event.val state phaseStart
  obtain ⟨field, resolves, associated⟩ := rosterOpening?_binding setup leaks who event
    (control.execution.observe app who) candidate raw opening
  have bound : phaseStart.application.accepted field = some candidate := by
    change control.execution.application.accepted field = some candidate at associated
    rwa [unchanged] at associated
  have unavailable := EvidenceRequest.forwardingPacket_eq_none
    (control.execution.network.known who) (⟨candidate, raw⟩ : OpeningFact (graph setup)) (by
      intro message known
      have included := unique.known_published who message known
        (currentClean.known who message known)
      exact checkpoint.unresolved_evidence event (by omega) field resolves candidate bound message
        (ledger ▸ included) raw)
  have known : ReactiveApplication.ResponseMenu.knownPackets (control.execution.recall who)
      (control.execution.observe app who) = control.execution.network.known who :=
    (app.known_from_recall control.execution who recall).symm
  have fixed : control.execution.application.candidates.lookup candidate = .openable raw := by
    rw [unchanged]
    exact valid
  have localFixed : control.execution.application.candidates.lookup (who, candidate.2) =
      .openable raw := by simpa only [← owned] using fixed
  simp only [ReactiveApplication.SubmissionNormalization.action, windowOpening,
    reactiveNormalization, WitnessedSubmission.normalizeReactive,
    Submission.normalizeReactive_none, disclosureSubmission, Submission.candidateAfter_opening]
  rw [known]
  exact congrArg (fun evidence => (⟨some (.submit ⟨⟨.opening event candidate raw, none⟩,
    evidence⟩)⟩ : app.Action)) (EvidenceRequest.normalize_owned_of_no_forward who
      (fun slot => control.execution.application.candidates.lookup (who, slot))
      (control.execution.network.known who) ⟨candidate, raw⟩ owned localFixed unavailable)

end Vegas
