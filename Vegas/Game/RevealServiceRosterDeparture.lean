/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterTraffic

/-! # Signed evidence for responses outside the revelation roster

The checker uses only an authentic phase, prior ledger and signed envelope.
The runtime evidence invariant connects a passing fresh packet to the owner's
canonical response; the serial test supplies the once-per-phase condition.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

private theorem openingTraffic_granted_actor
    (record : (application setup leaks).TrafficRecord) (event : (graph setup).EventId)
    (grant : record.observation.serviceGrant = some event)
    (conforming : openingTraffic setup leaks record) :
    (graph setup).actor? event = some record.input.broadcaster := by
  unfold openingTraffic at conforming
  cases call : record.input.envelope.payload.call with
  | commitment | withhold | malformed => simp only [call] at conforming
  | opening actual candidate raw =>
      rw [call] at conforming
      obtain ⟨granted, _, _, _, linked⟩ := conforming
      rw [grant] at granted
      cases Option.some.inj granted
      cases node : nodeView (graph setup) event with
      | bind | sample => simp only [node] at linked
      | resolve owner payload binding checks outputEq codeEq =>
          simp only [node] at linked
          have actors := congrArg EventCode.actor codeEq
          rw [EventCode.actor_cast outputEq ((graph setup).nodes event)] at actors
          exact actors.trans (congrArg some linked.1.symm)

/-- A passing fresh packet has the same effective representation as the
authentic opening reconstructed from the owner's actual application view. -/
theorem openingTraffic_roster_normalization
    (execution : (application setup leaks).Execution) (who : Player)
    (sound : ((runtime setup).packetEvidence leaks).Sound execution)
    (binding : execution.application.BindingInvariant)
    (event : (graph setup).EventId)
    (grant : execution.application.serviceGrant = some event)
    (candidate : Handle (graph setup)) (raw : Raw L)
    (owned : candidate.1 = who)
    (fixed : execution.application.candidates.lookup candidate = .openable raw)
    (opening : rosterOpening? setup leaks who event
      (execution.observe (application setup leaks) who) = some (candidate, raw))
    (submission : WitnessedSubmission (graph setup))
    (conforming : openingTraffic setup leaks
      ⟨execution.application.publicView, execution.network.ledger,
        ⟨who, ⟨(who, execution.network.nextSerial who), submission.emit
          ((application setup leaks).submit execution.application who submission) who
            (execution.network.known who)⟩⟩⟩) :
    submission.normalizeReactive who
        ((application setup leaks).observePlayer execution.application who)
        (execution.network.known who) =
      (disclosureSubmission (.opening event candidate raw)).normalizeReactive who
        ((application setup leaks).observePlayer execution.application who)
        (execution.network.known who) := by
  obtain ⟨⟨next, accepted⟩, certified⟩ := openingTraffic_accepted setup leaks execution who
    sound binding submission conforming
  unfold openingTraffic at conforming
  simp only [WitnessedSubmission.emit_call] at conforming
  cases call : submission.call.packet with
  | commitment | withhold | malformed => simp only [call] at conforming
  | opening actual offered claimed =>
      simp only [call] at conforming
      obtain ⟨granted, _, _, _, linked⟩ := conforming
      change execution.application.serviceGrant = some actual at granted
      rw [grant] at granted
      cases Option.some.inj granted
      cases node : nodeView (graph setup) event with
      | bind | sample => simp only [node] at linked
      | resolve owner payload ref checks outputEq codeEq =>
          simp only [node] at linked
          obtain ⟨ownerEq, _, _, _, _⟩ := linked
          subst owner
          have associated : execution.application.accepted ref.field = some candidate := by
            unfold rosterOpening? at opening
            simp only [node] at opening
            split at opening
            · cases opening
            · cases opening
            · obtain ⟨actual, associated, opening⟩ := Option.bind_eq_some_iff.mp opening
              split at opening
              · cases opening
              · have same := (Prod.mk.inj (Option.some.inj opening)).1
                subst actual
                exact associated
          exact (runtime setup).accepted_certified_opening_normalization leaks
            execution.application next who event payload ref checks outputEq codeEq node
            candidate raw associated owned fixed (execution.network.known who) submission
            (execution.network.nextSerial who) (by rw [call]; rfl) certified accepted

variable [Fintype Player]

/-- Every first additional effective response in the real roster protocol
creates a forbidden record signed by its acting player. This includes a second
fresh canonical opening; known-envelope replays remain admitted. -/
theorem roster_extra_traffic (bounds : MessageBounds (graph setup))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks) (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((rosterMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (active : control.actor = some who)
    (response : (application setup leaks).Action)
    (effective : response ∈ (bounds.menu (runtime setup) leaks).actions who
      (control.execution.recall who) (control.execution.observe (application setup leaks) who))
    (excluded : response ∉ (rosterMenu setup leaks bounds rosters).actions who
      (control.execution.recall who) (control.execution.observe (application setup leaks) who)) :
    ∃ record, (application setup leaks).trafficStep (some control)
      (some ⟨control.remaining, none,
        control.execution.respond (application setup leaks) who response⟩) = [record] ∧
      record.input.envelope.sender = who ∧
      permittedRosterEnvelope setup leaks (envelopeEvidence setup leaks record) = false := by
  classical
  let app := application setup leaks
  let menu := rosterMenu setup leaks bounds rosters
  obtain ⟨submission, rfl⟩ := roster_extra_submission setup leaks bounds rosters who _ _
    response effective excluded
  let record : app.TrafficRecord :=
    ⟨control.execution.application.publicView, control.execution.network.ledger,
      ⟨who, ⟨(who, control.execution.network.nextSerial who), submission.emit
        (app.submit control.execution.application who submission) who
          (control.execution.network.known who)⟩⟩⟩
  have actual : app.trafficStep (some control)
      (some ⟨control.remaining, none, control.execution.respond app who
        ⟨some (.submit submission)⟩⟩) = [record] := by
    have step := app.trafficStep_submit control.execution control.remaining who submission
    convert step using 1 <;> rfl
  refine ⟨record, actual, rfl, ?_⟩
  cases verdict : permittedRosterEnvelope setup leaks (envelopeEvidence setup leaks record) with
  | false => rfl
  | true =>
      have rawTrace := menu.toRawTrace (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network) trace
      have serials := app.serialsBeforeNext_history (rosterScheduler setup leaks rosters network)
        (initialLaw setup) (rosterPlan setup rosters).length rawTrace
      obtain published | ⟨nonce, conforming⟩ :=
        (permittedRosterEnvelope_iff setup leaks record rfl).mp verdict
      · exact (serials.next_unpublished who published).elim
      · obtain ⟨event, slot, granted, prior, sample, initial, state, selected, initialSupport,
          related, _, grant, _, _, _, _, _, unchanged⟩ :=
          roster_decision_phase setup leaks bounds rosters network reveals openable
            who control trace active
        have currentGrant : control.execution.application.serviceGrant = some event := by
          rw [unchanged, grant]
        have ownedEvent := openingTraffic_granted_actor setup leaks record event currentGrant
          conforming
        let profile : BehavioralProfile setup.program :=
          fun owner => RevealOnly.uniformPolicy owner setup.program reveals
        have data := owner_choices_at_prefix setup leaks bounds profile who initial initialSupport
          setup.program reveals profile
          (EventLowering.ContextRefs.initial setup.context
            (EventLowering.outputLayout setup.program))
          (Revelations.initial setup.context) (EventLowering.outputEmbedding setup.program)
          (EventLowering.initialRefsBefore setup.program) 0
          (EventLowering.CompiledPolicySuffix.whole setup.program profile)
          event.val event.isLt state granted related event (by omega) ownedEvent grant
        obtain ⟨candidate, raw, opening, owned, valid, _, _⟩ := data.2.2
        have currentOpening : rosterOpening? setup leaks who event
            (control.execution.observe app who) = some (candidate, raw) := by
          rw [rosterOpening?_application_eq setup leaks who event control.execution granted
            unchanged]
          exact opening
        have currentValid : control.execution.application.candidates.lookup candidate =
            .openable raw := by rw [unchanged]; exact valid
        have fresh := (roster_fresh_iff_serial setup leaks bounds rosters network reveals openable
          who control trace active event currentGrant ownedEvent candidate raw currentOpening).mpr
            nonce
        have canonical := roster_fresh_normal setup leaks bounds rosters network reveals openable
          who control trace active ((runtime setup).windowOpening leaks event candidate raw) fresh
        obtain ⟨context, source, refs, checkpoint⟩ := related.checkpoint setup.program
          (EventLowering.ContextRefs.initial setup.context
            (EventLowering.outputLayout setup.program))
          (Revelations.initial setup.context) (EventLowering.outputRef setup.program)
          0 event.val state granted
        have binding : control.execution.application.BindingInvariant :=
          unchanged.symm ▸ checkpoint.binding
        have sound := ((runtime setup).packetEvidence leaks).history_sound (initialLaw setup)
          (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network) rawTrace
        have same := openingTraffic_roster_normalization setup leaks control.execution who sound
          binding event currentGrant candidate raw owned currentValid currentOpening submission
          conforming
        have recalled := app.history_inputRecall (initialLaw setup)
          (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network) rawTrace
        have known : ReactiveApplication.ResponseMenu.knownPackets (control.execution.recall who)
            (control.execution.observe app who) = control.execution.network.known who :=
          (app.known_from_recall control.execution who recalled).symm
        have normal := (bounds.menu_mem (runtime setup) leaks who _ _ _).mp effective |>.2
        have actionEq : ((runtime setup).reactiveNormalization leaks).action who
            (control.execution.recall who) (control.execution.observe app who)
              ⟨some (.submit submission)⟩ =
            ((runtime setup).reactiveNormalization leaks).action who
              (control.execution.recall who) (control.execution.observe app who)
              ((runtime setup).windowOpening leaks event candidate raw) := by
          simp only [ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
            windowOpening]
          rw [known]
          exact congrArg (fun value => (⟨some (.submit value)⟩ : app.Action)) same
        rw [normal, canonical] at actionEq
        apply False.elim
        apply excluded
        change _ ∈ rosterActions setup leaks bounds rosters who _ _
        apply Finset.mem_inter.mpr
        refine ⟨Finset.mem_union_right _ ?_, effective⟩
        rw [actionEq, fresh]
        simp

end Vegas.SourceProgram.RevealService
