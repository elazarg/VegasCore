/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceEnforcement
import Vegas.Pending.ReactivePacketEvidence
import Vegas.Pending.EventPublicState
import Vegas.Pending.ReactiveRevealTranscript
import Interaction.ReactiveAuditCollection

/-! # Send-time traffic rules for the revelation service

These rules read the transmission phase, signed author and prior ledger. No audit
verdict uses them: settlement judges packets against the settled record. They
are proof devices for classifying additional responses. A fresh ordinary
transmission conforms when it is a certified opening of a ready, timely
resolution. The watcher transmits nothing on compliant executions.

A packet that conforms to the service rule is a conforming opening here
(`Vegas.openingTraffic_of_fresh`), so a breach of these rules breaches the
service rule, whose breach dooms its author at settlement.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The public part of a new opening. It does not inspect candidate meanings,
private source cells or a player's intended strategy. -/
def openingTraffic (record : (application setup leaks).TrafficRecord) : Prop :=
  match record.envelope.payload.call with
  | .opening event candidate raw =>
      record.observation.EventReady event ∧
      (match record.observation.activatedAt event with
        | none => False
        | some entered => record.observation.clock - entered < (runtime setup).deadline event) ∧
      record.envelope.payload.evidence = some ⟨candidate, raw⟩ ∧
      (match nodeView (graph setup) event with
        | .resolve owner payload binding _ _ _ =>
            record.envelope.sender = owner ∧ record.envelope.sender = owner ∧
            candidate.1 = owner ∧ record.observation.accepted binding.field = some candidate ∧
            raw.ty = payload
        | .bind .. | .sample .. => False)
  | .commitment .. | .withhold .. | .malformed .. => False

/-- In a reveal-only graph a packet conforming to the service rule is a
conforming opening by its signer. -/
theorem openingTraffic_of_fresh (reveals : setup.program.RevealOnly)
    (view : (application setup leaks).PublicObservation)
    (ledger : List (Message Player (application setup leaks).Payload))
    (message : Message Player (application setup leaks).Payload)
    (fresh : (runtime setup).freshServiceEnvelope view message) :
    openingTraffic setup leaks ⟨view, ledger, message⟩ := by
  rcases message with ⟨id, ⟨call, evidence, token⟩⟩
  cases call with
  | commitment event candidate =>
      obtain ⟨⟨_, _, owned⟩, _⟩ := fresh
      revert owned
      cases nodeView (graph setup) event with
      | bind owner payload kind _ =>
          exact (reveal_publications setup reveals event owner payload kind).elim
      | sample => intro owned; exact owned.elim
      | resolve => intro owned; exact owned.elim
  | opening event candidate raw =>
      obtain ⟨ready, timely, certified, _, linked⟩ := fresh
      have evidenced : evidence = some ⟨candidate, raw⟩ := by
        obtain ⟨_, _, _, _, same⟩ := (certifiedOpening_iff _).mp certified
        cases same
        rfl
      refine ⟨ready, timely, evidenced, ?_⟩
      revert linked
      cases nodeView (graph setup) event with
      | resolve owner payload binding checks outputEq codeEq =>
          rintro ⟨sender, owned, accepted, typed, _⟩
          exact ⟨sender, sender, owned, accepted, typed⟩
      | bind => intro linked; exact linked.elim
      | sample => intro linked; exact linked.elim
  | withhold => exact fresh.elim
  | malformed => exact fresh.elim

open Classical in
/-- The send-time rule attributes every fresh packet to its signed author. -/
def permittedTraffic (watcher : Player)
    (record : (application setup leaks).TrafficRecord) : Bool :=
  decide (record.envelope.sender ≠ watcher ∧
    (record.envelope.id ∈ record.ledger.map Message.id ∨ openingTraffic setup leaks record))

theorem permittedTraffic_iff (watcher : Player)
    (record : (application setup leaks).TrafficRecord) :
    permittedTraffic setup leaks watcher record = true ↔
      record.envelope.sender ≠ watcher ∧
        (record.envelope.id ∈ record.ledger.map Message.id ∨
          openingTraffic setup leaks record) := by
  classical
  simp only [permittedTraffic, decide_eq_true_eq]

/-- An authenticated certificate and the public conformance checks suffice
for real inclusion. The proof uses the runtime's invariant; the checker never
reads the hidden candidate or binding store. -/
theorem openingTraffic_accepted
    (execution : (application setup leaks).Execution) (who : Player)
    (sound : ((runtime setup).packetEvidence leaks).Sound execution)
    (binding : execution.application.BindingInvariant)
    (submission : WitnessedSubmission (graph setup))
    (conforming : openingTraffic setup leaks
      ⟨execution.application.publicView, execution.network.ledger,
        ⟨(who, execution.network.nextSerial who), submission.emit
          ((application setup leaks).submit execution.application who submission) who
            (execution.network.known who)⟩⟩) :
    let state := (application setup leaks).submit execution.application who submission
    let packet := submission.emit state who (execution.network.known who)
    (∃ next, (application setup leaks).handle state
      ⟨(who, execution.network.nextSerial who), packet⟩ = some next) ∧
      certifiedOpening packet = true := by
  dsimp only
  unfold openingTraffic at conforming
  simp only [WitnessedSubmission.emit_call] at conforming
  cases packet : submission.call.packet with
  | malformed | commitment | withhold => simp only [packet] at conforming
  | opening event candidate raw =>
      simp only [packet] at conforming
      obtain ⟨ready, timely, carried, linked⟩ := conforming
      have unchanged : (application setup leaks).submit execution.application who submission =
          execution.application := by
        rcases submission with ⟨⟨call, material⟩, request⟩
        dsimp only at packet
        subst call
        cases material <;> rfl
      rw [unchanged] at carried ⊢
      have valid := submission.emit_sound execution.application who
        (execution.network.known who)
        (fun message member fact evidence => sound.known who message member fact (by
          simp only [packetEvidence, evidence, Option.toList_some, List.mem_singleton]))
        ⟨candidate, raw⟩ carried
      have emitted : submission.emit execution.application who (execution.network.known who) =
          ⟨.opening event candidate raw, some ⟨candidate, raw⟩,
            execution.application.publicView.tokenFor (.opening event candidate raw)⟩ := by
        change (⟨(submission.emit execution.application who (execution.network.known who)).call,
          (submission.emit execution.application who (execution.network.known who)).evidence,
          (submission.emit execution.application who (execution.network.known who)).token⟩ :
            WitnessedPacket (graph setup)) = _
        rw [WitnessedSubmission.emit_call, WitnessedSubmission.emit_token, packet, carried]
      rw [emitted]
      refine ⟨?_, by simp only [certifiedOpening, decide_true]⟩
      cases node : nodeView (graph setup) event with
      | bind | sample => simp only [node] at linked
      | resolve owner payload ref checks outputEq codeEq =>
          simp only [node] at linked
          obtain ⟨ownerEq, _sender, owned, associated, typed⟩ := linked
          subst owner
          rcases raw with ⟨rawTy, value⟩
          change rawTy = payload at typed
          subst rawTy
          change execution.application.candidates.lookup candidate =
            .openable ⟨payload, value⟩ at valid
          have stored := binding.opening_stored ref candidate value associated valid
          have actualReady := (execution.application.publicView_eventReady event).mp ready
          have available : ∀ field ∈ insert ref.field (GuardCheck.listReadFields checks),
              (execution.application.config.store field).isSome = true := by
            intro field read
            apply execution.application.config.read_available actualReady
            have fields : ((graph setup).nodes event).readFields =
                insert ref.field (GuardCheck.listReadFields checks) := by
              calc
                _ = (cast (congrArg (EventCode (graph setup).layout) outputEq)
                    ((graph setup).nodes event)).readFields :=
                  (EventCode.readFields_cast outputEq ((graph setup).nodes event)).symm
                _ = (EventCode.resolve who payload ref checks).readFields :=
                  congrArg EventCode.readFields codeEq
                _ = _ := rfl
            rwa [fields]
          obtain ⟨result, resolved⟩ := Option.isSome_iff_exists.mp
            (EventCode.resolveOutput?_isSome ref checks true execution.application.config.store
              available)
          rw [execution.application.publicView_tokenFor_of_ready _ event rfl actualReady,
            reactiveApplication_handle_of_tokenValid (runtime setup) leaks _ _
              (WitnessedPacket.tokenValid_opening _ _ _ _)]
          exact ⟨_, handle_opening_eq (runtime setup) execution.application _ event candidate
            who payload ref checks outputEq codeEq node actualReady timely rfl
            owned associated value valid stored result resolved⟩

/-- Every rejected or uncertified fresh submission fails the public checker.
Freshness separates the allocated envelope from all previously published packets. -/
theorem departureTraffic_forbidden
    (execution : (application setup leaks).Execution) (watcher who : Player)
    (sound : ((runtime setup).packetEvidence leaks).Sound execution)
    (binding : execution.application.BindingInvariant)
    (serials : execution.network.SerialsBeforeNext)
    (submission : WitnessedSubmission (graph setup))
    (departure : let state := (application setup leaks).submit execution.application who submission
      let packet := submission.emit state who (execution.network.known who)
      (application setup leaks).handle state
          ⟨(who, execution.network.nextSerial who), packet⟩ = none ∨
        certifiedOpening packet = false) :
    permittedTraffic setup leaks watcher
      ⟨execution.application.publicView, execution.network.ledger,
        ⟨(who, execution.network.nextSerial who), submission.emit
          ((application setup leaks).submit execution.application who submission) who
            (execution.network.known who)⟩⟩ = false := by
  cases verdict : permittedTraffic setup leaks watcher _ with
  | false => rfl
  | true =>
      obtain ⟨_ordinary, published | opening⟩ :=
        (permittedTraffic_iff setup leaks watcher _).mp verdict
      · exact (serials.next_unpublished who published).elim
      · obtain ⟨⟨next, accepted⟩, certified⟩ := openingTraffic_accepted setup leaks execution who
          sound binding submission opening
        rcases departure with rejected | malformed
        · rw [rejected] at accepted
          contradiction
        · rw [malformed] at certified
          contradiction

end Vegas
