/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceEnforcement
import Vegas.Pending.ReactivePacketEvidence
import Vegas.Pending.EventPublicState
import Vegas.Pending.ReactiveRevealTranscript
import Interaction.ReactiveAuditCollection

/-! # Public traffic conformance for the revelation service

The checker reads the authenticated transmission phase, broadcaster and prior
ledger. A fresh ordinary transmission must be a certified opening of a ready,
timely resolution; no service turn is consulted. Previously published packets may be replayed.
The reporting player transmits nothing on compliant executions; every one of
its transmissions is therefore outside this source implementation.

Certificate validity is a theorem of the existing ideal evidence mechanism,
not a hidden value read by the checker. Authentic observation and terminal
collection remain separate service obligations.
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
  match record.input.envelope.payload.call with
  | .opening event candidate raw =>
      record.observation.EventReady event ∧
      (match record.observation.activatedAt event with
        | none => False
        | some entered => record.observation.clock - entered < (runtime setup).deadline event) ∧
      record.input.envelope.payload.evidence = some ⟨candidate, raw⟩ ∧
      (match nodeView (graph setup) event with
        | .resolve owner payload binding _ _ _ =>
            record.input.broadcaster = owner ∧ record.input.envelope.sender = owner ∧
            candidate.1 = owner ∧ record.observation.accepted binding.field = some candidate ∧
            raw.ty = payload
        | .bind .. | .sample .. => False)
  | .commitment .. | .withhold .. | .malformed .. => False

open Classical in
/-- The verdict uses the broadcaster, so rebroadcasting does not assign a new
violation to the original envelope author. -/
def permittedTraffic (watcher : Player)
    (record : (application setup leaks).TrafficRecord) : Bool :=
  decide (record.input.broadcaster ≠ watcher ∧
    (record.input.envelope.id ∈ record.ledger.map Message.id ∨ openingTraffic setup leaks record))

theorem permittedTraffic_iff (watcher : Player)
    (record : (application setup leaks).TrafficRecord) :
    permittedTraffic setup leaks watcher record = true ↔
      record.input.broadcaster ≠ watcher ∧
        (record.input.envelope.id ∈ record.ledger.map Message.id ∨
          openingTraffic setup leaks record) := by
  classical
  simp only [permittedTraffic, decide_eq_true_eq]

theorem permittedTraffic_reporter (watcher : Player)
    (record : (application setup leaks).TrafficRecord)
    (authored : record.input.broadcaster = watcher) :
    permittedTraffic setup leaks watcher record = false := by
  classical
  simp only [permittedTraffic, authored, ne_eq, not_true_eq_false, false_and, decide_false]

theorem permittedTraffic_published (watcher : Player)
    (record : (application setup leaks).TrafficRecord)
    (ordinary : record.input.broadcaster ≠ watcher)
    (published : record.input.envelope.id ∈ record.ledger.map Message.id) :
    permittedTraffic setup leaks watcher record = true :=
  (permittedTraffic_iff setup leaks watcher record).mpr ⟨ordinary, Or.inl published⟩

/-- A canonical actual opening passes the public checker. Its value occurs only
inside the certificate and transmitted packet, never as private checker input. -/
theorem permittedTraffic_opening (watcher owner : Player) (ordinary : owner ≠ watcher)
    (state : EventGraphRuntime.State (graph setup))
    (ledger : List (Message Player (WitnessedPacket (graph setup))))
    (event : (graph setup).EventId) (payload : L.Ty)
    (binding : FieldRef (graph setup).layout (.binding owner payload))
    (checks : List (GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (graph setup) event =
      .resolve owner payload binding checks outputEq codeEq)
    (candidate : Handle (graph setup)) (raw : Raw L) (serial : Nat)
    (ready : state.config.cut.Ready event)
    (timely : state.WithinDeadline (runtime setup) event)
    (owned : candidate.1 = owner)
    (accepted : state.accepted binding.field = some candidate)
    (typed : raw.ty = payload) :
    permittedTraffic setup leaks watcher
      ⟨state.publicView, ledger,
        ⟨owner, ⟨(owner, serial), ⟨.opening event candidate raw, some ⟨candidate, raw⟩⟩⟩⟩⟩ =
          true := by
  apply (permittedTraffic_iff setup leaks watcher _).mpr
  refine ⟨ordinary, Or.inr ?_⟩
  change state.publicView.EventReady event ∧ state.WithinDeadline (runtime setup) event ∧ _ ∧ _
  refine ⟨(state.publicView_eventReady event).mpr ready, timely, rfl, ?_⟩
  rw [node]
  exact ⟨rfl, rfl, owned, accepted, typed⟩

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
        ⟨who, ⟨(who, execution.network.nextSerial who), submission.emit
          ((application setup leaks).submit execution.application who submission) who
            (execution.network.known who)⟩⟩⟩) :
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
          ⟨.opening event candidate raw, some ⟨candidate, raw⟩⟩ := by
        change (⟨(submission.emit execution.application who (execution.network.known who)).call,
          (submission.emit execution.application who (execution.network.known who)).evidence⟩ :
            WitnessedPacket (graph setup)) = _
        rw [WitnessedSubmission.emit_call, packet, carried]
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
          exact ⟨_, handle_opening_eq (runtime setup) execution.application _ event candidate
            who payload ref checks outputEq codeEq node actualReady timely rfl
            owned associated value valid stored result resolved⟩

/-- Every rejected or uncertified fresh submission fails the public checker.
Freshness prevents presenting the new envelope as an already published replay. -/
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
        ⟨who, ⟨(who, execution.network.nextSerial who), submission.emit
          ((application setup leaks).submit execution.application who submission) who
            (execution.network.known who)⟩⟩⟩ = false := by
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

/-- Semantic certificate normalization preserves the actual checked traffic,
including when the chosen request forwards an earlier certificate. -/
theorem normalized_opening_traffic
    (execution : (application setup leaks).Execution) (watcher owner : Player)
    (ordinary : owner ≠ watcher) (remaining : Nat)
    (recalled : execution.InputRecall (application setup leaks))
    (event : (graph setup).EventId) (payload : L.Ty)
    (binding : FieldRef (graph setup).layout (.binding owner payload))
    (checks : List (GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (graph setup) event =
      .resolve owner payload binding checks outputEq codeEq)
    (candidate : Handle (graph setup)) (value : L.Val payload)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline (runtime setup) event)
    (owned : candidate.1 = owner)
    (accepted : execution.application.accepted binding.field = some candidate)
    (fixed : execution.application.candidates.lookup candidate = .openable ⟨payload, value⟩) :
    let response := ((runtime setup).reactiveNormalization leaks).action owner
      (execution.recall owner) (execution.observe (application setup leaks) owner)
      ((runtime setup).canonicalRevealResponse leaks event candidate ⟨payload, value⟩ true)
    ∀ record ∈ (application setup leaks).trafficStep
      (some ⟨remaining, some owner, execution⟩)
      (some ⟨remaining, none, execution.respond (application setup leaks) owner response⟩),
      permittedTraffic setup leaks watcher record = true := by
  intro response record member
  have network := (runtime setup).normalized_opening_network leaks execution owner event
    candidate ⟨payload, value⟩ recalled owned fixed
  change _ = (execution.network.submit owner _).2 at network
  change record ∈ ((execution.respond (application setup leaks) owner response).network.inputs.drop
    execution.network.inputs.length).map _ at member
  rw [network] at member
  simp only [MessageNetwork.submit, List.drop_left, List.map_cons, List.map_nil,
    List.mem_singleton] at member
  subst record
  exact permittedTraffic_opening setup leaks watcher owner ordinary execution.application
    execution.network.ledger event payload binding checks outputEq codeEq node candidate
    ⟨payload, value⟩ (execution.network.nextSerial owner) ready timely owned accepted rfl

/-- Every opening returned by the existing owner-local decoder emits allowed
traffic at a ready, timely opportunity. No source policy is assumed. -/
theorem decoded_opening_traffic
    (execution : (application setup leaks).Execution) (watcher who : Player)
    (ordinary : who ≠ watcher) (remaining : Nat)
    (recalled : execution.InputRecall (application setup leaks))
    (binding : execution.application.BindingInvariant)
    (timely : ∀ event, execution.application.config.cut.Ready event →
      execution.application.WithinDeadline (runtime setup) event)
    (response : (application setup leaks).Action)
    (selected : opening? setup leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) = some response) :
    ∀ record ∈ (application setup leaks).trafficStep
      (some ⟨remaining, some who, execution⟩)
      (some ⟨remaining, none, execution.respond (application setup leaks) who response⟩),
      permittedTraffic setup leaks watcher record = true := by
  unfold opening? at selected
  obtain ⟨event, serving, selected⟩ := Option.bind_eq_some_iff.mp selected
  have ready : execution.application.config.cut.Ready event :=
    (execution.application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ who event serving).1
  split at selected
  · cases selected
  · rename_i actor
    have ownedEvent : (graph setup).actor? event = some who := not_ne_iff.mp actor
    cases node : nodeView (graph setup) event with
    | bind | sample => simp only [node] at selected; cases selected
    | resolve owner payload ref checks outputEq codeEq =>
        have nodeActor := congrArg EventCode.actor codeEq
        rw [EventCode.actor_cast outputEq ((graph setup).nodes event)] at nodeActor
        have ownerEq : owner = who := Option.some.inj (nodeActor.symm.trans ownedEvent)
        subst owner
        simp only [node] at selected
        cases resolved : EventCode.resolveOutput? ref checks true
            (execution.observe (application setup leaks) who).application.observation.store with
        | none => simp only [resolved] at selected; cases selected
        | some result =>
            cases result with
            | failure => simp only [resolved] at selected; cases selected
            | success value =>
                simp only [resolved] at selected
                obtain ⟨candidate, accepted, selected⟩ := Option.bind_eq_some_iff.mp selected
                change execution.application.accepted ref.field = some candidate at accepted
                split at selected
                · cases selected
                · rename_i owner
                  have owned : candidate.1 = who := not_ne_iff.mp owner
                  have stored : ref.get? execution.application.config.store =
                      some (.success value) := by
                    change EventCode.resolveOutput? ref checks true
                      ((graph setup).playerStore who execution.application.config.store) = _
                        at resolved
                    rw [EventCode.resolveOutput?_playerStore] at resolved
                    exact EventCode.binding_success_of_resolve_success ref checks true _ value
                      resolved
                  obtain ⟨expected, associated, _expectedOwner, fixed⟩ :=
                    binding.success_provenance ref value stored
                  have same : expected = candidate :=
                    Option.some.inj (associated.symm.trans accepted)
                  subst expected
                  have responseEq := Option.some.inj selected
                  rw [← responseEq]
                  exact normalized_opening_traffic setup leaks execution watcher who ordinary
                    remaining recalled event payload ref checks outputEq codeEq node candidate value
                    ready (timely event ready) owned accepted fixed

variable [Fintype Player]

/-- All physical choices in an ordinary source opportunity have conforming
traffic. Silence and every published replay remain legal withholding aliases. -/
theorem ordinary_response_traffic (bounds : MessageBounds (graph setup))
    (execution : (application setup leaks).Execution) (watcher who : Player)
    (ordinary : who ≠ watcher) (remaining : Nat)
    (recalled : execution.InputRecall (application setup leaks))
    (binding : execution.application.BindingInvariant)
    (timely : ∀ event, execution.application.config.cut.Ready event →
      execution.application.WithinDeadline (runtime setup) event)
    (response : (application setup leaks).Action)
    (allowed : response ∈ ordinaryActions setup leaks bounds who (execution.recall who)
      (execution.observe (application setup leaks) who)) :
    ∀ record ∈ (application setup leaks).trafficStep
      (some ⟨remaining, some who, execution⟩)
      (some ⟨remaining, none, execution.respond (application setup leaks) who response⟩),
      permittedTraffic setup leaks watcher record = true := by
  rcases ordinary_response_cases setup leaks bounds who (execution.recall who)
    (execution.observe (application setup leaks) who) response allowed with
    silent | opening | replay
  · subst response
    simp only [(application setup leaks).trafficStep_silent, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true]
  · exact decoded_opening_traffic setup leaks execution watcher who ordinary remaining recalled
      binding timely response opening
  · obtain ⟨published, member, rfl⟩ := replay
    cases found : (execution.network.known who).find?
        (fun message => message.id = published.id) with
    | none =>
        simp only [ReactiveApplication.trafficStep, ReactiveApplication.Execution.respond,
          MessageNetwork.replay, found, List.drop_length, List.map_nil, List.not_mem_nil,
          IsEmpty.forall_iff, implies_true]
    | some message =>
        rw [(application setup leaks).trafficStep_replay execution remaining who published.id
          message found]
        intro record recorded
        cases List.mem_singleton.mp recorded
        apply permittedTraffic_published setup leaks watcher _ ordinary
        have identified : message.id = published.id := by
          have selected := List.find?_some found
          simpa only [decide_eq_true_eq] using selected
        rw [identified]
        exact List.mem_map.mpr ⟨published, member, rfl⟩

end Vegas
