/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealService
import Vegas.Pending.ReactiveOpeningConformance
import Vegas.Pending.ReactiveStateInvariant
import Vegas.Pending.ReactiveSelectionObservation

/-! # Evidence for departures from ordinary revelation responses

At a clean revelation checkpoint, known replays are already published and are
ordinary aliases of silence. Every other effective response is a fresh packet.
Its actual inclusion either rejects the call or exposes a static certificate
format violation. The hypotheses describe actual execution state and the local
opening decoder; no player optimality or detection rate is assumed.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup))

/-- No unobservable silence or old replay is misclassified as a punishable
departure. An excluded effective response necessarily allocates a fresh packet. -/
theorem extra_response_submission (execution : (application setup leaks).Execution)
    (owner : Player) (recall : execution.InputRecall (application setup leaks))
    (published : ∀ message ∈ execution.network.known owner,
      message.id ∈ execution.network.ledger.map Message.id)
    (response : (application setup leaks).Action)
    (effective : response ∈ (bounds.menu (runtime setup) leaks).actions owner
      (execution.recall owner) (execution.observe (application setup leaks) owner))
    (extra : response ∉ ordinaryActions setup leaks bounds owner (execution.recall owner)
      (execution.observe (application setup leaks) owner)) :
    ∃ submission, response = ⟨some (.submit submission)⟩ := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact (extra (silence_ordinary setup leaks bounds owner _ _)).elim
  | some transmission =>
      cases transmission with
      | submit submission => exact ⟨submission, rfl⟩
      | replay id =>
          have known := ((bounds.menu_mem (runtime setup) leaks owner _ _ _).mp effective).1
          have actual := (ReactiveApplication.SubmissionNormalization.replayKnown_iff
            (app := application setup leaks) execution owner recall id).mp known
          obtain ⟨message, member, identified⟩ := actual
          have onLedger := published message member
          obtain ⟨recorded, recordedMem, same⟩ := List.mem_map.mp onLedger
          have ordinary := published_replay_ordinary setup leaks bounds owner
            (execution.recall owner) (execution.observe (application setup leaks) owner)
            recorded recordedMem
          rw [same, identified] at ordinary
          exact (extra ordinary).elim

/-- Exhaustive packet classification at an actual ordinary checkpoint. The
canonical opening is identified by the existing local decoder; all remaining
effective responses produce attributable rejection or bad public format. -/
theorem extra_response_packet_cases (execution : (application setup leaks).Execution)
    (owner : Player) (recall : execution.InputRecall (application setup leaks))
    (published : ∀ message ∈ execution.network.known owner,
      message.id ∈ execution.network.ledger.map Message.id)
    (event : (graph setup).EventId) (payload : L.Ty)
    (binding : FieldRef (graph setup).layout (.binding owner payload))
    (checks : List (GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
    (ready : execution.application.config.cut.Ready event)
    (candidate : Handle (graph setup)) (raw : Raw L)
    (associated : execution.application.accepted binding.field = some candidate)
    (owned : candidate.1 = owner)
    (fixed : execution.application.candidates.lookup candidate = .openable raw)
    (selected : opening? setup leaks owner (execution.recall owner)
      (execution.observe (application setup leaks) owner) =
        some (((runtime setup).reactiveNormalization leaks).action owner
          (execution.recall owner) (execution.observe (application setup leaks) owner)
          ((runtime setup).canonicalRevealResponse leaks event candidate raw true)))
    (response : (application setup leaks).Action)
    (effective : response ∈ (bounds.menu (runtime setup) leaks).actions owner
      (execution.recall owner) (execution.observe (application setup leaks) owner))
    (extra : response ∉ ordinaryActions setup leaks bounds owner (execution.recall owner)
      (execution.observe (application setup leaks) owner)) :
    ∃ submission, response = ⟨some (.submit submission)⟩ ∧
      let state := (application setup leaks).submit execution.application owner submission
      let packet := submission.emit state owner (execution.network.known owner)
      (application setup leaks).handle state
          ⟨(owner, execution.network.nextSerial owner), packet⟩ = none ∨
        certifiedOpening packet = false := by
  obtain ⟨submission, rfl⟩ := extra_response_submission setup leaks bounds execution owner
    recall published response effective extra
  refine ⟨submission, rfl, ?_⟩
  dsimp only
  by_cases addressed : submission.call.packet.event? (graph setup) = some event
  · rcases (runtime setup).current_opening_submission_cases leaks execution.application owner
      event payload binding checks outputEq codeEq node candidate raw associated owned fixed
      (execution.network.known owner) submission (execution.network.nextSerial owner) addressed
      with canonical | rejected | malformed
    · have known : ReactiveApplication.ResponseMenu.knownPackets
          (execution.recall owner) (execution.observe (application setup leaks) owner) =
          execution.network.known owner :=
        ((application setup leaks).known_from_recall execution owner recall).symm
      have normal := ((bounds.menu_mem (runtime setup) leaks owner _ _ _).mp effective).2
      have equivalent : ((runtime setup).reactiveNormalization leaks).action owner
          (execution.recall owner) (execution.observe (application setup leaks) owner)
          ⟨some (.submit submission)⟩ =
        ((runtime setup).reactiveNormalization leaks).action owner
          (execution.recall owner) (execution.observe (application setup leaks) owner)
          ((runtime setup).canonicalRevealResponse leaks event candidate raw true) := by
        change (⟨some (.submit (submission.normalizeReactive owner _ _))⟩ :
            (application setup leaks).Action) = ⟨some (.submit _)⟩
        rw [known]
        exact congrArg (fun material : WitnessedSubmission (graph setup) =>
          (⟨some (.submit material)⟩ : (application setup leaks).Action)) canonical
      have isOpening : opening? setup leaks owner (execution.recall owner)
          (execution.observe (application setup leaks) owner) =
          some ⟨some (.submit submission)⟩ := by
        rw [selected, ← equivalent, normal]
      exact (extra (opening_ordinary setup leaks bounds owner _ _ _ isOpening effective)).elim
    · exact Or.inl rejected
    · exact Or.inr malformed
  · refine Or.inl ?_
    have preserved := (runtime setup).reactive_respond_application leaks execution owner
      ⟨some (.submit submission)⟩ |>.1
    have stillReady :
        ((application setup leaks).submit execution.application owner submission).config.cut.Ready
          event := by
      change (execution.respond (application setup leaks) owner
        ⟨some (.submit submission)⟩).application.config.cut.Ready event
      rw [preserved]
      exact ready
    exact (runtime setup).handle_eq_none_of_other_event_ready_public
      setup.eventGraph.sequentialize_barrierOrdered _ event (by rw [outputEq]; trivial)
      stillReady ⟨(owner, execution.network.nextSerial owner), submission.call.packet⟩ addressed

omit [Fintype Player] in
/-- Public evidence attributable to this author. Receipt evidence remembers the
phase of actual rejection; ledger evidence covers accepted bad-format calls. -/
def departureEvidence (owner : Player) (execution : (application setup leaks).Execution) : Prop :=
  (∃ id, id.1 = owner ∧ (id, false) ∈ execution.receipts) ∨
    ledgerViolation owner certifiedOpening execution.network.ledger = true

omit [Fintype Player] in
theorem departureEvidence_persistent (owner : Player)
    (players : Player → (application setup leaks).Policy) :
    (application setup leaks).PolicyInvariant players (departureEvidence setup leaks owner) where
  respond execution who response evidence supported := by
    rcases evidence with ⟨id, authored, rejected⟩ | malformed
    · exact Or.inl ⟨id, authored, ((application setup leaks).receipt_policyInvariant players
        (id, false)).respond execution who response rejected supported⟩
    · exact Or.inr ((application setup leaks).ledgerViolation_respond owner certifiedOpening
        execution who response malformed)
  environment execution next command evidence reached := by
    rcases evidence with ⟨id, authored, rejected⟩ | malformed
    · exact Or.inl ⟨id, authored, ((application setup leaks).receipt_policyInvariant players
        (id, false)).environment execution next command rejected reached⟩
    · exact Or.inr ((application setup leaks).ledgerViolation_environment owner certifiedOpening
        execution next command malformed reached)

omit [Fintype Player] in
/-- Actual inclusion records evidence in both arms of the packet classifier. -/
theorem inclusion_records_departure (owner : Player)
    (execution : (application setup leaks).Execution) (id : MessageId Player)
    (message : Message Player (WitnessedPacket (graph setup)))
    (found : execution.network.lookup id = some message) (identified : message.id = id)
    (authored : id.1 = owner)
    (departure : (application setup leaks).handle execution.application message = none ∨
      certifiedOpening message.payload = false) :
    departureEvidence setup leaks owner
      (execution.includePending (application setup leaks) id) := by
  rcases departure with rejected | malformed
  · refine Or.inl ⟨id, authored, ?_⟩
    simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, rejected, Option.isSome_none]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · apply Or.inr
    exact (application setup leaks).ledgerViolation_includePending owner certifiedOpening
      execution id message found (by change message.id.1 = owner; rw [identified, authored])
      malformed

omit [Fintype Player] in
/-- Sampling followed by the fixed reporter supplies the corresponding
evidence bound. Later responses and scheduler choices remain arbitrary. -/
theorem report_departure_lower (owner watcher : Player)
    (players : Player → (application setup leaks).Policy)
    (reporter : players watcher = (application setup leaks).reportFirstUnpublished)
    (execution : (application setup leaks).Execution) (id : MessageId Player)
    (message : Message Player (WitnessedPacket (graph setup)))
    (found : execution.network.lookup id = some message) (identified : message.id = id)
    (authored : id.1 = owner) (foreign : id.1 ≠ watcher)
    (unknown : (execution.network.known watcher).any (fun packet => packet.id = id) = false)
    (fresh : id ∉ execution.network.ledger.map Message.id)
    (oldPublished : ∀ packet ∈ execution.network.leaked watcher,
      packet.id ∈ execution.network.ledger.map Message.id)
    (uniquePending : ∀ packet ∈ execution.network.pending,
      packet.id ∉ execution.network.ledger.map Message.id → packet.id = id)
    (departure : (application setup leaks).handle execution.application message = none ∨
      certifiedOpening message.payload = false)
    (continuation : (application setup leaks).Scheduler) (count : Nat) :
    (leaks watcher execution.network.pending).probOf {selected | id ∈ selected} ≤
      (((application setup leaks).reportInclusion players watcher execution).bind
        ((application setup leaks).runRounds continuation players count)).probOf
          {final | departureEvidence setup leaks owner final} := by
  classical
  have reports : ∀ observed ∈ (execution.environmentStep (application setup leaks)
      (.activate watcher)).support,
      message ∈ (observed.observe (application setup leaks) watcher).messages.leaked →
        players watcher (observed.recall watcher)
          (observed.observe (application setup leaks) watcher) =
            FinDist.pure ⟨some (.replay id)⟩ := by
    intro observed reached seen
    rw [reporter]
    exact (application setup leaks).reportFirstUnpublished_after_activation execution watcher
      id message identified fresh oldPublished uniquePending observed reached seen
  rcases departure with rejected | malformed
  · have detection := (application setup leaks).sampling_rejected_receipt_lower players watcher
      execution id message found foreign unknown fresh reports rejected continuation count
    apply detection.trans
    rw [← FinDist.expect_indicator_eq_probOf, ← FinDist.expect_indicator_eq_probOf]
    apply FinDist.expect_mono
    intro final _
    change (if (id, false) ∈ final.receipts then (1 : ℝ) else 0) ≤
      if departureEvidence setup leaks owner final then 1 else 0
    split
    · rename_i present
      have evidence : departureEvidence setup leaks owner final := Or.inl ⟨id, authored, present⟩
      simp only [evidence, ↓reduceIte, le_refl]
    · split <;> norm_num
  · have detection := (application setup leaks).sampling_ledger_violation_lower players watcher
      owner certifiedOpening execution id message found foreign unknown fresh
      (by change message.id.1 = owner; rw [identified, authored]) malformed reports
      continuation count
    apply detection.trans
    rw [← FinDist.expect_indicator_eq_probOf, ← FinDist.expect_indicator_eq_probOf]
    apply FinDist.expect_mono
    intro final _
    change (if ledgerViolation owner certifiedOpening final.network.ledger = true then
      (1 : ℝ) else 0) ≤ if departureEvidence setup leaks owner final then 1 else 0
    split
    · rename_i present
      have evidence : departureEvidence setup leaks owner final := Or.inr present
      simp only [evidence, ↓reduceIte, le_refl]
    · split <;> norm_num


omit [Fintype Player] in
/-- A clean pending pool plus one newly authored packet satisfies the fixed
reporter's premises, even when published replay copies remain in the pool.
The snapshot may include intervening service bookkeeping such as a reserved
wait; its exact submitted network is the only required correspondence. -/
theorem fresh_submission_report_lower (owner watcher : Player) (different : owner ≠ watcher)
    (players : Player → (application setup leaks).Policy)
    (reporter : players watcher = (application setup leaks).reportFirstUnpublished)
    (before snapshot : (application setup leaks).Execution)
    (packet : WitnessedPacket (graph setup))
    (network : snapshot.network = (before.network.submit owner packet).2)
    (serials : before.network.SerialsBeforeNext)
    (pendingPublished : ∀ message ∈ before.network.pending,
      message.id ∈ before.network.ledger.map Message.id)
    (knownPublished : ∀ message ∈ before.network.known watcher,
      message.id ∈ before.network.ledger.map Message.id)
    (departure : (application setup leaks).handle snapshot.application
        ⟨(owner, before.network.nextSerial owner), packet⟩ = none ∨
      certifiedOpening packet = false)
    (continuation : (application setup leaks).Scheduler) (count : Nat) :
    (leaks watcher snapshot.network.pending).probOf
        {selected | (owner, before.network.nextSerial owner) ∈ selected} ≤
      (((application setup leaks).reportInclusion players watcher snapshot).bind
        ((application setup leaks).runRounds continuation players count)).probOf
          {final | departureEvidence setup leaks owner final} := by
  let id := (owner, before.network.nextSerial owner)
  have found : snapshot.network.lookup id = some ⟨id, packet⟩ := by
    rw [network]
    exact serials.lookup_submit owner packet
  have ledger : snapshot.network.ledger = before.network.ledger := by rw [network]; rfl
  have fresh : id ∉ snapshot.network.ledger.map Message.id := by
    rw [ledger]
    exact serials.next_unpublished owner
  have known : snapshot.network.known watcher = before.network.known watcher := by
    rw [network]
    simp only [MessageNetwork.known, MessageNetwork.submit, List.filterMap_append,
      List.filterMap_cons, List.filterMap_nil, different, ↓reduceIte, List.append_nil]
  have unknown : (snapshot.network.known watcher).any (fun message => message.id = id) =
      false := by
    rw [known]
    cases selected : (before.network.known watcher).any (fun message => message.id = id) with
    | false => rfl
    | true =>
        obtain ⟨message, member, same⟩ := List.any_eq_true.mp selected
        have published := knownPublished message member
        have identified : message.id = id := of_decide_eq_true same
        rw [identified, ← ledger] at published
        exact (fresh published).elim
  have oldPublished : ∀ message ∈ snapshot.network.leaked watcher,
      message.id ∈ snapshot.network.ledger.map Message.id := by
    intro message member
    have retained : message ∈ snapshot.network.known watcher := by
      simp only [MessageNetwork.known, List.mem_append]
      exact Or.inl (Or.inr member)
    rw [known] at retained
    rw [ledger]
    exact knownPublished message retained
  have uniquePending : ∀ message ∈ snapshot.network.pending,
      message.id ∉ snapshot.network.ledger.map Message.id → message.id = id := by
    intro message member unpublished
    rw [network] at member
    change message ∈ before.network.pending ++ [⟨id, packet⟩] at member
    rcases List.mem_append.mp member with old | freshPacket
    · exact (unpublished (ledger ▸ pendingPublished message old)).elim
    · cases List.mem_singleton.mp freshPacket
      rfl
  exact report_departure_lower setup leaks owner watcher players reporter snapshot id
    ⟨id, packet⟩ found rfl rfl different unknown fresh oldPublished uniquePending
    departure continuation count
omit [Fintype Player] in
private theorem evidence_after_report (owner watcher : Player)
    (players : Player → (application setup leaks).Policy)
    (execution final : (application setup leaks).Execution)
    (evidence : departureEvidence setup leaks owner execution)
    (continuation : (application setup leaks).Scheduler) (count : Nat)
    (reached : final ∈ (((application setup leaks).reportInclusion players watcher execution).bind
      ((application setup leaks).runRounds continuation players count)).support) :
    departureEvidence setup leaks owner final := by
  have invariant := departureEvidence_persistent setup leaks owner players
  obtain ⟨reported, report, rest⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  obtain ⟨observed, activate, included⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ report)
  exact invariant.runRounds continuation count reported final
    (invariant.dispatch _ observed reported
      (invariant.dispatch (.activate watcher) execution observed evidence activate) included) rest

omit [Fintype Player] in
private theorem nonmatching_submission_wait (owner : Player)
    (execution : (application setup leaks).Execution) (event : (graph setup).EventId)
    (submission : WitnessedSubmission (graph setup))
    (pendingPublished : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id)
    (different : submission.call.packet.event? (graph setup) ≠ some event) :
    (runtime setup).reactiveLatest leaks event owner
      ((execution.respond (application setup leaks) owner
        ⟨some (.submit submission)⟩).observeEnvironment (application setup leaks)) = .wait := by
  let submitted := execution.respond (application setup leaks) owner ⟨some (.submit submission)⟩
  have absent : submitted.network.pending.reverse.find? (fun message =>
      message.sender = owner ∧ message.payload.call.event? (graph setup) = some event ∧
        message.id ∉ submitted.network.ledger.map Message.id) = none := by
    apply List.find?_eq_none.mpr
    intro message member
    have pending := List.mem_reverse.mp member
    change message ∈ execution.network.pending ++ [_] at pending
    rcases List.mem_append.mp pending with old | fresh
    · have spent := pendingPublished message old
      change message.id ∈ submitted.network.ledger.map Message.id at spent
      simp only [spent, not_true_eq_false, and_false, decide_false, Bool.false_eq_true,
        not_false_eq_true]
    · cases List.mem_singleton.mp fresh
      change ¬ decide (owner = owner ∧ submission.call.packet.event? (graph setup) = some event ∧
        (owner, execution.network.nextSerial owner) ∉
          submitted.network.ledger.map Message.id) = true
      simp only [different, false_and, and_false, decide_false, Bool.false_eq_true,
        not_false_eq_true]
  change (runtime setup).reactiveLatest leaks event owner
    (submitted.observeEnvironment (application setup leaks)) = .wait
  simp only [reactiveLatest, ReactiveApplication.Execution.observeEnvironment,
    MessageNetwork.publicView, ReactiveApplication.EnvironmentView.Unpublished, absent]

omit [Fintype Player] in
/-- The actual reserved inclusion followed by the fixed watcher collects
departure evidence with at least the fresh packet's sampling probability.
Current-address packets are included immediately; other packets remain for
passive observation. Subsequent responses and scheduling are unrestricted. -/
theorem reserved_report_departure_lower (owner watcher : Player) (different : owner ≠ watcher)
    (players : Player → (application setup leaks).Policy)
    (reporter : players watcher = (application setup leaks).reportFirstUnpublished)
    (before : (application setup leaks).Execution) (event : (graph setup).EventId)
    (submission : WitnessedSubmission (graph setup))
    (serials : before.network.SerialsBeforeNext)
    (pendingPublished : ∀ message ∈ before.network.pending,
      message.id ∈ before.network.ledger.map Message.id)
    (knownPublished : ∀ message ∈ before.network.known watcher,
      message.id ∈ before.network.ledger.map Message.id)
    (departure :
      let state := (application setup leaks).submit before.application owner submission
      let packet := submission.emit state owner (before.network.known owner)
      (application setup leaks).handle state
          ⟨(owner, before.network.nextSerial owner), packet⟩ = none ∨
        certifiedOpening packet = false)
    (continuation : (application setup leaks).Scheduler) (count : Nat) :
    let submitted := before.respond (application setup leaks) owner ⟨some (.submit submission)⟩
    (leaks watcher submitted.network.pending).probOf
        {selected | (owner, before.network.nextSerial owner) ∈ selected} ≤
      ((((runtime setup).interactionStep leaks players ((runtime setup).reportNetwork leaks watcher)
          (.includeLatest event owner) submitted).bind
        ((application setup leaks).reportInclusion players watcher)).bind
          ((application setup leaks).runRounds continuation players count)).probOf
            {final | departureEvidence setup leaks owner final} := by
  classical
  let app := application setup leaks
  let submitted := before.respond app owner ⟨some (.submit submission)⟩
  let id := (owner, before.network.nextSerial owner)
  let packet := submission.emit submitted.application owner (before.network.known owner)
  change (leaks watcher submitted.network.pending).probOf {selected | id ∈ selected} ≤
    ((((runtime setup).interactionStep leaks players ((runtime setup).reportNetwork leaks watcher)
      (.includeLatest event owner) submitted).bind (app.reportInclusion players watcher)).bind
        (app.runRounds continuation players count)).probOf _
  rw [(runtime setup).interaction_includeLatest_environment]
  by_cases addressed : submission.call.packet.event? (graph setup) = some event
  · rw [(runtime setup).reactiveLatest_after_submit leaks owner event before serials submission
      addressed]
    simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
      FinDist.pure_bind]
    have found : submitted.network.lookup id = some ⟨id, packet⟩ :=
      serials.lookup_submit owner packet
    have evidence := inclusion_records_departure setup leaks owner submitted id ⟨id, packet⟩
      found rfl rfl departure
    let recorded : app.Execution := { submitted.includePending app id with
      environmentRecall := submitted.environmentRecall ++
        [⟨submitted.observeEnvironment app, .include id⟩] }
    have recordedEvidence : departureEvidence setup leaks owner recorded := evidence
    rw [← FinDist.expect_indicator_eq_probOf, ← FinDist.expect_indicator_eq_probOf]
    calc
      _ ≤ (leaks watcher submitted.network.pending).expect (fun _ => (1 : ℝ)) := by
        apply FinDist.expect_mono
        intro selected _
        change (if id ∈ selected then (1 : ℝ) else 0) ≤ 1
        split <;> norm_num
      _ = 1 := FinDist.expect_const ..
      _ = _ := by
        symm
        calc
          _ = (((app.reportInclusion players watcher _).bind
              (app.runRounds continuation players count))).expect (fun _ => (1 : ℝ)) := by
            apply FinDist.expect_congr
            intro final reached
            have detected := evidence_after_report setup leaks owner watcher players recorded final
              recordedEvidence continuation count reached
            change (if departureEvidence setup leaks owner final then (1 : ℝ) else 0) = 1
            simp only [detected, ↓reduceIte]
          _ = 1 := FinDist.expect_const ..
  · rw [nonmatching_submission_wait setup leaks owner before event submission pendingPublished
      addressed]
    simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
      FinDist.pure_bind]
    let waited : app.Execution := { submitted with
      environmentRecall := submitted.environmentRecall ++
        [⟨submitted.observeEnvironment app, .wait⟩] }
    exact fresh_submission_report_lower setup leaks owner watcher different players reporter
      before waited packet rfl serials pendingPublished knownPublished departure continuation count

end Vegas
