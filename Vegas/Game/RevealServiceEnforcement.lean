/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealService
import Vegas.Game.ServiceSettledEvidence
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
    (owner : Player) (_inputRecall : execution.InputRecall (application setup leaks))
    (_published : ∀ message ∈ execution.network.known owner,
      message.id ∈ execution.network.ledger.map Message.id)
    (response : (application setup leaks).Action)
    (effective : response ∈ (bounds.menu (runtime setup) leaks).actions owner
      (execution.recall owner) (execution.observe (application setup leaks) owner))
    (extra : response ∉ ordinaryActions setup leaks bounds owner (execution.recall owner)
      (execution.observe (application setup leaks) owner)) :
    ∃ submission, response = ⟨some submission⟩ := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact (extra (silence_ordinary setup leaks bounds owner _ _)).elim
  | some submission => exact ⟨submission, rfl⟩

/-- Exhaustive packet classification at an actual ordinary checkpoint. The
canonical opening is identified by the existing local decoder; all remaining
effective responses produce attributable rejection or bad public format. -/
theorem extra_response_packet_cases (execution : (application setup leaks).Execution)
    (owner : Player) (inputRecall : execution.InputRecall (application setup leaks))
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
    ∃ submission, response = ⟨some submission⟩ ∧
      let state := (application setup leaks).submit execution.application owner submission
      let packet := submission.emit state owner (execution.network.known owner)
      (application setup leaks).handle state
          ⟨(owner, execution.network.nextSerial owner), packet⟩ = none ∨
        certifiedOpening packet = false := by
  obtain ⟨submission, rfl⟩ := extra_response_submission setup leaks bounds execution owner
    inputRecall published response effective extra
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
        ((application setup leaks).known_from_recall execution owner inputRecall).symm
      have normal := ((bounds.menu_mem (runtime setup) leaks owner _ _ _).mp effective).2
      have equivalent : ((runtime setup).reactiveNormalization leaks).action owner
          (execution.recall owner) (execution.observe (application setup leaks) owner)
          ⟨some submission⟩ =
        ((runtime setup).reactiveNormalization leaks).action owner
          (execution.recall owner) (execution.observe (application setup leaks) owner)
          ((runtime setup).canonicalRevealResponse leaks event candidate raw true) := by
        change (⟨some (submission.normalizeReactive owner _ _)⟩ :
            (application setup leaks).Action) = ⟨some _⟩
        rw [known]
        exact congrArg (fun material : WitnessedSubmission (graph setup) =>
          (⟨some material⟩ : (application setup leaks).Action)) canonical
      have isOpening : opening? setup leaks owner (execution.recall owner)
          (execution.observe (application setup leaks) owner) =
          some ⟨some submission⟩ := by
        rw [selected, ← equivalent, normal]
      exact (extra (opening_ordinary setup leaks bounds owner _ _ _ isOpening effective)).elim
    · exact Or.inl rejected
    · exact Or.inr malformed
  · refine Or.inl ?_
    have preserved := (runtime setup).reactive_respond_application leaks execution owner
      ⟨some submission⟩ |>.1
    have stillReady :
        ((application setup leaks).submit execution.application owner submission).config.cut.Ready
          event := by
      change (execution.respond (application setup leaks) owner
        ⟨some submission⟩).application.config.cut.Ready event
      rw [preserved]
      exact ready
    exact reactiveHandle_none ((runtime setup).handle_eq_none_of_other_event_ready_public
      setup.eventGraph.sequentialize_barrierOrdered _ event (by rw [outputEq]; trivial)
      stillReady ⟨(owner, execution.network.nextSerial owner), submission.call.packet⟩ addressed)

omit [Fintype Player] in
/-- The settlement charges `owner` when a packet it signed, on the contract's
ledger or in the watcher's report, is forbidden by the settled record. The
contract judges its own ledger. The watcher's report carries the signed packets
the watcher observed; it is included within the challenge window, which ends
before settlement. -/
def departureEvidence (watcher owner : Player)
    (execution : (application setup leaks).Execution) : Prop :=
  ∃ message, (message ∈ execution.network.ledger ∨ message ∈ execution.network.leaked watcher) ∧
    message.sender = owner ∧
    ((runtime setup).settledRecord leaks execution).permits message = false

omit [Fintype Player] in
/-- A mark that settlement will charge `owner`: a condemned packet it signed is
on the ledger or in the watcher's report. -/
def markedDeparture (watcher owner : Player)
    (execution : (application setup leaks).Execution) : Prop :=
  ∃ message, (message ∈ execution.network.ledger ∨ message ∈ execution.network.leaked watcher) ∧
    message.sender = owner ∧ CondemnedFacts setup leaks message execution

omit [Fintype Player] in
/-- A ledger entry stays on the ledger. -/
theorem ledger_policyInvariant (players : Player → (application setup leaks).Policy)
    (message : Message Player (WitnessedPacket (graph setup))) :
    (application setup leaks).PolicyInvariant players
      (fun execution => message ∈ execution.network.ledger) where
  respond execution who action published _ := by
    rw [(application setup leaks).respond_ledger]
    exact published
  environment execution next command published reached := by
    obtain ⟨_, _, effect⟩ := environmentStep_shape setup leaks execution next command reached
    rcases effect with ⟨_, ledgerEq, _⟩ | ⟨id, included, found, networkEq, _, _⟩
    · rw [ledgerEq]
      exact published
    · rw [networkEq, (includePending_found execution.network id included found).2.2]
      exact List.mem_append_left _ published

omit [Fintype Player] in
theorem markedDeparture_persistent (watcher owner : Player)
    (players : Player → (application setup leaks).Policy) :
    (application setup leaks).PolicyInvariant players
      (markedDeparture setup leaks watcher owner) where
  respond execution who action marked supported := by
    obtain ⟨message, place, authored, held⟩ := marked
    refine ⟨message, ?_, authored,
      (condemnedFacts_persistent message players).respond execution who action held supported⟩
    rcases place with published | observed
    · exact Or.inl ((ledger_policyInvariant setup leaks players message).respond execution who
        action published supported)
    · exact Or.inr (((application setup leaks).leaked_policyInvariant players watcher
        message).respond execution who action observed supported)
  environment execution next command marked reached := by
    obtain ⟨message, place, authored, held⟩ := marked
    refine ⟨message, ?_, authored,
      (condemnedFacts_persistent message players).environment execution next command held
        reached⟩
    rcases place with published | observed
    · exact Or.inl ((ledger_policyInvariant setup leaks players message).environment execution
        next command published reached)
    · exact Or.inr (((application setup leaks).leaked_policyInvariant players watcher
        message).environment execution next command observed reached)

omit [Fintype Player] in
/-- At a settlement that completed every event, a mark is a charge. -/
theorem markedDeparture_evidence (watcher owner : Player)
    (execution : (application setup leaks).Execution)
    (marked : markedDeparture setup leaks watcher owner execution)
    (terminal : execution.application.config.cut.Terminal) :
    departureEvidence setup leaks watcher owner execution := by
  obtain ⟨message, place, authored, facts, emitted, condemned⟩ := marked
  exact ⟨message, place, authored, condemned.forbidden facts terminal emitted⟩

omit [Fintype Player] in
private theorem nonmatching_submission_wait (owner : Player)
    (execution : (application setup leaks).Execution) (event : (graph setup).EventId)
    (submission : WitnessedSubmission (graph setup))
    (pendingPublished : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id)
    (different : submission.call.packet.event? (graph setup) ≠ some event) :
    (runtime setup).reactiveLatest leaks event owner
      ((execution.respond (application setup leaks) owner
        ⟨some submission⟩).observeEnvironment (application setup leaks)) = .wait := by
  let submitted := execution.respond (application setup leaks) owner ⟨some submission⟩
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
/-- The actual reserved inclusion followed by the watcher's observation marks a
departure with at least the fresh packet's sampling probability. A packet for
the current event is included at once and lands on the ledger; any other packet
stays pending for passive observation. Subsequent responses and scheduling are
unrestricted. -/
theorem reserved_observation_departure_lower (owner watcher : Player) (different : owner ≠ watcher)
    (players : Player → (application setup leaks).Policy)
    (before : (application setup leaks).Execution) (event : (graph setup).EventId)
    (submission : WitnessedSubmission (graph setup))
    (facts : SettledFacts setup leaks before)
    (sound : ((runtime setup).packetEvidence leaks).Sound before)
    (binding : before.application.BindingInvariant)
    (publications : ∀ event owner payload,
      (graph setup).outputLayout event ≠ .binding owner payload)
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
    let submitted := before.respond (application setup leaks) owner ⟨some submission⟩
    ((leaks watcher submitted.network.pending).toOuterMeasure
        {selected | (owner, before.network.nextSerial owner) ∈ selected}).toReal ≤
      (((((runtime setup).interactionStep leaks players
          ((runtime setup).idleNetwork leaks)
          (.includeLatest event owner) submitted).bind
        ((application setup leaks).observationRound players watcher)).bind
          ((application setup leaks).runRounds continuation players count)).toOuterMeasure
              {final | markedDeparture setup leaks watcher owner final}).toReal := by
  classical
  let app := application setup leaks
  let submitted := before.respond app owner ⟨some submission⟩
  let id := (owner, before.network.nextSerial owner)
  let packet := submission.emit submitted.application owner (before.network.known owner)
  let message : Message Player (WitnessedPacket (graph setup)) := ⟨id, packet⟩
  have serials := facts.serials
  have condemned : CondemnedFacts setup leaks message submitted :=
    ⟨settledFacts_respond before facts owner _,
      List.mem_append_right _ (List.mem_singleton_self _),
      condemned_of_unacceptable before facts sound binding publications owner submission
        departure⟩
  have persistent := markedDeparture_persistent setup leaks watcher owner players
  have heldPersistent := condemnedFacts_persistent message players
  change ((leaks watcher submitted.network.pending).toOuterMeasure
      {selected | id ∈ selected}).toReal ≤
    (((((runtime setup).interactionStep leaks players ((runtime setup).idleNetwork leaks)
      (.includeLatest event owner) submitted).bind (app.observationRound players watcher)).bind
        (app.runRounds continuation players count)).toOuterMeasure _).toReal
  rw [(runtime setup).interaction_includeLatest_environment]
  by_cases addressed : submission.call.packet.event? (graph setup) = some event
  · rw [(runtime setup).reactiveLatest_after_submit leaks owner event before serials submission
      addressed]
    let recorded : app.Execution := { submitted.includePending app id with
      environmentRecall := submitted.environmentRecall ++
        [⟨submitted.observeEnvironment app, .include id⟩] }
    have recordedMem : recorded ∈ (submitted.environmentStep app (.include id)).support := by
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
    have found : submitted.network.lookup id = some message :=
      serials.lookup_submit owner packet
    have marked : markedDeparture setup leaks watcher owner recorded := by
      refine ⟨message, Or.inl ?_, rfl,
        heldPersistent.environment submitted recorded (.include id) condemned recordedMem⟩
      change message ∈ (submitted.includePending app id).network.ledger
      rw [app.includePending_network, (includePending_found submitted.network id message
        found).2.2]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
      PMF.pure_bind]
    rw [← expect_indicator, ← expect_indicator]
    calc
      _ ≤ expect (leaks watcher submitted.network.pending) (fun _ => (1 : ℝ)) := by
        refine expect_mono ?_ (payoffIntegrable_ite_one_zero _ _) (payoffIntegrable_constant _ _)
        intro selected _
        split <;> norm_num
      _ = 1 := expect_constant ..
      _ = _ := by
        symm
        calc
          _ = expect (((app.observationRound players watcher recorded).bind
              (app.runRounds continuation players count))) (fun _ => (1 : ℝ)) := by
            apply expect_congr_on_support
            intro final reached
            obtain ⟨observed, round, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
            obtain ⟨activated, activation, waited⟩ :=
              Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ round)
            have detected := persistent.runRounds continuation count observed final
              (persistent.dispatch _ activated observed
                (persistent.dispatch _ recorded activated marked activation) waited) rest
            exact ite_eq_left detected
          _ = 1 := expect_constant ..
  · rw [nonmatching_submission_wait setup leaks owner before event submission pendingPublished
      addressed]
    let waited : app.Execution := { submitted with
      environmentRecall := submitted.environmentRecall ++
        [⟨submitted.observeEnvironment app, .wait⟩] }
    have waitedMem : waited ∈ (submitted.environmentStep app .wait).support := by
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
    have held : CondemnedFacts setup leaks message waited :=
      heldPersistent.environment submitted waited .wait condemned waitedMem
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
      PMF.pure_bind]
    have found : waited.network.lookup id = some message :=
      serials.lookup_submit owner packet
    have ledger : waited.network.ledger = before.network.ledger := rfl
    have fresh : id ∉ waited.network.ledger.map Message.id := by
      rw [ledger]
      exact serials.next_unpublished owner
    have known : waited.network.known watcher = before.network.known watcher := by
      change (before.network.submit owner packet).2.known watcher = _
      simp [MessageNetwork.known, MessageNetwork.submit, Message.sender, different]
    have unknown : (waited.network.known watcher).any (fun message => message.id = id) =
        false := by
      rw [known]
      cases selected : (before.network.known watcher).any (fun message => message.id = id) with
      | false => rfl
      | true =>
          obtain ⟨other, member, same⟩ := List.any_eq_true.mp selected
          have published := knownPublished other member
          have identified : other.id = id := of_decide_eq_true same
          rw [identified, ← ledger] at published
          exact (fresh published).elim
    have observed := app.sampling_observed_lower players watcher waited id message found
      different unknown fresh continuation count
    apply observed.trans
    rw [← expect_indicator, ← expect_indicator]
    refine expect_mono ?_ (payoffIntegrable_ite_one_zero _ _) (payoffIntegrable_ite_one_zero _ _)
    intro final reached
    simp only [Set.mem_ofPred_eq]
    split
    · rename_i seen
      obtain ⟨middle, round, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨activated, activation, idle⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ round)
      have heldFinal := heldPersistent.runRounds continuation count middle final
        (heldPersistent.dispatch _ activated middle
          (heldPersistent.dispatch _ waited activated held activation) idle) rest
      have marked : final ∈ {final | markedDeparture setup leaks watcher owner final} :=
        ⟨message, Or.inr seen, rfl, heldFinal⟩
      rw [ite_eq_left marked]
    · split <;> norm_num

end Vegas
