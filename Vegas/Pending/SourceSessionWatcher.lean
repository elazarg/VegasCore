/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.SourceSessionAudit
import Interaction.ReactiveResponseNormalization
import Interaction.ReactiveRounds
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Bounded reporting by the native watcher

The watcher uses only possessed envelopes and the sealed public record. It
chooses one source player uniformly and reports a unary witness or a pair of
distinct signed identifiers against that player, requiring at most two
envelopes. Candidate selection uses the emitter's actual identifier lookup.
Partial observation and report delivery remain distinct service obligations.
-/

noncomputable section

namespace Vegas.SourceSession

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Normalize known evidence through the same lookup used when it is sent. -/
def reportCandidates (known : List (Message (Principal Player) (Packet graph))) :
    List (Message (Principal Player) (Packet graph)) :=
  reportMaterial known ((reportEnvelopes known).map Message.id)

/-- Prefer a unary witness; otherwise select one duplicate pair. Selection
does not depend on how many other owners' offenses are known. -/
def reportWitness (view : PublicView graph)
    (evidence : List (Message (Principal Player) (Packet graph))) (who : Player) :
    List (Message (Principal Player) (Packet graph)) :=
  match evidence.find? (fun message =>
      decide (message.sender = .player who) && !view.permitsPacket who message.payload) with
  | some message => [message]
  | none =>
      match evidence.find? (fun first => decide (first.sender = .player who) &&
          evidence.any (fun second => equivocation first second)) with
      | none => []
      | some first =>
          match evidence.find? (fun second => equivocation first second) with
          | none => []
          | some second => [first, second]

theorem reportWitness_length (view : PublicView graph)
    (evidence : List (Message (Principal Player) (Packet graph))) (who : Player) :
    (reportWitness view evidence who).length ≤ 2 := by
  unfold reportWitness
  split
  · simp
  · split
    · simp
    · split <;> simp

theorem reportWitness_subset (view : PublicView graph)
    (evidence : List (Message (Principal Player) (Packet graph))) (who : Player) :
    reportWitness view evidence who ⊆ evidence := by
  unfold reportWitness
  split
  · rename_i message found
    simpa using List.mem_of_find?_eq_some found
  · split
    · simp
    · rename_i first found
      split
      · simp
      · rename_i second paired
        intro message member
        rcases List.mem_cons.mp member with rfl | later
        · exact List.mem_of_find?_eq_some found
        · cases List.mem_singleton.mp later
          exact List.mem_of_find?_eq_some paired

/-- Any known offense against the selected owner yields a charged witness;
the reporter need not select the particular offense used to establish coverage. -/
theorem reportWitness_charged (view : PublicView graph)
    (evidence : List (Message (Principal Player) (Packet graph))) (who : Player)
    (bad : misconductCharge view evidence who = true) :
    misconductCharge view (reportWitness view evidence who) who = true := by
  unfold reportWitness
  split
  · rename_i message found
    have validated := List.find?_some found
    have checked := Bool.and_eq_true_iff.mp validated
    exact misconductCharge_of_unary view [message] who message (by simp)
      (of_decide_eq_true checked.1) (by simpa using checked.2)
  · rename_i absent
    split
    · rename_i pairsAbsent
      rcases Bool.or_eq_true_iff.mp bad with unary | pair
      · obtain ⟨message, present, checked⟩ := List.any_eq_true.mp unary
        exact ((List.find?_eq_none.mp absent) message present checked).elim
      · obtain ⟨first, present, checked⟩ := List.any_eq_true.mp pair
        exact ((List.find?_eq_none.mp pairsAbsent) first present checked).elim
    · rename_i first found
      have validated := List.find?_some found
      have checked := Bool.and_eq_true_iff.mp validated
      split
      · rename_i absentSecond
        obtain ⟨second, present, paired⟩ := List.any_eq_true.mp checked.2
        exact ((List.find?_eq_none.mp absentSecond) second present paired).elim
      · rename_i second paired
        exact misconductCharge_of_pair view [first, second] who first second
          (by simp) (by simp) (of_decide_eq_true checked.1) (List.find?_some paired)

theorem reportCandidates_lookup
    (known : List (Message (Principal Player) (Packet graph)))
    (message : Message (Principal Player) (Packet graph))
    (member : message ∈ reportCandidates known) :
    reportEnvelope? known message.id = some message := by
  obtain ⟨id, _, found⟩ := List.mem_filterMap.mp member
  have identified : message.id = id := by
    simpa [reportEnvelope?] using List.find?_some found
  simpa only [identified] using found

/-- Sending the selected identifiers materializes exactly the selected
signed bodies, including when knowledge contains repeated identifiers. -/
theorem reportWitness_material (view : PublicView graph)
    (known : List (Message (Principal Player) (Packet graph))) (who : Player) :
    reportMaterial known ((reportWitness view (reportCandidates known) who).map Message.id) =
      reportWitness view (reportCandidates known) who := by
  unfold reportWitness
  split
  · rename_i message found
    have lookup := reportCandidates_lookup known message (List.mem_of_find?_eq_some found)
    simp only [List.map_cons, List.map_nil, reportMaterial]
    simp [List.eraseDups_cons, lookup]
  · split
    · simp [reportMaterial]
    · rename_i first found
      split
      · simp [reportMaterial]
      · rename_i second paired
        have firstLookup := reportCandidates_lookup known first (List.mem_of_find?_eq_some found)
        have secondLookup := reportCandidates_lookup known second (List.mem_of_find?_eq_some paired)
        have validated := List.find?_some paired
        have different : first.id ≠ second.id :=
          (of_decide_eq_true (Bool.and_eq_true_iff.mp validated).1).2
        simp only [List.map_cons, List.map_nil, reportMaterial]
        simp [List.eraseDups_cons, firstLookup, secondLookup, Ne.symm different]

/-- The empty-player case sends an empty report. Otherwise the owner draw is
uniform and independent of the available evidence and source equilibrium. -/
def watcherReportLaw [Fintype Player] (view : PublicView graph)
    (known : List (Message (Principal Player) (Packet graph))) :
    PMF (List (MessageId (Principal Player))) := by
  classical
  exact if nonempty : Nonempty Player then
    letI := nonempty
    (PMF.uniformOfFintype Player).map fun who =>
      (reportWitness view (reportCandidates known) who).map Message.id
  else PMF.pure []

/-- Both the requested identifiers and their actual materialized report body
fit the two-envelope evidence budget. -/
theorem watcherReportLaw_bounded [Fintype Player] (view : PublicView graph)
    (known : List (Message (Principal Player) (Packet graph)))
    (ids : List (MessageId (Principal Player)))
    (supported : ids ∈ (watcherReportLaw view known).support) :
    ids.length ≤ 2 ∧ (reportMaterial known ids).length ≤ 2 := by
  classical
  unfold watcherReportLaw at supported
  split at supported
  · obtain ⟨who, _, rfl⟩ := (PMF.mem_support_map_iff ..).mp supported
    rw [reportWitness_material]
    simpa only [List.length_map] using
      And.intro (reportWitness_length view (reportCandidates known) who)
        (reportWitness_length view (reportCandidates known) who)
  · cases (PMF.mem_support_pure_iff _ _).mp supported
    simp [reportMaterial]

/-- Once an owner's offense is known, uniform owner selection reports a
genuine charged witness with probability at least one over the player count.
This is the selection bound; acceptance remains a service obligation. -/
theorem watcherReportLaw_charge_lower [Fintype Player] (view : PublicView graph)
    (known : List (Message (Principal Player) (Packet graph))) (who : Player)
    (bad : misconductCharge view (reportCandidates known) who = true) :
    (Fintype.card Player : ℝ)⁻¹ ≤
      ((watcherReportLaw view known).toOuterMeasure
        {ids | misconductCharge view (reportMaterial known ids) who = true}).toReal := by
  classical
  let : Nonempty Player := ⟨who⟩
  rw [watcherReportLaw, dite_eq_left (inferInstance : Nonempty Player),
    PMF.toOuterMeasure_map_apply]
  calc
    (Fintype.card Player : ℝ)⁻¹ =
        ((PMF.uniformOfFintype Player).toOuterMeasure {who}).toReal := by
      rw [PMF.toOuterMeasure_apply_singleton, toReal_uniformOfFintype_apply]
    _ ≤ _ := outerMeasure_toReal_mono _ (Set.singleton_subset_iff.mpr (by
      change misconductCharge view
        (reportMaterial known ((reportWitness view (reportCandidates known) who).map
          Message.id)) who = true
      rw [reportWitness_material]
      exact reportWitness_charged view (reportCandidates known) who bad))

def alreadyReported (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (past : List (application runtime leaks).PlayerEntry) : Bool :=
  past.any fun entry => entry.emitted.any fun message =>
    match message.payload with
    | .report _ token => token = some .reporting
    | .gameplay _ => false

/-- Report once in the live reporting window after sealing. Earlier
unauthorized report attempts do not suppress this genuine opportunity. -/
def watcherPolicy [Fintype Player] (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph)) :
    (application runtime leaks).Policy := fun past observed =>
  match observed.application with
  | .player .. => PMF.pure ⟨none⟩
  | .watcher view =>
      if view.status ≠ .running ∧ view.report.isNone ∧ view.timely runtime .reporting ∧
          alreadyReported runtime leaks past = false then
        (watcherReportLaw view
          (ReactiveApplication.ResponseMenu.knownPackets past observed)).map fun ids =>
            ⟨some (.report ids)⟩
      else PMF.pure ⟨none⟩

/-- At an actual reporting opportunity, private recall and the observed
message lists reconstruct exactly the evidence possessed by the watcher. -/
theorem watcherPolicy_observe [Fintype Player] (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (execution : (application runtime leaks).Execution)
    (valid : execution.InputRecall (application runtime leaks))
    (ready : execution.application.status ≠ .running ∧
      execution.application.report.isNone ∧
      execution.application.publicView.timely runtime .reporting ∧
      alreadyReported runtime leaks (execution.recall .watcher) = false) :
    watcherPolicy runtime leaks (execution.recall .watcher)
        (execution.observe (application runtime leaks) .watcher) =
      (watcherReportLaw execution.application.publicView
        (execution.network.known .watcher)).map fun ids => ⟨some (.report ids)⟩ := by
  have known := (application runtime leaks).known_from_recall execution .watcher valid
  change (if execution.application.status ≠ .running ∧ execution.application.report.isNone ∧
      execution.application.publicView.timely runtime .reporting ∧
      alreadyReported runtime leaks (execution.recall .watcher) = false then
    (watcherReportLaw execution.application.publicView
      ((application runtime leaks).outputs (execution.recall .watcher) ++
        execution.network.leaked .watcher ++ execution.network.ledger)).map fun ids =>
          (⟨some (.report ids)⟩ : (application runtime leaks).Action)
      else PMF.pure (⟨none⟩ : (application runtime leaks).Action)) = _
  rw [← known]
  simp [ready]

/-- Including the actual newly emitted watcher envelope in its live window
collects the offense carried by its materialized body. This uses the pending
lookup and accepting receipt, rather than a separate evidence-delivery draw. -/
theorem watcher_report_collects (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (execution : (application runtime leaks).Execution)
    (serials : execution.network.SerialsBeforeNext)
    (aligned : execution.network.ledger.length = execution.receipts.length)
    (closed : execution.application.status ≠ .running)
    (clear : execution.application.report.isNone = true)
    (timely : execution.application.timely runtime .reporting = true)
    (ids : List (MessageId (Principal Player))) (who : Player)
    (bad : misconductCharge execution.application.publicView
      (reportMaterial (execution.network.known .watcher) ids) who = true) :
    let final := (execution.respond (application runtime leaks) .watcher
      ⟨some (.report ids)⟩).includePending (application runtime leaks)
        (.watcher, execution.network.nextSerial .watcher)
    misconductCharge final.application.publicView
      (reportedEvidence final.network.ledger final.receipts) who = true := by
  let body := reportMaterial (execution.network.known .watcher) ids
  let id : MessageId (Principal Player) := (.watcher, execution.network.nextSerial .watcher)
  let message : Message (Principal Player) (application runtime leaks).Payload :=
    ⟨id, .report body (some .reporting)⟩
  have token : execution.application.tokenFor .reporting = some .reporting := by
    simp [State.tokenFor, closed, clear]
  have found : (execution.respond (application runtime leaks) .watcher
      ⟨some (.report ids)⟩).network.lookup id = some message := by
    change (execution.network.submit .watcher
      (emit (submit execution.application .watcher (.report ids)) .watcher
        (execution.network.known .watcher) (.report ids))).2.lookup id = some message
    simpa only [submit_watcher, emit, token] using
      serials.lookup_submit .watcher (.report body (some .reporting))
  have accepted : handle runtime execution.application message =
      some { execution.application.record .reporting id with
        report := some (body.map Message.id) } := by
    simp [handle, message, Message.sender, id, token, timely]
  dsimp only
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  rw [found]
  change misconductCharge ((handle runtime execution.application message).getD
    execution.application).publicView
      (reportedEvidence (execution.network.ledger ++ [message])
        (execution.receipts ++ [(id, (handle runtime execution.application message).isSome)]))
      who = true
  rw [accepted]
  change misconductCharge execution.application.publicView
    (reportedEvidence (execution.network.ledger ++ [message])
      (execution.receipts ++ [(id, true)])) who = true
  rw [reportedEvidence_append _ _ aligned]
  have material : acceptedReportEvidence message true = body := by
    simp [acceptedReportEvidence, message, Message.sender, id]
  rw [material]
  exact misconductCharge_mono _ who (List.subset_append_right _ _) bad

/-- At a genuine watcher input, immediate native inclusion of its report
collects each already-known owner's offense with probability at least `1/K`.
A general builder still needs its conditional reporting-delivery bound. -/
theorem watcher_invoke_inclusion_lower [Fintype Player] (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (players : Principal Player → (application runtime leaks).Policy)
    (policy : players .watcher = watcherPolicy runtime leaks)
    (execution : (application runtime leaks).Execution)
    (valid : execution.InputRecall (application runtime leaks))
    (serials : execution.network.SerialsBeforeNext)
    (aligned : execution.network.ledger.length = execution.receipts.length)
    (ready : execution.application.status ≠ .running ∧
      execution.application.report.isNone ∧
      execution.application.publicView.timely runtime .reporting ∧
      alreadyReported runtime leaks (execution.recall .watcher) = false)
    (who : Player) (bad : misconductCharge execution.application.publicView
      (reportCandidates (execution.network.known .watcher)) who = true) :
    (Fintype.card Player : ℝ)⁻¹ ≤
      ((((application runtime leaks).invoke players .watcher execution).map
        fun (sent : (application runtime leaks).Execution) =>
        sent.includePending (application runtime leaks)
          (.watcher, execution.network.nextSerial .watcher)).toOuterMeasure
          {final | misconductCharge final.application.publicView
            (reportedEvidence final.network.ledger final.receipts) who = true}).toReal := by
  rw [ReactiveApplication.invoke, policy,
    watcherPolicy_observe runtime leaks execution valid ready, PMF.map_comp,
    PMF.map_comp, PMF.toOuterMeasure_map_apply]
  refine (watcherReportLaw_charge_lower _ _ who bad).trans
    (outerMeasure_toReal_mono _ ?_)
  intro ids charged
  exact watcher_report_collects runtime leaks execution serials aligned
    ready.1 ready.2.1 ready.2.2.1 ids who charged

end Vegas.SourceSession
