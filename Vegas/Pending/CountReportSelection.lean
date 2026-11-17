module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ThinnedCountCollection

@[expose] public section

/-! # Reporting the first observed count violation per sender -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Keep the first forbidden item of each sender in observation order. -/
def firstCountReports : List (CountEvidence graph) → List (CountEvidence graph)
  | [] => []
  | item :: rest =>
    if countPermits item.1 item.2 then firstCountReports rest
    else item :: (firstCountReports rest).filter (fun other => other.2.sender != item.2.sender)

/-- The retained item for a sender is its earliest observed forbidden item. -/
theorem find_firstCountReports (seen : List (CountEvidence graph)) (who : Player) :
    (firstCountReports seen).find? (fun item => item.2.sender == who) =
      seen.find? (fun item => item.2.sender == who && !countPermits item.1 item.2) := by
  induction seen with
  | nil => rfl
  | cons first rest ih =>
    by_cases permitted : countPermits first.1 first.2 = true
    · simpa [firstCountReports, permitted, List.find?_cons] using ih
    · by_cases owner : first.2.sender = who
      · simp [firstCountReports, permitted, owner]
      · simp only [firstCountReports, permitted, Bool.false_eq_true, ite_false, List.find?_cons,
          beq_eq_false_iff_ne.mpr owner, Bool.false_and, List.find?_filter]
        convert ih using 2
        rename_i item _
        by_cases same : item.2.sender = who <;> simp [same, Ne.symm owner]

theorem firstCountReports_subset (seen : List (CountEvidence graph)) :
    firstCountReports seen ⊆ seen := by
  induction seen with
  | nil => exact List.Subset.refl _
  | cons first rest ih =>
    simp only [firstCountReports]
    split
    · exact fun _ member => List.mem_cons_of_mem _ (ih member)
    · exact List.cons_subset_cons _ (fun _ member => ih (List.mem_filter.mp member).1)

/-- The queue contains at most one item from each sender. -/
theorem firstCountReports_senders_nodup (seen : List (CountEvidence graph)) :
    ((firstCountReports seen).map (fun item => item.2.sender)).Nodup := by
  induction seen with
  | nil => simp [firstCountReports]
  | cons first rest ih =>
    simp only [firstCountReports]
    split
    · exact ih
    · apply List.nodup_cons.mpr
      constructor
      · simp only [List.mem_map, List.mem_filter, bne_iff_ne]
        grind
      · exact ih.sublist ((List.filter_sublist ..).map _)

/-- Selection leaves the set of players with a witnessed violation unchanged. -/
theorem firstCountReports_violation_iff (seen : List (CountEvidence graph)) (who : Player) :
    firstCountReports seen ∈ countViolation who ↔ seen ∈ countViolation who := by
  constructor
  · rintro ⟨item, member, owner, bad⟩
    exact ⟨item, firstCountReports_subset seen member, owner, bad⟩
  · induction seen with
    | nil => exact id
    | cons first rest ih =>
      intro witnessed
      simp only [firstCountReports]
      split
      next allowed =>
        apply ih
        obtain ⟨item, member, owner, bad⟩ := witnessed
        rcases List.mem_cons.mp member with rfl | later
        · simp_all
        · exact ⟨_, later, owner, bad⟩
      next rejected =>
        by_cases owner : first.2.sender = who
        · exact ⟨first, List.mem_cons_self, owner, Bool.eq_false_iff.mpr rejected⟩
        · obtain ⟨item, member, sender, bad⟩ := witnessed
          have later : item ∈ rest := (List.mem_cons.mp member).resolve_left (by grind)
          obtain ⟨report, kept, author, forbidden⟩ := ih ⟨item, later, sender, bad⟩
          exact ⟨report, List.mem_cons_of_mem _ (List.mem_filter.mpr
            ⟨kept, by simpa only [bne_iff_ne, author] using Ne.symm owner⟩), author, forbidden⟩

/-- Submit the first witnessed violation per sender to the supplied report
channel, using its original observation law and challenge window. -/
def firstCountReportService (service : EvidenceReportService (CountEvidence graph)) :
    EvidenceReportService (CountEvidence graph) :=
  { service with
    reports := fun seen => service.reports (firstCountReports seen)
    reports_authentic := fun seen reports supported report member =>
      firstCountReports_subset seen (service.reports_authentic _ reports supported report member)
    reports_timelySubmitted := fun seen =>
      service.reports_timelySubmitted (firstCountReports seen) }

/-- Partial observations may be arbitrarily correlated. It suffices to
capture a violation by the player and deliver its selected witness from
the resulting queue by the deadline, conditional on that observation. -/
theorem countEvidenceCoverage_of_firstReport (service : EvidenceReportService (CountEvidence graph))
    (observationRate deliveryRate : Player → ℝ)
    (capture : ∀ actual who, actual ∈ countViolation who → observationRate who ≤
      ((service.observations actual).toOuterMeasure (countViolation who)).toReal)
    (timely : ∀ actual who, actual ∈ countViolation who →
      ∀ seen ∈ (service.observations actual).support, ∀ item ∈ firstCountReports seen,
        item.2.sender = who → deliveryRate who ≤
          ((service.reports seen).toOuterMeasure {reports |
            item ∈ EvidenceReport.deliveredEvidence
              (service.window.reportCutoff + service.window.inclusionBound) reports}).toReal) :
    CountEvidenceCoverage service observationRate deliveryRate := by
  intro actual who witnessed
  refine ⟨capture actual who witnessed, ?_⟩
  intro seen supported observed
  obtain ⟨item, member, owner, bad⟩ := (firstCountReports_violation_iff seen who).2 observed
  refine (timely actual who witnessed seen supported item member owner).trans
    (ENNReal.toReal_mono (outerMeasure_ne_top _ _) ?_)
  apply (service.reports seen).toOuterMeasure_mono
  intro reports delivered
  exact ⟨item, delivered.1, owner, bad⟩

/-- Protecting each selected report for one inclusion bound after submission
gives conditional delivery rate one. The cutoff reserves this time before settlement. -/
theorem countEvidenceCoverage_of_bounded_report_delay
    (service : EvidenceReportService (CountEvidence graph)) (observationRate : Player → ℝ)
    (capture : ∀ actual who, actual ∈ countViolation who → observationRate who ≤
      ((service.observations actual).toOuterMeasure (countViolation who)).toReal)
    (inclusion : ∀ actual, ∀ seen ∈ (service.observations actual).support,
      ∀ reports ∈ (service.reports seen).support, ∀ item ∈ firstCountReports seen,
      ∃ report ∈ reports, report.evidence = item ∧
        report.includedAt ≤ report.submittedAt + service.window.inclusionBound) :
    CountEvidenceCoverage service observationRate (fun _ => 1) := by
  apply countEvidenceCoverage_of_firstReport service observationRate _ capture
  intro actual who _ seen observed item selected _
  have allTimely : (service.reports seen).support ⊆ {reports |
      item ∈ EvidenceReport.deliveredEvidence
        (service.window.reportCutoff + service.window.inclusionBound) reports} := by
    intro reports supported
    obtain ⟨report, present, same, bounded⟩ := inclusion actual seen observed reports supported
      item selected
    have early := (service.reports_timelySubmitted seen reports supported report present).1
    exact (EvidenceReport.mem_deliveredEvidence ..).mpr
      ⟨report, present, same, bounded.trans (Nat.add_le_add_right early _)⟩
  rw [((service.reports seen).toOuterMeasure_apply_eq_one_iff _).mpr allTimely]
  simp

/-- The one-witness service with whole-batch capture and delivery coins. -/
abbrev thinnedFirstCountReports (capture delivery : Set.Icc (0 : ℝ) 1) :
    EvidenceReportService (CountEvidence graph) :=
  firstCountReportService (EvidenceReportService.thinned capture delivery)

/-- Every supported report batch contains at most one item for each sender. -/
theorem thinnedFirstCountReports_senders_nodup (capture delivery : Set.Icc (0 : ℝ) 1)
    (seen : List (CountEvidence graph)) (reports : List (EvidenceReport (CountEvidence graph)))
    (supported : reports ∈ ((thinnedFirstCountReports capture delivery).reports seen).support) :
    (reports.map (fun report => report.evidence.2.sender)).Nodup := by
  obtain rfl | rfl := EvidenceReportService.erase_support delivery
    ((firstCountReports seen).map fun item => (⟨item, 0, 1⟩ : EvidenceReport _)) reports supported
  · simpa only [List.map_map, Function.comp_def] using firstCountReports_senders_nodup seen
  · simp

/-- With whole-batch capture, the delivered evidence has the batch-channel law
on the witnesses selected from the actual list. -/
theorem thinnedFirstCountReports_sample (capture delivery : Set.Icc (0 : ℝ) 1)
    (actual : List (CountEvidence graph)) :
    (thinnedFirstCountReports capture delivery).sample actual =
      (EvidenceReportService.thinned capture delivery).sample (firstCountReports actual) := by
  simp only [thinnedFirstCountReports, firstCountReportService, EvidenceReportService.sample,
    EvidenceReportService.thinned,
    EvidenceReportService.erase, mix_bind, PMF.pure_bind, firstCountReports]

/-- For each role with a violation, capture covers a witness and the selected
queue delivers a witness with the stated conditional probability. -/
theorem thinnedFirstCountReports_coverage (capture delivery : Set.Icc (0 : ℝ) 1) :
    CountEvidenceCoverage
      (thinnedFirstCountReports (graph := graph) capture delivery)
      (fun _ => capture.val) (fun _ => delivery.val) := by
  apply countEvidenceCoverage_of_firstReport
  · intro actual who witnessed
    exact (thinnedCountEvidence_coverage capture delivery actual who witnessed).1
  · intro _ _ _ seen _ item member _
    exact (EvidenceReportService.thinned_delivery_mass capture delivery
      (firstCountReports seen) item member).symm.le

/-- With the same capture and batch delivery rates, sending only one report
per sender preserves the joint distribution of all deposit charges. -/
theorem thinnedFirstCountReports_audit (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (capture delivery : Set.Icc (0 : ℝ) 1)
    (traffic : List ((reactiveApplication timeouts) leaks).TrafficRecord) :
    countAudit timeouts leaks (thinnedFirstCountReports capture delivery).sample traffic =
      countAudit timeouts leaks (EvidenceReportService.thinned capture delivery).sample
        traffic := by
  classical
  let actual := traffic.map (countEvidence timeouts leaks traffic)
  let charge := fun (items : List (CountEvidence graph)) (who : Player) =>
    decide (∃ item ∈ items, item.2.sender = who ∧ countPermits item.1 item.2 = false)
  let batch := EvidenceReportService.thinned (Evidence := CountEvidence graph) capture delivery
  change ((thinnedFirstCountReports capture delivery).sample actual).map charge =
    (batch.sample actual).map charge
  unfold EvidenceReportService.sample
  rw [PMF.map_bind, PMF.map_bind]
  apply bind_congr_on_support _
  intro seen _
  change ((batch.reports (firstCountReports seen)).map
    (EvidenceReport.deliveredEvidence batch.window.settlementTime)).map charge =
    ((batch.reports seen).map (EvidenceReport.deliveredEvidence batch.window.settlementTime)).map
      charge
  simp only [batch, EvidenceReportService.thinned_delivered_law, EvidenceReportService.erase,
    mix_map, PMF.pure_map]
  have same : charge (firstCountReports seen) = charge seen := by
    funext who
    exact decide_eq_decide.mpr (firstCountReports_violation_iff seen who)
  rw [same]

end Vegas.EventGraphRuntime
