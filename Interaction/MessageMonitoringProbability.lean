/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageMonitoring

/-! # Sampling and reporting at one network snapshot

The existing passive observation rule induces a law on ordinary-view report
material. Bounds here concern a fixed snapshot and one observer activation.
They do not supply activation guarantees or bounds conditional on a sender's
information across an execution. A report-delivery kernel is an assumed
continuation law, not an additional execution model or enforcement service.
-/

noncomputable section

namespace Interaction.MessageNetwork

open GameTheory.Math.Probability

variable {Principal Payload : Type} [DecidableEq Principal]

/-- Report material obtained by the existing sampling rule at this snapshot. -/
def reportLaw (network : MessageNetwork Principal Payload)
    (rule : ObservationRule Principal Payload) (who : Principal)
    (violation : Message Principal Payload → Bool) :
    FinDist (List (Message Principal Payload)) :=
  (rule who network.pending).map fun selected =>
    ((network.learn who selected).observe who).reports violation

/-- At a fixed snapshot, sampling a fresh offending foreign packet always
places it in the ordinary observation's report material. -/
theorem sampling_le_report (network : MessageNetwork Principal Payload)
    (rule : ObservationRule Principal Payload) (who : Principal)
    (violation : Message Principal Payload → Bool) (id : MessageId Principal)
    (message : Message Principal Payload)
    (found : network.lookup id = some message) (foreign : id.1 ≠ who)
    (unknown : (network.known who).any (fun packet => packet.id = id) = false)
    (offending : violation message = true) :
    (rule who network.pending).probOf {selected | id ∈ selected} ≤
      (network.reportLaw rule who violation).probOf {reports | message ∈ reports} := by
  classical
  rw [reportLaw, FinDist.probOf_map, ← FinDist.expect_indicator_eq_probOf,
    ← FinDist.expect_indicator_eq_probOf]
  apply FinDist.expect_mono
  intro selected _
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  by_cases chosen : id ∈ selected
  · have reported := network.reports_learn_selected violation who selected id message
      found foreign chosen unknown offending
    simp only [chosen, reported, ↓reduceIte, le_refl]
  · simp only [chosen, ↓reduceIte]
    split <;> norm_num

/-- Every sample at a compliant snapshot produces no report. Compliance is
required only for this observer's retained packets and the current pending pool. -/
theorem reportLaw_eq_pure_nil_of_compliant (network : MessageNetwork Principal Payload)
    (rule : ObservationRule Principal Payload) (who : Principal)
    (violation : Message Principal Payload → Bool)
    (leaked : ∀ message ∈ network.leaked who, violation message = false)
    (ledger : ∀ message ∈ network.ledger, violation message = false)
    (pending : ∀ message ∈ network.pending, violation message = false) :
    network.reportLaw rule who violation = FinDist.pure [] := by
  have quiet : ∀ selected,
      ((network.learn who selected).observe who).reports violation = [] := by
    intro selected
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro message member
    obtain ⟨observed, offending⟩ := (PlayerView.mem_reports ..).mp member
    have compliant : violation message = false := by
      rcases observed with received | included
      · rcases network.learn_mem who selected message received with prior | fresh
        · exact leaked message prior
        · exact pending message fresh.1
      · exact ledger message included
    rw [compliant] at offending
    cases offending
  simp only [reportLaw, quiet, FinDist.map_const]

/-- Zero false positives at the specified compliant snapshot; this alone does
not establish that every legal source execution has compliant snapshots. -/
theorem reportLaw_prob_nonempty_of_compliant (network : MessageNetwork Principal Payload)
    (rule : ObservationRule Principal Payload) (who : Principal)
    (violation : Message Principal Payload → Bool)
    (leaked : ∀ message ∈ network.leaked who, violation message = false)
    (ledger : ∀ message ∈ network.ledger, violation message = false)
    (pending : ∀ message ∈ network.pending, violation message = false) :
    (network.reportLaw rule who violation).probOf {reports | reports ≠ []} = 0 := by
  classical
  rw [network.reportLaw_eq_pure_nil_of_compliant rule who violation leaked ledger pending,
    ← FinDist.expect_indicator_eq_probOf, FinDist.expect_pure]
  simp

/-- Sampling and a conditional reporting guarantee compose at this fixed
snapshot. Delivery may depend on the complete report material: no independence
assumption is used. The supplied kernel and lower bounds need implementation. -/
theorem sampling_delivery_lower (network : MessageNetwork Principal Payload)
    (rule : ObservationRule Principal Payload) (who : Principal)
    (violation : Message Principal Payload → Bool) (id : MessageId Principal)
    (message : Message Principal Payload)
    (found : network.lookup id = some message) (foreign : id.1 ≠ who)
    (unknown : (network.known who).any (fun packet => packet.id = id) = false)
    (offending : violation message = true)
    (deliver : List (Message Principal Payload) → FinDist Bool) (p q : ℝ)
    (nonnegative : 0 ≤ q)
    (sampling : p ≤ (rule who network.pending).probOf {selected | id ∈ selected})
    (delivery : ∀ reports ∈ (network.reportLaw rule who violation).support,
      reports ≠ [] → q ≤ (deliver reports).prob true) :
    p * q ≤ ((network.reportLaw rule who violation).bind deliver).prob true := by
  classical
  calc
    p * q ≤ (rule who network.pending).probOf {selected | id ∈ selected} * q :=
      mul_le_mul_of_nonneg_right sampling nonnegative
    _ = (rule who network.pending).expect
        (fun selected => q * if selected ∈ {selected | id ∈ selected} then 1 else 0) := by
      rw [FinDist.expect_smul, FinDist.expect_indicator_eq_probOf, mul_comm]
    _ ≤ (rule who network.pending).expect (fun selected =>
        (deliver (((network.learn who selected).observe who).reports violation)).prob true) := by
      apply FinDist.expect_mono
      intro selected supported
      by_cases chosen : id ∈ selected
      · have reported := network.reports_learn_selected violation who selected id message
          found foreign chosen unknown offending
        have reportSupported : ((network.learn who selected).observe who).reports violation ∈
            (network.reportLaw rule who violation).support := by
          rw [reportLaw, FinDist.support_map]
          exact ⟨selected, supported, rfl⟩
        have nonempty : ((network.learn who selected).observe who).reports violation ≠ [] := by
          intro empty
          rw [empty] at reported
          exact List.not_mem_nil reported
        simpa only [Set.mem_ofPred_eq, chosen, ↓reduceIte, mul_one] using
          delivery _ reportSupported nonempty
      · simpa only [Set.mem_ofPred_eq, chosen, ↓reduceIte, mul_zero] using
          (deliver (((network.learn who selected).observe who).reports violation)).prob_nonneg true
    _ = ((network.reportLaw rule who violation).bind deliver).prob true := by
      rw [reportLaw, FinDist.bind_map, FinDist.prob_bind]

end Interaction.MessageNetwork
