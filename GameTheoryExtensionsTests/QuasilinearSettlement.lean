/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.QuasilinearSettlement

/-! # Correlated charges with indistinguishable monetary receipts

Two players are charged together after a successful outcome, using one shared
coin. Failure is never charged. Charged success and uncharged failure pay the
same cash, but have different valuations. The full joint readout distinguishes
them and recovers the exact cash distribution from realized utility.
-/

noncomputable section

namespace GameTheoryExtensionsTests.QuasilinearSettlement

open GameTheory GameTheory.Enforcement.TerminalAudit

private def coin : PMF Bool := PMF.uniformOfFintype Bool

private def chargeCoin (outcome : Bool) : PMF Bool :=
  if outcome then coin else PMF.pure false

private def audit (outcome : Bool) : PMF (Bool → Bool) :=
  (chargeCoin outcome).map fun charged _ => charged

private def transfer (outcome who : Bool) : ℝ :=
  if outcome then (if who then 11 else 5) else (if who then 7 else 3)

private def deposit (who : Bool) : ℝ := if who then 4 else 2

private def valuation (outcome who : Bool) : ℝ :=
  (if outcome then 20 else 10) + if who then 1 else 0

private def cashObservation (outcome charged : Bool) : Bool × (Bool → ℝ) :=
  (outcome, fun who =>
    if outcome && !charged then (if who then 11 else 5) else (if who then 7 else 3))

private def utilityObservation (outcome charged : Bool) : Bool × (Bool → ℝ) :=
  (outcome, fun who => if outcome then
    (if charged then (if who then 28 else 23) else (if who then 32 else 25))
    else (if who then 18 else 13))

private def scenarioLaw (readout : Bool → Bool → Bool × (Bool → ℝ)) :
    PMF (Bool × (Bool → ℝ)) :=
  coin.bind fun outcome => (chargeCoin outcome).map (readout outcome)

/-- Both players share the very same realized charge verdict. -/
theorem audit_shared_charge (outcome : Bool) (verdict : Bool → Bool)
    (supported : verdict ∈ (audit outcome).support) : verdict false = verdict true := by
  rw [audit, PMF.support_map] at supported
  obtain ⟨charged, _, rfl⟩ := supported
  rfl

/-- An actual correlated monetary audit produces exactly these cash vectors. -/
theorem cash_distribution :
    jointSettlement coin transfer id audit deposit = scenarioLaw cashObservation := by
  simp only [jointSettlement, settlement, audit, PMF.map_comp]
  congr 1
  funext outcome
  apply GameTheory.Math.Probability.map_congr_on_support _
  intro charged supported
  cases outcome with
  | false =>
    have uncharged : charged = false := by simpa [chargeCoin] using supported
    subst charged
    apply Prod.ext
    · rfl
    · funext who
      cases who <;> norm_num [Function.comp_def, transfer, deposit, cashObservation]
  | true =>
    apply Prod.ext
    · rfl
    · funext who
      cases charged <;> cases who <;>
        norm_num [Function.comp_def, transfer, deposit, cashObservation]

/-- The concrete utility vectors retain both the outcome and shared audit coin. -/
theorem utility_distribution :
    (jointSettlement coin transfer id audit deposit).map (utilityReadout valuation) =
      scenarioLaw utilityObservation := by
  rw [cash_distribution]
  simp only [scenarioLaw, PMF.map_bind, PMF.map_comp]
  congr 1
  funext outcome
  congr 1
  funext charged
  apply Prod.ext
  · rfl
  · funext who
    cases outcome <;> cases charged <;> cases who <;>
      norm_num [Function.comp_def, utilityReadout, monetaryUtility,
        valuation, cashObservation, utilityObservation]

/-- Subtraction recovers this exact joint cash law, despite correlated charges. -/
theorem recovered_cash_distribution :
    (scenarioLaw utilityObservation).map (receiptReadout valuation) =
      scenarioLaw cashObservation := by
  rw [← utility_distribution, map_utilityReadout_receiptReadout, cash_distribution]

/-- Cash alone cannot distinguish failure from charged success. -/
theorem cash_does_not_determine_outcome :
    (cashObservation false false).2 = (cashObservation true true).2 ∧
      (cashObservation false false).1 ≠ (cashObservation true true).1 := by
  exact ⟨rfl, Bool.false_ne_true⟩

end GameTheoryExtensionsTests.QuasilinearSettlement
