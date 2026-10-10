/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeUniformSeObstruction
import Vegas.Examples.LateOpeningRuntimePreservingSettlement

/-! # Native charges under partial sender auditing

The sampler always retains the receiver's signed evidence and retains the
sender's evidence with a fixed probability. Public binding omissions remain
fully charged. Since the sender owns no binding event, this is exactly the
full-audit utility with a scaled sender deposit on every raw history.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimePartialAudit

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Enforcement GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeUtility
  LateOpeningRuntimePreservingLaw

abbrev Evidence := SettledEvidence setup .sequential

/-- All receiver evidence is retained; sender evidence is retained together
with probability `probability`. Sampling never creates signed evidence. -/
def sample (probability : ℝ) (nonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    (actual : List Evidence) : PMF (List Evidence) :=
  mix probability nonnegative bounded (PMF.pure actual)
    (PMF.pure (actual.filter fun evidence => evidence.2.sender = bob))

/-- The actual collection-equivalent full-audit deposits. -/
def effectiveDeposit (probability : ℝ) (deposit : Player → ℝ) (who : Player) : ℝ :=
  if who = alice then probability * deposit who else deposit who

theorem sample_authentic (probability : ℝ) (nonnegative : 0 ≤ probability)
    (bounded : probability ≤ 1) (actual observed : List Evidence)
    (supported : observed ∈ (sample probability nonnegative bounded actual).support) :
    observed ⊆ actual := by
  classical
  by_cases same : observed = actual
  · subst observed
    exact List.Subset.refl _
  · have filtered : observed = actual.filter (fun evidence => evidence.2.sender = bob) := by
      by_contra different
      rw [PMF.mem_support_iff, sample, mix_apply,
        PMF.pure_apply_of_ne _ _ same, PMF.pure_apply_of_ne _ _ different,
        mul_zero, mul_zero, add_zero] at supported
      exact supported rfl
    rw [filtered]
    intro evidence member
    exact (List.mem_filter.mp member).1

/-- Every actual envelope has conditional coverage at least the sender's
sampling probability. Receiver evidence is additionally always retained. -/
theorem sample_coverage (probability : ℝ) (nonnegative : 0 ≤ probability)
    (bounded : probability ≤ 1) (actual : List Evidence) (evidence : Evidence)
    (present : evidence ∈ actual) :
    probability ≤ ((sample probability nonnegative bounded actual).toOuterMeasure
      {observed | evidence ∈ observed}).toReal := by
  classical
  have domination (observed : List Evidence) :
      probability * ((PMF.pure actual) observed).toReal ≤
        ((sample probability nonnegative bounded actual) observed).toReal := by
    rw [sample, mix_apply_toReal]
    exact le_add_of_nonneg_right
      (mul_nonneg (sub_nonneg.mpr bounded) ENNReal.toReal_nonneg)
  have bound := probOf_domination (PMF.pure actual)
    (sample probability nonnegative bounded actual) probability domination
      {observed | evidence ∈ observed}
  simpa only [PMF.toOuterMeasure_pure_apply,
    ite_eq_left (show actual ∈ {observed | evidence ∈ observed} from present),
    ENNReal.toReal_one, mul_one] using bound

open Classical in
private theorem filtered_verdict (actual : List Evidence) (who : Player) :
    decide (∃ evidence ∈ actual.filter (fun evidence : Evidence => evidence.2.sender = bob),
      evidence.2.sender = who ∧ evidence.1.permits evidence.2 = false) =
      if who = alice then false else
        decide (∃ evidence ∈ actual,
          evidence.2.sender = who ∧ evidence.1.permits evidence.2 = false) := by
  classical
  fin_cases who
  · simp only [List.mem_filter, decide_eq_true_eq, Fin.zero_eta, Fin.isValue, Prod.exists,
      ↓reduceIte, decide_eq_false_iff_not, not_exists, not_and, Bool.not_eq_false, and_imp]
    intro record message _ owned other
    rw [owned] at other
    cases other
  · simp [alice, bob, and_assoc]

theorem partial_charge (probability : ℝ) (nonnegative : 0 ≤ probability)
    (bounded : probability ≤ 1) (state : app.ProtocolState) (who : Player) :
    TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
        (serviceSourceAudit setup .sequential deadline leaks
          (sample probability nonnegative bounded)) state who =
      (if who = alice then probability else 1) *
        TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
          (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
          state who := by
  classical
  change TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
    (LateOpeningRuntimeService.runtime.serviceAudit leaks fun record =>
      app.sampledTrafficAudit (fun traffic => ((record, traffic.envelope) : Evidence))
        (fun evidence => evidence.2.sender) (fun evidence => evidence.1.permits evidence.2)
          (sample probability nonnegative bounded)) state who =
    (if who = alice then probability else 1) *
      TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
        (LateOpeningRuntimeService.runtime.serviceAudit leaks fun record =>
          app.sampledTrafficAudit (fun traffic => ((record, traffic.envelope) : Evidence))
            (fun evidence => evidence.2.sender) (fun evidence => evidence.1.permits evidence.2)
              (fun actual => PMF.pure actual)) state who
  cases state with
  | none =>
      rw [serviceAudit_charge_none, serviceAudit_charge_none, mul_zero]
  | some control =>
      rw [serviceAudit_charge, serviceAudit_charge]
      by_cases missing : control.execution.application.publicView.missedBindingBy who = true
      · have receiver : who ≠ alice := by
          intro same
          subst who
          rw [alice_no_binding_omission] at missing
          cases missing
        simp [missing, receiver]
      · simp only [missing, Bool.false_eq_true, ↓reduceIte]
        simp only [ReactiveApplication.sampledTrafficAudit, sample,
        mix_map, PMF.pure_map]
        rw [mix_apply_toReal]
        simp only [filtered_verdict]
        fin_cases who
        · simp [alice, PMF.pure_apply]
        · (simp [alice, PMF.pure_apply]; ring)

theorem partial_payoff (probability : ℝ) (nonnegative : 0 ≤ probability)
    (bounded : probability ≤ 1) (reward forfeit : ℝ) (deposit : Player → ℝ)
    (state : app.ProtocolState) (who : Player) :
    LateOpeningRuntimeNash.payoff reward forfeit (sample probability nonnegative bounded)
        deposit state who =
      LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
        (effectiveDeposit probability deposit) state who := by
  unfold LateOpeningRuntimeNash.payoff TerminalAudit.utility
  rw [partial_charge]
  unfold effectiveDeposit
  split_ifs <;> ring

/-- Reproducing the Safe joint law under this partial sampler also reproduces
it under the collection-equivalent full audit. Realized settlement, rather
than equality of expected payoffs alone, supplies the supportwise argument. -/
theorem preserving_partial_implies_full (probability : ℝ) (positive : 0 < probability)
    (bounded : probability ≤ 1) (weight : ℝ) (nonnegative : 0 ≤ weight)
    (reward forfeit : ℝ) (deposit : Player → ℝ) (nonzero : ∀ who, deposit who ≠ 0)
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (same : nativeTerminalLaw weight nonnegative reward forfeit
      (sample probability positive.le bounded) deposit profile = safeTerminalLaw reward) :
    nativeTerminalLaw weight nonnegative reward forfeit (fun actual => PMF.pure actual)
      (effectiveDeposit probability deposit) profile = safeTerminalLaw reward := by
  classical
  refine Eq.trans ?_ same
  unfold nativeTerminalLaw
  apply bind_congr_on_support _
  intro history reached
  have partialZero (who : Player) :=
    LateOpeningRuntimePreservingSettlement.history_charge_zero weight nonnegative reward forfeit
      (sample probability positive.le bounded) deposit profile same history reached who
        (nonzero who)
  have fullZero (who : Player) :
      TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
        (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
          history.state who = 0 := by
    have zero := partialZero who
    rw [partial_charge] at zero
    by_cases sender : who = alice
    · rw [ite_eq_left sender] at zero
      exact (mul_eq_zero.mp zero).resolve_left positive.ne'
    · simpa only [ite_eq_right sender, one_mul] using zero
  have partialClean := TerminalAudit.settlement_clean (nativeBaseUtility reward forfeit)
    (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
    (serviceSourceAudit setup .sequential deadline leaks (sample probability positive.le bounded))
    deposit history.state partialZero
  have fullClean := TerminalAudit.settlement_clean (nativeBaseUtility reward forfeit)
    (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
    (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
    (effectiveDeposit probability deposit) history.state fullZero
  change (TerminalAudit.settlement _ _ _ _ _).map _ =
    (TerminalAudit.settlement _ _ _ _ _).map _
  rw [fullClean, partialClean]

/-- Fixed partially audited sender collateral admits arbitrarily reliable
native services with equilibria, none of which realizes the Safe source law.
The receiver remains fully audited, including public binding omissions. -/
theorem exists_service_with_no_preserving_equilibrium
    (probability : ℝ) (positive : 0 < probability) (bounded : probability ≤ 1)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (rewardPositive : 0 < reward) (largeForfeit : reward < forfeit)
    (aliceCollateral : reward < probability * deposit alice) (bobCollateral : 1 < deposit bob)
    (failureFloor : ℝ) (floorPositive : 0 < failureFloor) :
    ∃ (weight : ℝ) (nonnegative : 0 ≤ weight),
      0 < weight ∧
      LateOpeningRuntimeService.runtime.AsyncContract leaks initial
        LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
          delay bound ∧
      LateOpeningRuntimeService.runtime.BlindToLatePackets leaks bound
        (LateOpeningRuntimeService.scheduler weight nonnegative) ∧
      0 < 1 - LateOpeningRuntimeLateAcceptance.inclusionProbability weight ∧
      1 - LateOpeningRuntimeLateAcceptance.inclusionProbability weight < failureFloor ∧
      (∃ assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment,
        assessment.IsSequentialEquilibrium
          (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
          (rawMenu.bounded initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
          (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
            (sample probability positive.le bounded) deposit history.state who)) ∧
      ∀ assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment,
        assessment.IsSequentialEquilibrium
          (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
          (rawMenu.bounded initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
          (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
            (sample probability positive.le bounded) deposit history.state who) →
        nativeTerminalLaw weight nonnegative reward forfeit
          (sample probability positive.le bounded) deposit assessment.strategy ≠
            safeTerminalLaw reward := by
  have aliceEffective : reward < effectiveDeposit probability deposit alice := by
    change reward < probability * deposit alice
    exact aliceCollateral
  have bobEffective : 1 < effectiveDeposit probability deposit bob := by
    simpa only [effectiveDeposit, ite_eq_right (by decide : bob ≠ alice)] using bobCollateral
  obtain ⟨weight, nonnegative, servicePositive, contract, blind, failurePositive, close,
    existsEquilibrium, excludes⟩ :=
    LateOpeningRuntimeUniformSeObstruction.exists_service_with_no_preserving_equilibrium
      reward forfeit (effectiveDeposit probability deposit) rewardPositive largeForfeit
        aliceEffective bobEffective failureFloor floorPositive
  have payoffs : (fun who (history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).History) =>
      LateOpeningRuntimeNash.payoff reward forfeit
        (sample probability positive.le bounded) deposit history.state who) =
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual)
        (effectiveDeposit probability deposit) history.state who) := by
    funext who history
    exact partial_payoff probability positive.le bounded reward forfeit deposit history.state who
  refine ⟨weight, nonnegative, servicePositive, contract, blind, failurePositive, close, ?_, ?_⟩
  · simpa only [payoffs] using existsEquilibrium
  · intro assessment equilibrium same
    have fullEquilibrium := equilibrium
    rw [payoffs] at fullEquilibrium
    apply excludes assessment fullEquilibrium
    apply preserving_partial_implies_full probability positive bounded weight nonnegative
      reward forfeit deposit _ assessment.strategy same
    intro who
    fin_cases who
    · have productPositive := rewardPositive.trans aliceCollateral
      exact (mul_ne_zero_iff.mp productPositive.ne').2
    · exact (zero_lt_one.trans bobCollateral).ne'

end Vegas.Examples.LateOpeningRuntimePartialAudit
