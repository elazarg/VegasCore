/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimePreservingLaw

/-! # What reproducing the source settlement forces on native support

The selected source law has successful Safe publications and a fixed payoff
vector. Reproducing its full realized law forces the same typed readout and
payoff at every supported native terminal history. Every nonzero collateral
therefore has zero collection probability there, for arbitrary audit sampling.
These are necessary preservation conditions, without an equilibrium premise.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimePreservingSettlement

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeUtility
  LateOpeningRuntimePreservingLaw

variable (weight : ℝ) (nonnegative : 0 ≤ weight) (reward forfeit : ℝ)
  (sample : List (SettledEvidence setup .sequential) →
    PMF (List (SettledEvidence setup .sequential))) (deposit : Player → ℝ)
  (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
  (same : nativeTerminalLaw weight nonnegative reward forfeit sample deposit profile =
    safeTerminalLaw reward)

include same in
theorem supported_settlement_matches
    (history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).History)
    (reached : history ∈ ((LateOpeningRuntimeNash.model weight nonnegative).runBehavioral profile
      (2 * LateOpeningRuntimeService.horizon + 1)).support)
    (payoffs : Player → ℝ)
    (supported : payoffs ∈
      (LateOpeningRuntimeNash.settlement reward forfeit sample deposit history.state).support) :
    ∃ initial ∈ prior.support,
      serviceSourceReadout setup .sequential deadline leaks history.state =
        some (finalState initial.1 initial.2 true safe true) ∧
      payoffs = (fun who : Player => if who = alice then reward / 2 else (2 / 5 : ℝ)) := by
  have member : (serviceSourceReadout setup .sequential deadline leaks history.state, payoffs) ∈
      (nativeTerminalLaw weight nonnegative reward forfeit sample deposit profile).support := by
    apply (PMF.mem_support_bind_iff _ _ _).mpr
    refine ⟨history, reached, ?_⟩
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨payoffs, supported, rfl⟩
  rw [same, safeTerminalLaw, PMF.mem_support_map_iff] at member
  obtain ⟨initial, initialSupported, pairEq⟩ := member
  exact ⟨initial, initialSupported, (congrArg Prod.fst pairEq).symm,
    (congrArg Prod.snd pairEq).symm⟩

include same in
/-- Even when the audit is randomized, the supported history has a fixed
realized settlement vector if the joint source law is reproduced. -/
theorem history_settlement_pure
    (history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).History)
    (reached : history ∈ ((LateOpeningRuntimeNash.model weight nonnegative).runBehavioral profile
      (2 * LateOpeningRuntimeService.horizon + 1)).support) :
    LateOpeningRuntimeNash.settlement reward forfeit sample deposit history.state =
      PMF.pure (fun who : Player => if who = alice then reward / 2 else (2 / 5 : ℝ)) := by
  apply pmf_eq_pure_of_support_subset_singleton
  intro payoffs supported
  obtain ⟨_, _, _, fixed⟩ := supported_settlement_matches weight nonnegative reward forfeit
    sample deposit profile same history reached payoffs supported
  exact Set.mem_singleton_iff.mpr fixed

include same in
theorem history_payoff_fixed
    (history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).History)
    (reached : history ∈ ((LateOpeningRuntimeNash.model weight nonnegative).runBehavioral profile
      (2 * LateOpeningRuntimeService.horizon + 1)).support) (who : Player) :
    LateOpeningRuntimeNash.payoff reward forfeit sample deposit history.state who =
      if who = alice then reward / 2 else (2 / 5 : ℝ) := by
  have equality := TerminalAudit.settlement_expect (nativeBaseUtility reward forfeit)
    (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
    (serviceSourceAudit setup .sequential deadline leaks sample) deposit history.state who
  change expect (LateOpeningRuntimeNash.settlement reward forfeit sample deposit history.state)
    (fun payoffs => payoffs who) =
      LateOpeningRuntimeNash.payoff reward forfeit sample deposit history.state who at equality
  rw [history_settlement_pure weight nonnegative reward forfeit sample deposit profile same
    history reached, expect_pure] at equality
  exact equality.symm

include same in
/-- Charge freedom follows from the actual preserved settlement for every
nonzero deposit. No audit authenticity or payoff-sign assumption is needed. -/
theorem history_charge_zero
    (history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).History)
    (reached : history ∈ ((LateOpeningRuntimeNash.model weight nonnegative).runBehavioral profile
      (2 * LateOpeningRuntimeService.horizon + 1)).support)
    (who : Player) (nonzero : deposit who ≠ 0) :
    TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential deadline leaks sample) history.state who = 0 := by
  obtain ⟨payoffs, supported⟩ :=
    (LateOpeningRuntimeNash.settlement reward forfeit sample deposit history.state).support_nonempty
  obtain ⟨initial, _, decoded, _⟩ := supported_settlement_matches weight nonnegative reward forfeit
    sample deposit profile same history reached payoffs supported
  have base : nativeBaseUtility reward forfeit history.state who =
      if who = alice then reward / 2 else (2 / 5 : ℝ) := by
    rw [nativeBaseUtility_of_readout reward forfeit history.state _ decoded]
    obtain ⟨aliceValue, bobValue⟩ := sourceUtility_intended reward forfeit initial.1 initial.2
    fin_cases who
    · change sourceUtility reward forfeit (finalState initial.1 initial.2 true safe true) alice =
        if alice = alice then reward / 2 else (2 / 5 : ℝ)
      rw [ite_eq_left rfl]
      exact aliceValue
    · change sourceUtility reward forfeit (finalState initial.1 initial.2 true safe true) bob =
        if bob = alice then reward / 2 else (2 / 5 : ℝ)
      rw [ite_eq_right (by decide : bob ≠ alice)]
      exact bobValue
  have utility := history_payoff_fixed weight nonnegative reward forfeit sample deposit profile
    same history reached who
  change nativeBaseUtility reward forfeit history.state who -
    TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential deadline leaks sample) history.state who * deposit who =
        _ at utility
  rw [base] at utility
  have product : TerminalAudit.charge
      (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential deadline leaks sample) history.state who *
        deposit who = 0 := by linarith
  exact (mul_eq_zero.mp product).resolve_right nonzero

end Vegas.Examples.LateOpeningRuntimePreservingSettlement
