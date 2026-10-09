/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeProtectedReceipt
import Vegas.Examples.LateOpeningRuntimeNash

/-! # Reproducing the source law requires protected native acceptance

Every intended source equilibrium has the initialized Safe terminal law.
Any bounded raw native profile reproducing that law must obtain accepting
Alice receipt zero in the protected prefix. This conclusion is independent
of equilibrium, payoff signs, audit authenticity and collateral. It applies
to the actual typed readout and realized settlement law, rather than assuming
successful physical publication as a separate premise.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimePreservingLaw

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeProtectedOpening
  LateOpeningRuntimeProtectedReceipt

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

/-- The initialized typed terminal state together with realized audit payoff
for the actual bounded raw profile. -/
def nativeTerminalLaw (reward forfeit : ℝ)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential))) (deposit : Player → ℝ)
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who) :=
  ((LateOpeningRuntimeNash.model weight nonnegative).runBehavioral profile
    (2 * LateOpeningRuntimeService.horizon + 1)).bind fun history =>
      (LateOpeningRuntimeNash.settlement reward forfeit sample deposit history.state).map
        fun payoffs =>
          (serviceSourceReadout setup .sequential deadline leaks history.state, payoffs)

theorem native_terminal_readout (reward forfeit : ℝ)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential))) (deposit : Player → ℝ)
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who) :
    (nativeTerminalLaw weight nonnegative reward forfeit sample deposit profile).map Prod.fst =
      ((LateOpeningRuntimeNash.model weight nonnegative).runBehavioral profile
        (2 * LateOpeningRuntimeService.horizon + 1)).map
          (fun history => serviceSourceReadout setup .sequential deadline leaks history.state) := by
  unfold nativeTerminalLaw
  rw [PMF.map_bind]
  conv_rhs => rw [← pmf_bind_pure_eq_map]
  congr 1
  funext history
  rw [PMF.map_comp]
  exact PMF.map_const _ _

theorem readout_success (state : app.ProtocolState)
    (terminal : State simpleExpr program.terminalCtx)
    (decoded : serviceSourceReadout setup .sequential deadline leaks state = some terminal)
    (opened : (terminal.get alicePublication).isSuccess = true) :
    stateSucceeded state = true := by
  cases state with
  | none => simp [serviceSourceReadout] at decoded
  | some control =>
      unfold serviceSourceReadout at decoded
      rw [Option.bind_some] at decoded
      dsimp only at decoded
      split at decoded
      · have stored := decodeState?_agrees (terminalRefs program)
          control.execution.application.config.store terminal decoded alicePublication
        change control.execution.application.config.store (.inr aliceEvent) =
          some (terminal.get alicePublication) at stored
        simp only [stateSucceeded, aliceSucceeded, stored]
        exact opened
      · cases decoded

/-- Only Alice's public publication marginal is needed: this condition
does not reveal or constrain hidden terminal bindings or initial secrets. -/
theorem successful_readout_protected_receipt
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (same : ((LateOpeningRuntimeNash.model weight nonnegative).runBehavioral profile
        (2 * LateOpeningRuntimeService.horizon + 1)).map
          (fun history =>
            (serviceSourceReadout setup .sequential deadline leaks history.state).map
              (fun terminal => (terminal.get alicePublication).isSuccess)) =
      PMF.pure (some true)) :
    (app.roundsFrom initial (LateOpeningRuntimeService.scheduler weight nonnegative)
      (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) profile) 2).map protectedAccepted =
          PMF.pure true := by
  apply native_almost_sure_success_protected_receipt_law weight nonnegative profile
  change ((LateOpeningRuntimeNash.model weight nonnegative).runBehavioral profile
    (2 * LateOpeningRuntimeService.horizon + 1)).map
      (fun history => stateSucceeded history.state) = PMF.pure true
  apply pmf_eq_pure_of_support_subset_singleton
  intro result supported
  obtain ⟨history, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have projected :
      (serviceSourceReadout setup .sequential deadline leaks history.state).map
        (fun terminal => (terminal.get alicePublication).isSuccess) ∈
      (((LateOpeningRuntimeNash.model weight nonnegative).runBehavioral profile
        (2 * LateOpeningRuntimeService.horizon + 1)).map
          (fun final => (serviceSourceReadout setup .sequential deadline leaks final.state).map
            (fun terminal => (terminal.get alicePublication).isSuccess))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨history, reached, rfl⟩
  rw [same] at projected
  have known := (PMF.mem_support_pure_iff _ _).mp projected
  cases decoded : serviceSourceReadout setup .sequential deadline leaks history.state with
  | none => simp [decoded] at known
  | some terminal =>
      rw [decoded, Option.map_some] at known
      exact Set.mem_singleton_iff.mpr
        (readout_success history.state terminal decoded (Option.some.inj known))

/-- Matching just the source typed outcome marginal already forces the
protected accepting receipt; no target equilibrium assumption is used. -/
theorem safe_readout_protected_receipt
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (same : ((LateOpeningRuntimeNash.model weight nonnegative).runBehavioral profile
        (2 * LateOpeningRuntimeService.horizon + 1)).map
          (fun history => serviceSourceReadout setup .sequential deadline leaks history.state) =
      prior.map (fun initial => some (finalState initial.1 initial.2 true safe true))) :
    (app.roundsFrom initial (LateOpeningRuntimeService.scheduler weight nonnegative)
      (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) profile) 2).map protectedAccepted =
          PMF.pure true := by
  apply native_almost_sure_success_protected_receipt_law weight nonnegative profile
  change ((LateOpeningRuntimeNash.model weight nonnegative).runBehavioral profile
    (2 * LateOpeningRuntimeService.horizon + 1)).map
      (fun history => stateSucceeded history.state) = PMF.pure true
  apply pmf_eq_pure_of_support_subset_singleton
  intro result supported
  obtain ⟨history, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have projected : serviceSourceReadout setup .sequential deadline leaks history.state ∈
      (((LateOpeningRuntimeNash.model weight nonnegative).runBehavioral profile
        (2 * LateOpeningRuntimeService.horizon + 1)).map
          (fun final =>
            serviceSourceReadout setup .sequential deadline leaks final.state)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨history, reached, rfl⟩
  rw [same] at projected
  obtain ⟨parameter, _, decoded⟩ := (PMF.mem_support_map_iff _ _ _).mp projected
  apply Set.mem_singleton_iff.mpr
  exact readout_success history.state _ decoded.symm rfl

/-- The joint source state and realized net payoff law implies the necessary
protected receipt condition for every actual raw native profile. -/
theorem safe_settlement_protected_receipt (reward forfeit : ℝ)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential))) (deposit : Player → ℝ)
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (same : nativeTerminalLaw weight nonnegative reward forfeit sample deposit profile =
      safeTerminalLaw reward) :
    (app.roundsFrom initial (LateOpeningRuntimeService.scheduler weight nonnegative)
      (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) profile) 2).map protectedAccepted =
          PMF.pure true := by
  apply safe_readout_protected_receipt weight nonnegative profile
  have marginal := congrArg (fun law => law.map Prod.fst) same
  rw [native_terminal_readout] at marginal
  simpa only [safeTerminalLaw, PMF.map_comp, Function.comp_def] using marginal

/-- Preservation of any intended source equilibrium's joint law requires
protected native acceptance, irrespective of the target equilibrium notion. -/
theorem intended_law_protected_receipt (reward forfeit : ℝ)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential))) (deposit : Player → ℝ)
    (source : setup.intendedModel.BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibrium
      intended_decisionRecall.decisionInformationAntichain
        setup.intended_bounded.wellFoundedHistories (intendedPayoff reward))
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (same : nativeTerminalLaw weight nonnegative reward forfeit sample deposit profile =
      intendedTerminalLaw reward source.strategy) :
    (app.roundsFrom initial (LateOpeningRuntimeService.scheduler weight nonnegative)
      (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) profile) 2).map protectedAccepted =
          PMF.pure true := by
  rw [intended_equilibrium_terminal_law equilibrium] at same
  exact safe_settlement_protected_receipt weight nonnegative reward forfeit sample deposit
    profile same

end Vegas.Examples.LateOpeningRuntimePreservingLaw
