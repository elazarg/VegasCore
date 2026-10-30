/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketExclusionPayoff
import Vegas.Game.ProgramPayoffs
import GameTheoryExtensions.Analysis.QuasilinearSettlement

/-! # Valuation and actual receipts under native public default

Valuation and cash use the same authoritative public default and full source
readout. Their sum is the total utility, so a joint utility law determines the
joint realized cash law without changing any retained source data.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Enforcement GameTheory.Math.Probability
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {Parameter : Type} (parameter : State L setup.context → Parameter)

/-- Valuation and cash add through the same public-default branch and zero fallback. -/
theorem exclusionBase_add
    (valuation transfer : Parameter × PublicOutcome setup.program → Player → ℝ)
    (exitValuation exitTransfer : Player → ℝ)
    (state : (application setup runtime leaks).ProtocolState) (who : Player) :
    exclusionBase setup runtime parameter
        (fun outcome owner => valuation outcome owner + transfer outcome owner)
        (fun owner => exitValuation owner + exitTransfer owner) leaks state who =
      exclusionBase setup runtime parameter valuation exitValuation leaks state who +
        exclusionBase setup runtime parameter transfer exitTransfer leaks state who := by
  cases state with
  | none => simp only [exclusionBase, add_zero]
  | some control =>
      simp only [exclusionBase]
      split_ifs
      · rfl
      · unfold exclusionReadoutUtility exclusionTerminalUtility
        cases sourceReadout setup runtime leaks (some control) with
        | none => simp only [Option.elim_none, add_zero]
        | some terminal =>
            dsimp only [Option.elim_some]
            unfold SourceProgram.exclusionUtility
            split_ifs <;> rfl

/-- On native support without public defaults, valuation factors through the
full typed source readout, even when the readout is absent. -/
theorem exclusionBase_valuation_factors
    (valuation : Parameter × PublicOutcome setup.program → Player → ℝ)
    (exitValuation : Player → ℝ)
    (law : PMF (application setup runtime leaks).ProtocolState)
    (clear : ∀ control, some control ∈ law.support →
      control.execution.application.config.defaulted = ∅) :
    ∀ state ∈ law.support,
      exclusionBase setup runtime parameter valuation exitValuation leaks state =
        fun who => (sourceReadout setup runtime leaks state).elim 0
          (fun terminal => valuation (setup.parameterOutcome parameter terminal) who) := by
  intro state supported
  funext who
  cases state with
  | none => rfl
  | some control =>
      have active : who ∉ control.execution.application.config.defaulted := by
        rw [clear control supported]
        exact Finset.notMem_empty _
      rw [exclusionBase_of_not_defaulted setup runtime parameter valuation exitValuation leaks
        control who active]
      cases read : sourceReadout setup runtime leaks (some control) with
      | none => rfl
      | some terminal =>
          apply exclusionTerminalUtility_of_not_defaulted
          change who ∉ terminal.defaults.defaulted
          rw [serviceSourceReadout_defaults setup .sequential runtime.deadline leaks control
            terminal read]
          exact active

/-- Inverting the joint utility law retains the full source configuration and
all cash and audit correlations. -/
theorem jointCashLaw_of_utility_law {Observation : Type}
    (valuation transfer : Parameter × PublicOutcome setup.program → Player → ℝ)
    (exitValuation exitTransfer : Player → ℝ)
    (law : PMF (application setup runtime leaks).ProtocolState)
    (reference : PMF (Option (Config Player L setup.program.terminalCtx) × (Player → ℝ)))
    (factors : ∀ state ∈ law.support,
      exclusionBase setup runtime parameter valuation exitValuation leaks state =
        fun who => (sourceReadout setup runtime leaks state).elim 0
          (fun terminal => valuation (setup.parameterOutcome parameter terminal) who))
    (observe : (application setup runtime leaks).ProtocolState → Observation)
    (audit : Observation → PMF (Player → Bool)) (deposit : Player → ℝ)
    (utilityLaw :
      (TerminalAudit.jointSettlement law
        (exclusionBase setup runtime parameter
          (fun outcome who => valuation outcome who + transfer outcome who)
          (fun who => exitValuation who + exitTransfer who) leaks) observe audit deposit).map
        (fun realized => (sourceReadout setup runtime leaks realized.1, realized.2)) =
        reference.map (utilityReadout (fun readout who =>
          readout.elim 0 (fun terminal =>
            valuation (setup.parameterOutcome parameter terminal) who)))) :
    (TerminalAudit.jointSettlement law
      (exclusionBase setup runtime parameter transfer exitTransfer leaks) observe audit deposit).map
      (fun realized => (sourceReadout setup runtime leaks realized.1, realized.2)) = reference := by
  have baseAdd : exclusionBase setup runtime parameter
      (fun outcome who => valuation outcome who + transfer outcome who)
      (fun who => exitValuation who + exitTransfer who) leaks = fun state who =>
      exclusionBase setup runtime parameter valuation exitValuation leaks state who +
        exclusionBase setup runtime parameter transfer exitTransfer leaks state who := by
    funext state who
    exact exclusionBase_add parameter valuation transfer exitValuation exitTransfer state who
  rw [baseAdd] at utilityLaw
  exact TerminalAudit.jointSettlement_readout_eq_of_utility_law law
    (exclusionBase setup runtime parameter valuation exitValuation leaks) _
    (sourceReadout setup runtime leaks) _ factors observe audit deposit reference utilityLaw

/-- Declared valuation plus actual audited program receipts has the native
total utility, including the separately declared exit valuation and transfer. -/
theorem exclusionBase_expect_monetaryUtility {Observation : Type}
    (valuation : Parameter × PublicOutcome setup.program → Player → ℝ)
    (exitValuation exitTransfer : Player → ℝ)
    (observe : (application setup runtime leaks).ProtocolState → Observation)
    (audit : Observation → PMF (Player → Bool)) (deposit : Player → ℝ)
    (state : (application setup runtime leaks).ProtocolState) (who : Player) :
    expect (TerminalAudit.settlement
        (exclusionBase setup runtime parameter
          (fun outcome owner => setup.program.publicTransfers outcome.2 owner) exitTransfer leaks)
        observe audit deposit state)
      (fun receipts => monetaryUtility
        (exclusionBase setup runtime parameter valuation exitValuation leaks)
        (state, receipts) who) =
      TerminalAudit.utility
        (exclusionBase setup runtime parameter (setup.program.parameterPaymentUtility valuation)
          (fun owner => exitValuation owner + exitTransfer owner) leaks)
        observe audit deposit state who := by
  rw [TerminalAudit.settlement_expect_monetaryUtility]
  congr 1
  funext current owner
  exact (exclusionBase_add parameter valuation _ exitValuation exitTransfer current owner).symm

end Vegas
