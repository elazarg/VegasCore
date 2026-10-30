/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.NativeExitContinuation
import Vegas.Game.ProgramPayoffs
import Vegas.Pending.ExclusionPrefix
import GameTheoryExtensions.Analysis.QuasilinearSettlement

/-! # Valuation and actual receipts in the permanent-exclusion runtime -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Enforcement GameTheory.Math.Probability
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {Parameter : Type} (parameter : State L setup.context → Parameter)

/-- Valuation and cash use the same exclusion branches and zero fallback. -/
theorem recoveryExclusionBase_add
    (valuation transfer : Parameter × PublicOutcome setup.program → Player → ℝ)
    (exitValuation exitTransfer : Player → ℝ)
    (state : (recoveryApplication runtime leaks).ProtocolState) (who : Player) :
    recoveryExclusionBase (runtime := runtime) (leaks := leaks) parameter
        (fun outcome owner => valuation outcome owner + transfer outcome owner)
        (fun owner => exitValuation owner + exitTransfer owner) state who =
      recoveryExclusionBase (runtime := runtime) (leaks := leaks) parameter
        valuation exitValuation state who +
        recoveryExclusionBase (runtime := runtime) (leaks := leaks) parameter
          transfer exitTransfer state who := by
  cases state with
  | none => simp only [recoveryExclusionBase, add_zero]
  | some control =>
      unfold recoveryExclusionBase
      dsimp only
      split_ifs
      · rfl
      · rw [exclusionBase_eq_readout, exclusionBase_eq_readout, exclusionBase_eq_readout]
        unfold exclusionReadoutUtility exclusionTerminalUtility
        cases sourceReadout setup runtime leaks
            (some (RecoveryProjection.control runtime leaks control)) with
        | none => simp only [Option.elim_none, add_zero]
        | some terminal =>
            dsimp only [Option.elim_some]
            unfold SourceProgram.exclusionUtility
            split_ifs <;> rfl

/-- On clean support whose typed readouts occur in intended histories, the
runtime valuation is the ordinary valuation of the retained source store. -/
theorem recoveryExclusionBase_valuation_factors
    (wellFormed : setup.WellFormed)
    (valuation : Parameter × PublicOutcome setup.program → Player → ℝ)
    (exitValuation : Player → ℝ)
    (law : PMF (recoveryApplication runtime leaks).ProtocolState)
    (clear : ∀ control, some control ∈ law.support → control.execution.application.excluded = ∅)
    (intendedReadouts : ∀ state ∈ law.support, ∃ history : setup.intendedProtocol.History,
      sourceReadout setup runtime leaks (RecoveryProjection.protocolState runtime leaks state) =
        setup.protocolReadout history.state) :
    ∀ state ∈ law.support,
      recoveryExclusionBase (runtime := runtime) (leaks := leaks) parameter
          valuation exitValuation state =
        fun who => (sourceReadout setup runtime leaks
          (RecoveryProjection.protocolState runtime leaks state)).elim 0
            (fun terminal => valuation (setup.parameterOutcome parameter terminal) who) := by
  intro state supported
  funext who
  cases state with
  | none => rfl
  | some control =>
      have notExcluded : who ∉ control.execution.application.excluded := by
        rw [clear control supported]
        exact Finset.notMem_empty _
      rw [recoveryExclusionBase_of_not_excluded (runtime := runtime) (leaks := leaks)
        parameter valuation exitValuation control who notExcluded, exclusionBase_eq_readout]
      obtain ⟨history, same⟩ := intendedReadouts (some control) supported
      change exclusionReadoutUtility setup parameter valuation exitValuation
          (sourceReadout setup runtime leaks
            (RecoveryProjection.protocolState runtime leaks (some control))) who = _
      rw [same]
      exact setup.intended_exclusionReadoutUtility wellFormed parameter valuation
        exitValuation history who

/-- Invert the retained joint utility law into the actual joint cash law.
All state, receipt and audit correlations remain in the common law. -/
theorem recovery_jointCashLaw_of_utility_law {Observation : Type}
    (valuation transfer : Parameter × PublicOutcome setup.program → Player → ℝ)
    (exitValuation exitTransfer : Player → ℝ)
    (law : PMF (recoveryApplication runtime leaks).ProtocolState)
    (reference : PMF (Option (State L setup.program.terminalCtx) × (Player → ℝ)))
    (factors : ∀ state ∈ law.support,
      recoveryExclusionBase (runtime := runtime) (leaks := leaks) parameter
          valuation exitValuation state =
        fun who => (sourceReadout setup runtime leaks
          (RecoveryProjection.protocolState runtime leaks state)).elim 0
            (fun terminal => valuation (setup.parameterOutcome parameter terminal) who))
    (observe : (recoveryApplication runtime leaks).ProtocolState → Observation)
    (audit : Observation → PMF (Player → Bool)) (deposit : Player → ℝ)
    (utilityLaw :
      (TerminalAudit.jointSettlement law
        (recoveryExclusionBase (runtime := runtime) (leaks := leaks) parameter
          (fun outcome who => valuation outcome who + transfer outcome who)
          (fun who => exitValuation who + exitTransfer who)) observe audit deposit).map
        (fun realized => (sourceReadout setup runtime leaks
          (RecoveryProjection.protocolState runtime leaks realized.1), realized.2)) =
        reference.map (utilityReadout (fun readout who =>
          readout.elim 0 (fun terminal =>
            valuation (setup.parameterOutcome parameter terminal) who)))) :
    (TerminalAudit.jointSettlement law
      (recoveryExclusionBase (runtime := runtime) (leaks := leaks) parameter transfer exitTransfer)
        observe audit deposit).map
      (fun realized => (sourceReadout setup runtime leaks
        (RecoveryProjection.protocolState runtime leaks realized.1), realized.2)) = reference := by
  have baseAdd : recoveryExclusionBase (runtime := runtime) (leaks := leaks) parameter
      (fun outcome who => valuation outcome who + transfer outcome who)
      (fun who => exitValuation who + exitTransfer who) =
      fun state who =>
        recoveryExclusionBase (runtime := runtime) (leaks := leaks) parameter
          valuation exitValuation state who +
          recoveryExclusionBase (runtime := runtime) (leaks := leaks) parameter
            transfer exitTransfer state who := by
    funext state who
    exact recoveryExclusionBase_add parameter valuation transfer exitValuation exitTransfer
      state who
  rw [baseAdd] at utilityLaw
  exact TerminalAudit.jointSettlement_readout_eq_of_utility_law law
    (recoveryExclusionBase (runtime := runtime) (leaks := leaks) parameter
      valuation exitValuation) _
    (fun state => sourceReadout setup runtime leaks
      (RecoveryProjection.protocolState runtime leaks state)) _ factors observe audit deposit
        reference utilityLaw

/-- The forced-exit recovery utility is also the expectation of declared
valuation plus actual audited cash, including its existing exclusion branches. -/
theorem recoveryExclusionBase_expect_monetaryUtility
    {setup : Setup (Player := Player) (L := L)}
    {runtime : EventGraphRuntime (graph setup)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (valuation : Parameter × PublicOutcome setup.program → Player → ℝ)
    (exitValuation exitTransfer : Player → ℝ) {Observation : Type}
    (observe : (recoveryApplication runtime leaks).ProtocolState → Observation)
    (audit : Observation → PMF (Player → Bool)) (deposit : Player → ℝ)
    (state : (recoveryApplication runtime leaks).ProtocolState) (who : Player) :
    expect (TerminalAudit.settlement
        (recoveryExclusionBase (runtime := runtime) parameter
          (fun outcome owner => setup.program.publicTransfers outcome.2 owner) exitTransfer)
        observe audit deposit state)
      (fun receipts => monetaryUtility
        (recoveryExclusionBase (runtime := runtime) parameter valuation exitValuation) (state,
          receipts) who) =
      TerminalAudit.utility
        (recoveryExclusionBase (runtime := runtime) parameter
          (setup.program.parameterPaymentUtility valuation)
          (fun owner => exitValuation owner + exitTransfer owner))
        observe audit deposit state who := by
  rw [TerminalAudit.settlement_expect_monetaryUtility]
  congr 1
  funext current owner
  exact (recoveryExclusionBase_add parameter valuation _
    exitValuation exitTransfer current owner).symm

end Vegas
