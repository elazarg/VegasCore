/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPaymentValuation
import Vegas.Pending.ExclusionPrefix

/-! # Conditional monetary readout of forced-exit recovery

Monetary inversion of an arbitrary runtime utility law needs a valuation
recoverable from the retained source readout. The condition below concerns only
valuation on supported excluded states. It is vacuous for the no-exclusion
support supplied by intended recovery preservation. For other laws, an excluded
state with no terminal readout requires zero exit valuation under the existing
zero-readout convention.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Enforcement GameTheory.Math.Probability
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The same optional typed source reader retained by forced-exit preservation. -/
def recoveryPaymentReadout (state : (recoveryApplication (runtime setup) leaks).ProtocolState) :
    Option (State L setup.program.terminalCtx) :=
  sourceReadout setup leaks (RecoveryProjection.protocolState (runtime setup) leaks state)

/-- Reading source exclusion utility commutes with addition of valuation and
cash, including failed reveals and absent terminal readouts. -/
theorem exclusionReadoutUtility_add {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (valuation transfer : Parameter × PublicOutcome setup.program → Player → ℝ)
    (exitValuation exitTransfer : Player → ℝ)
    (readout : Option (State L setup.program.terminalCtx)) (who : Player) :
    exclusionReadoutUtility setup parameter
        (fun outcome owner => valuation outcome owner + transfer outcome owner)
        (fun owner => exitValuation owner + exitTransfer owner) readout who =
      exclusionReadoutUtility setup parameter valuation exitValuation readout who +
        exclusionReadoutUtility setup parameter transfer exitTransfer readout who := by
  cases readout with
  | none => simp only [exclusionReadoutUtility, Option.elim_none, add_zero]
  | some terminal =>
    exact exclusionUtility_add setup.program valuation transfer exitValuation exitTransfer
      (setup.parameterOutcome parameter terminal) who

/-- Unexcluded states already factor through the retained source reader. The
only additional obligation is that constant exit valuation agree with its value
at the retained readout on every supported excluded state. -/
theorem recoveryExclusionBase_valuation_factors {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (valuation : Parameter × PublicOutcome setup.program → Player → ℝ)
    (exitValuation : Player → ℝ)
    (law : PMF (recoveryApplication (runtime setup) leaks).ProtocolState)
    (exitCompatible : ∀ control, some control ∈ law.support → ∀ who,
      who ∈ control.execution.application.excluded →
      exitValuation who = exclusionReadoutUtility setup parameter valuation exitValuation
        (recoveryPaymentReadout setup leaks (some control)) who) :
    ∀ state ∈ law.support,
      recoveryExclusionBase parameter valuation exitValuation state =
        exclusionReadoutUtility setup parameter valuation exitValuation
          (recoveryPaymentReadout setup leaks state) := by
  intro state supported
  funext who
  cases state with
  | none => rfl
  | some control =>
    by_cases excluded : who ∈ control.execution.application.excluded
    · rw [recoveryExclusionBase_of_excluded parameter valuation exitValuation control who excluded]
      exact exitCompatible control supported who excluded
    · rw [recoveryExclusionBase_of_not_excluded parameter valuation exitValuation control who
        excluded, exclusionBase_eq_readout]
      rfl

/-- A preserved utility law yields the actual joint cash law under the explicit
exit-valuation factorability condition. The audit may be correlated and need
not be clean. No equilibrium or scheduling hypothesis is added or removed. -/
theorem recovery_jointCashLaw_of_utility_law {Parameter Observation : Type}
    (parameter : State L setup.context → Parameter)
    (valuation : Parameter × PublicOutcome setup.program → Player → ℝ)
    (exitValuation exitTransfer : Player → ℝ)
    (law : PMF (recoveryApplication (runtime setup) leaks).ProtocolState)
    (reference : PMF (Option (State L setup.program.terminalCtx)))
    (exitCompatible : ∀ control, some control ∈ law.support → ∀ who,
      who ∈ control.execution.application.excluded →
      exitValuation who = exclusionReadoutUtility setup parameter valuation exitValuation
        (recoveryPaymentReadout setup leaks (some control)) who)
    (observe : (recoveryApplication (runtime setup) leaks).ProtocolState → Observation)
    (audit : Observation → PMF (Player → Bool)) (deposit : Player → ℝ)
    (utilityLaw :
      (TerminalAudit.jointSettlement law
          (recoveryExclusionBase parameter (setup.program.parameterPaymentUtility valuation)
            (fun who => exitValuation who + exitTransfer who)) observe audit deposit).map
          (fun realized => (recoveryPaymentReadout setup leaks realized.1, realized.2)) =
        reference.map (fun readout => (readout,
          exclusionReadoutUtility setup parameter (setup.program.parameterPaymentUtility valuation)
            (fun who => exitValuation who + exitTransfer who) readout))) :
    (TerminalAudit.jointSettlement law
        (recoveryExclusionBase parameter
          (fun outcome who => setup.program.publicTransfers outcome.2 who) exitTransfer)
        observe audit deposit).map
        (fun realized => (recoveryPaymentReadout setup leaks realized.1, realized.2)) =
      reference.map (fun readout => (readout,
        exclusionReadoutUtility setup parameter
          (fun outcome who => setup.program.publicTransfers outcome.2 who)
          exitTransfer readout)) := by
  let sourceValuation := exclusionReadoutUtility setup parameter valuation exitValuation
  have baseAdd : recoveryExclusionBase (leaks := leaks) parameter
        (setup.program.parameterPaymentUtility valuation)
        (fun who => exitValuation who + exitTransfer who) =
      fun (state : (recoveryApplication (runtime setup) leaks).ProtocolState) who =>
        recoveryExclusionBase parameter valuation exitValuation state who +
        recoveryExclusionBase parameter
          (fun outcome owner => setup.program.publicTransfers outcome.2 owner) exitTransfer
          state who := by
    funext state who
    exact recoveryExclusionBase_add parameter valuation _ exitValuation exitTransfer state who
  have recovered := congrArg (PMF.map (receiptReadout sourceValuation)) utilityLaw
  rw [PMF.map_comp, baseAdd, TerminalAudit.jointSettlement_readout_sub_valuation law
    (recoveryExclusionBase parameter valuation exitValuation) _
    (recoveryPaymentReadout setup leaks) sourceValuation
    (recoveryExclusionBase_valuation_factors setup leaks parameter valuation exitValuation law
      exitCompatible)] at recovered
  rw [PMF.map_comp] at recovered
  exact recovered.trans (by
    congr 1
    funext readout
    apply Prod.ext
    · rfl
    · funext who
      change exclusionReadoutUtility setup parameter
          (fun outcome owner => valuation outcome owner +
            setup.program.publicTransfers outcome.2 owner)
          (fun owner => exitValuation owner + exitTransfer owner) readout who -
        exclusionReadoutUtility setup parameter valuation exitValuation readout who =
          exclusionReadoutUtility setup parameter
            (fun outcome owner => setup.program.publicTransfers outcome.2 owner)
            exitTransfer readout who
      rw [exclusionReadoutUtility_add setup parameter valuation
        (fun outcome owner => setup.program.publicTransfers outcome.2 owner)
        exitValuation exitTransfer]
      ring)

end Vegas
