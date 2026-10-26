/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPaymentValuation

/-! # Monetary inversion of the phase runtime's retained source readout

The cash reader uses the same completed typed store as utility preservation.
At excluded states its valuation must agree with the declared exit valuation;
this is automatic on unexcluded support. No audit cleanliness is required.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Enforcement GameTheory.Math.Probability
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))

/-- Only excluded supported states require an additional valuation identity.
The absent terminal reader retains its existing zero valuation. -/
theorem phaseExclusionBase_valuation_factors
    (valuation : State L setup.program.terminalCtx → Player → ℝ)
    (exitValuation : Player → ℝ) (law : PMF (phaseApplication runtime leaks).ProtocolState)
    (exitCompatible : ∀ control, some control ∈ law.support → ∀ who,
      who ∈ control.execution.application.current.excluded →
      exitValuation who = (phaseSourceReadout setup mode runtime leaks (some control)).elim 0
        (fun terminal => valuation terminal who)) :
    ∀ state ∈ law.support,
      phaseExclusionBase setup mode runtime leaks valuation exitValuation state =
        fun who => (phaseSourceReadout setup mode runtime leaks state).elim 0
          (fun terminal => valuation terminal who) := by
  intro state supported
  funext who
  cases state with
  | none => rfl
  | some control =>
    by_cases excluded : who ∈ control.execution.application.current.excluded
    · rw [phaseExclusionBase_of_excluded setup mode runtime leaks valuation exitValuation
        control who excluded]
      exact exitCompatible control supported who excluded
    · simp only [phaseExclusionBase, excluded, ite_false]

/-- The exact retained joint cash law follows from the utility law. The same
physical audit is used, including all correlations between verdicts. -/
theorem phase_jointCashLaw_of_utility_law {Observation : Type}
    (valuation transfer : State L setup.program.terminalCtx → Player → ℝ)
    (exitValuation exitTransfer : Player → ℝ)
    (law : PMF (phaseApplication runtime leaks).ProtocolState)
    (reference : PMF (Option (State L setup.program.terminalCtx) × (Player → ℝ)))
    (exitCompatible : ∀ control, some control ∈ law.support → ∀ who,
      who ∈ control.execution.application.current.excluded →
      exitValuation who = (phaseSourceReadout setup mode runtime leaks (some control)).elim 0
        (fun terminal => valuation terminal who))
    (observe : (phaseApplication runtime leaks).ProtocolState → Observation)
    (audit : Observation → PMF (Player → Bool)) (deposit : Player → ℝ)
    (utilityLaw :
      (TerminalAudit.jointSettlement law
        (phaseExclusionBase setup mode runtime leaks
          (fun terminal who => valuation terminal who + transfer terminal who)
          (fun who => exitValuation who + exitTransfer who)) observe audit deposit).map
        (fun realized => (phaseSourceReadout setup mode runtime leaks realized.1, realized.2)) =
        reference.map (utilityReadout (fun readout who =>
          readout.elim 0 (fun terminal => valuation terminal who)))) :
    (TerminalAudit.jointSettlement law
      (phaseExclusionBase setup mode runtime leaks transfer exitTransfer) observe audit deposit).map
      (fun realized => (phaseSourceReadout setup mode runtime leaks realized.1, realized.2)) =
        reference := by
  have baseAdd : phaseExclusionBase setup mode runtime leaks
      (fun terminal who => valuation terminal who + transfer terminal who)
      (fun who => exitValuation who + exitTransfer who) =
      fun state who =>
        phaseExclusionBase setup mode runtime leaks valuation exitValuation state who +
          phaseExclusionBase setup mode runtime leaks transfer exitTransfer state who := by
    funext state who
    exact phaseExclusionBase_add setup mode runtime leaks valuation transfer exitValuation
      exitTransfer state who
  rw [baseAdd] at utilityLaw
  exact TerminalAudit.jointSettlement_readout_eq_of_utility_law law
    (phaseExclusionBase setup mode runtime leaks valuation exitValuation) _
    (phaseSourceReadout setup mode runtime leaks) _
    (phaseExclusionBase_valuation_factors setup mode runtime leaks valuation exitValuation law
      exitCompatible) observe audit deposit reference utilityLaw

end Vegas
