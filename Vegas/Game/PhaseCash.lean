/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.EventGraphCash
import Vegas.Game.SequentialPaymentValuation

/-! # Physical phase cash and quasi-linear audited utility

Cash is read from the actual current native configuration and actual excluded
set. Integer program settlement agrees pointwise with its source reader, then
casts to the existing real audit base. Arbitrary real deposits and correlated
verdicts remain in the actual terminal settlement kernel.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Enforcement GameTheory.Math.Probability
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))

/-- The real interpretation of source integer settlement changes no branch. -/
theorem sourceCash_cast (excluded : Finset Player)
    (terminal : Option (State L setup.program.terminalCtx)) (who : Player) :
    (setup.cash excluded terminal who : ℝ) =
      if who ∈ excluded then (setup.exitTransfers who : ℝ) else
        terminal.elim 0 (fun state => setup.program.publicTransfers
          (setup.program.publicOutcome state) who) := by
  by_cases exited : who ∈ excluded
  · simp only [Setup.cash, exited, ite_true]
  · simp only [Setup.cash, exited, ite_false]
    cases terminal with
    | none => simp only [Option.elim_none, Int.cast_zero]
    | some state => rfl

/-- Actual physical cash uses the surviving current configuration, never a
retired archive or a source failed-reveal counter. -/
def phaseCash (state : (phaseApplication runtime leaks).ProtocolState) (who : Player) : Int :=
  match state with
  | none => 0
  | some control => compiledCash setup mode control.execution.application.current.excluded
      control.execution.application.current.native.config who

/-- Source and physical compiled settlement agree on every protocol state. -/
theorem phaseCash_eq_source (state : (phaseApplication runtime leaks).ProtocolState)
    (who : Player) :
    phaseCash setup mode runtime leaks state who = match state with
      | none => 0
      | some control => setup.cash control.execution.application.current.excluded
          (phaseSourceReadout setup mode runtime leaks (some control)) who := by
  cases state with
  | none => rfl
  | some control =>
    exact compiledCash_eq_source setup mode control.execution.application.current.excluded
      control.execution.application.current.native.config who

/-- Casting physical integer cash gives the original audit cash base, with
exit money fixed by the source setup's declared integer field. -/
theorem phaseCash_cast_eq_base :
    (fun state who => (phaseCash setup mode runtime leaks state who : ℝ)) =
      phaseExclusionBase setup mode runtime leaks
        (fun terminal who => setup.program.publicTransfers (setup.program.publicOutcome terminal)
          who) (fun who => (setup.exitTransfers who : ℝ)) := by
  funext state who
  rw [phaseCash_eq_source]
  cases state with
  | none => simp only [phaseExclusionBase, Int.cast_zero]
  | some control =>
    exact sourceCash_cast setup control.execution.application.current.excluded
      (phaseSourceReadout setup mode runtime leaks (some control)) who

/-- Actual audited monetary receipts evaluate to the existing quasi-linear
utility, including arbitrary correlated charges and real-valued deposits. -/
theorem phaseCash_expect_monetaryUtility
    (valuation : State L setup.program.terminalCtx → Player → ℝ)
    (exitValuation : Player → ℝ) {Observation : Type}
    (observe : (phaseApplication runtime leaks).ProtocolState → Observation)
    (audit : Observation → PMF (Player → Bool)) (deposit : Player → ℝ)
    (state : (phaseApplication runtime leaks).ProtocolState) (who : Player) :
    expect (TerminalAudit.settlement
        (fun current owner => (phaseCash setup mode runtime leaks current owner : ℝ))
        observe audit deposit state)
      (fun receipts => monetaryUtility
        (phaseExclusionBase setup mode runtime leaks valuation exitValuation)
        (state, receipts) who) =
      TerminalAudit.utility (phaseExclusionBase setup mode runtime leaks
        (fun terminal owner => valuation terminal owner + setup.program.publicTransfers
          (setup.program.publicOutcome terminal) owner)
        (fun owner => exitValuation owner + (setup.exitTransfers owner : ℝ)))
        observe audit deposit state who := by
  rw [phaseCash_cast_eq_base]
  exact phaseExclusionBase_expect_monetaryUtility setup mode runtime leaks valuation exitValuation
    (fun owner => (setup.exitTransfers owner : ℝ)) observe audit deposit state who

end Vegas
