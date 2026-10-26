/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourcePhaseGame
import Vegas.Game.TerminalObservation
import GameTheory.Core.Approximate

/-! # Monetary observations of the full source phase game

The observable game keeps every source strategy and deviation. A history
valuation may be read from the common terminal observation when it factors
there on completed paths. The factorization is explicit and need not hold on
unfinished paths. No finiteness or integrability premise is added.
This is source outcome recoding, not a native strategy correspondence.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- The source reader retains the complete terminal store and actual declared
cash vector, with the same initial-input and public-result readers as runtime. -/
def sourcePhaseObservation (history : setup.commitRecoveryProtocol.History) :
    TerminalObservation setup :=
  TerminalObservation.read setup
    (history.state.bind fun state => ProtocolState.readout setup.program state.point)
    (fun who => (setup.sourcePhaseCash history who : ℝ))

/-- Exact Nash recoding with every source unilateral deviation retained.
Only completed-path valuation factorization is needed, and expectation guards
are transported rather than replaced by an integrability assumption. -/
theorem sourcePhaseObservation_isεNash_iff [Fintype Player]
    (valuation : setup.commitRecoveryProtocol.History → Player → ℝ)
    (retained : TerminalObservation setup → Player → ℝ)
    (factors : ∀ history : setup.commitRecoveryProtocol.History,
      setup.commitRecoveryProtocol.terminal history.state →
        ∀ who, valuation history who = retained (setup.sourcePhaseObservation history) who)
    (ε : ℝ) (profile : Profile (setup.sourcePhaseGame valuation).form.sig) :
    IsεNash ((setup.sourcePhaseGame valuation).form.mapOutcome setup.sourcePhaseObservation)
        (fun observation who => retained observation who + observation.netPayoffs who)
        ε profile ↔
      IsεNash (setup.sourcePhaseGame valuation).form
        (setup.sourcePhaseGame valuation).utility ε profile := by
  let form := (setup.sourcePhaseGame valuation).form
  let observed := fun observation : TerminalObservation setup => fun who =>
    retained observation who + observation.netPayoffs who
  have same (policies : Profile form.sig) (who : Player)
      (history : setup.commitRecoveryProtocol.History)
      (supported : history ∈ (form.play policies).support) :
      observed (setup.sourcePhaseObservation history) who =
        (setup.sourcePhaseGame valuation).utility history who := by
    change retained (setup.sourcePhaseObservation history) who +
      (setup.sourcePhaseCash history who : ℝ) =
        valuation history who + (setup.sourcePhaseCash history who : ℝ)
    exact congrArg (· + (setup.sourcePhaseCash history who : ℝ))
      (factors history (setup.sourcePhaseGame_terminal valuation policies history supported)
        who).symm
  have expectations (policies : Profile form.sig) (who : Player) :
      UtilityHasExpectation observed who
          ((form.play policies).map setup.sourcePhaseObservation) ↔
        UtilityHasExpectation (setup.sourcePhaseGame valuation).utility who
          (form.play policies) := by
    rw [UtilityHasExpectation, hasExpectation_map_iff]
    exact hasExpectation_congr_on_support (same policies who)
  have values (policies : Profile form.sig) (who : Player) :
      extendedExpectedUtility observed who
          ((form.play policies).map setup.sourcePhaseObservation) =
        extendedExpectedUtility (setup.sourcePhaseGame valuation).utility who
          (form.play policies) := by
    rw [extendedExpectedUtility_map]
    exact extendedExpect_congr_on_support (same policies who)
  change IsεNash (form.mapOutcome setup.sourcePhaseObservation) observed ε profile ↔
    IsεNash form (setup.sourcePhaseGame valuation).utility ε profile
  rw [isεNash_iff, isεNash_iff]
  refine forall_congr' fun who => forall_congr' fun replacement => ?_
  rw [expectations, expectations, values, values]
  exact Iff.rfl

end Vegas.SourceProgram.Setup
