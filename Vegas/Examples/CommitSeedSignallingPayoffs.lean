/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingLaws
import Vegas.Examples.CommitSeedSignallingService
import Vegas.Compile.EventGraphParameterReadout
import Vegas.Pending.PhaseFailureCoverage

/-! # Native publication readout and realized clean payoffs -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

def revealEvent (owner : Player) : graph.EventId :=
  if owner = alice then aliceReveal else bobReveal

theorem failedReveals_alice
    (source : Vegas.State simpleExpr program.terminalCtx) :
    failedReveals program alice (publicOutcome program source) =
      if (source.get (.there .here)).isSuccess then 0 else 1 := by
  classical
  have observed : (IExpr.ResultTypes.valueEquiv (L := simpleExpr) .bool)
      ((sourcePublicEnv source).get (publicRef
        (.there .here : HasVar program.terminalCtx 2 (.publication .bool)))) =
      source.get (.there .here) := by
    exact (congrArg (IExpr.ResultTypes.valueEquiv (L := simpleExpr) .bool)
      (sourcePublicEnv_get_publicRef source (.there .here))).trans
        ((IExpr.ResultTypes.valueEquiv (L := simpleExpr) .bool).apply_symm_apply _)
  cases value : source.get (.there .here) <;>
    simp [failedReveals, program, revealCells, RevealCell.failed, publicOutcome,
      observed, value, terminalRef, PublicationResult.isSuccess,
      OnePacketCommitRevealHypotheses.alice, OnePacketCommitRevealHypotheses.bob]

theorem failedReveals_bob
    (source : Vegas.State simpleExpr program.terminalCtx) :
    failedReveals program bob (publicOutcome program source) =
      if (source.get .here).isSuccess then 0 else 1 := by
  classical
  have observed : (IExpr.ResultTypes.valueEquiv (L := simpleExpr) .bool)
      ((sourcePublicEnv source).get (publicRef
        (.here : HasVar program.terminalCtx 3 (.publication .bool)))) = source.get .here := by
    exact (congrArg (IExpr.ResultTypes.valueEquiv (L := simpleExpr) .bool)
      (sourcePublicEnv_get_publicRef source .here)).trans
        ((IExpr.ResultTypes.valueEquiv (L := simpleExpr) .bool).apply_symm_apply _)
  cases value : source.get .here <;>
    simp [failedReveals, program, revealCells, RevealCell.failed, publicOutcome,
      observed, value, terminalRef, PublicationResult.isSuccess,
      OnePacketCommitRevealHypotheses.alice, OnePacketCommitRevealHypotheses.bob]

theorem readout_alice_publication (native : EventGraphRuntime.State graph)
    (source : Vegas.State simpleExpr program.terminalCtx)
    (decoded : decodeState? (terminalRefs program) native.config.store = some source) :
    RecoveryState.publicationFailed native aliceReveal =
      !(source.get (.there .here)).isSuccess := by
  have agree : (terminalRefs program).Agrees source native.config.store :=
    decodeState?_agrees (terminalRefs program) native.config.store source decoded
  have output : native.config.outputs aliceReveal = some (source.get (.there .here)) := by
    exact agree (.there .here)
  cases node : nodeView graph aliceReveal with
  | bind owner payload kind code => cases kind.symm.trans reveal_layouts.1
  | sample payload law kind code => cases kind.symm.trans reveal_layouts.1
  | resolve owner payload binding checks kind code =>
      have same := EventField.publication.inj (kind.symm.trans reveal_layouts.1)
      subst payload
      rw [RecoveryState.publicationFailed, node, output]
      cases source.get (.there .here) <;> rfl

theorem readout_bob_publication (native : EventGraphRuntime.State graph)
    (source : Vegas.State simpleExpr program.terminalCtx)
    (decoded : decodeState? (terminalRefs program) native.config.store = some source) :
    RecoveryState.publicationFailed native bobReveal = !(source.get .here).isSuccess := by
  have agree : (terminalRefs program).Agrees source native.config.store :=
    decodeState?_agrees (terminalRefs program) native.config.store source decoded
  have output : native.config.outputs bobReveal = some (source.get .here) := by
    exact agree .here
  cases node : nodeView graph bobReveal with
  | bind owner payload kind code => cases kind.symm.trans reveal_layouts.2
  | sample payload law kind code => cases kind.symm.trans reveal_layouts.2
  | resolve owner payload binding checks kind code =>
      have same := EventField.publication.inj (kind.symm.trans reveal_layouts.2)
      subst payload
      rw [RecoveryState.publicationFailed, node, output]
      cases source.get .here <;> rfl

/-- Utility is read from the actual native publication output, not an assumed
delivery payoff table. -/
theorem utility_eq_native_publication (native : EventGraphRuntime.State graph)
    (source : Vegas.State simpleExpr program.terminalCtx)
    (decoded : decodeState? (terminalRefs program) native.config.store = some source)
    (who : Player) : utility source who =
      if RecoveryState.publicationFailed native (revealEvent (opponent who)) then 3 else 0 := by
  fin_cases who
  · change (if failedReveals program bob (publicOutcome program source) = 0 then 0 else 3) =
      if RecoveryState.publicationFailed native bobReveal then 3 else 0
    rw [failedReveals_bob, readout_bob_publication native source decoded]
    cases source.get .here <;> rfl
  · change (if failedReveals program alice (publicOutcome program source) = 0 then 0 else 3) =
      if RecoveryState.publicationFailed native aliceReveal then 3 else 0
    rw [failedReveals_alice, readout_alice_publication native source decoded]
    cases source.get (.there .here) <;> rfl

/-- Completed native stores use permanent own exclusion and the opponent's
literal failed-publication bit. No converse exclusion invariant is assumed. -/
theorem basePayoff_terminal_formula (current : app.Control)
    (complete : current.execution.application.current.native.config.cut.Terminal)
    (who : Player) :
    basePayoff (some current) who =
      if who ∈ current.execution.application.current.excluded then -1 else
        if RecoveryState.publicationFailed current.execution.application.current.native
          (revealEvent (opponent who)) then 3 else 0 := by
  classical
  have available := phaseSourceReadout_succeeds setup .concurrentReveals runtime leaks
    current complete
  obtain ⟨source, read⟩ := Option.isSome_iff_exists.mp available
  have decoded : decodeState? (terminalRefs program)
      current.execution.application.current.native.config.store = some source := by
    change (if current.execution.application.current.native.config.cut.Terminal then
      decodeState? (terminalRefs program) current.execution.application.current.native.config.store
      else none) = some source at read
    rw [ite_eq_left complete] at read
    exact read
  change (if who ∈ current.execution.application.current.excluded then excludedPayoff who else
    (phaseSourceReadout setup .concurrentReveals runtime leaks (some current)).elim 0
      (fun terminal => utility terminal who)) = _
  rw [read]
  simp only [Option.elim_some, excludedPayoff, utility_eq_native_publication _ _ decoded]

theorem rawPayoff_terminal_formula (history : rawProtocol.History) (current : app.Control)
    (state : history.state = some current)
    (complete : current.execution.application.current.native.config.cut.Terminal)
    (who : Player) (clean : OwnPermitted who current.execution) :
    rawPayoff who history =
      if who ∈ current.execution.application.current.excluded then -1 else
        if RecoveryState.publicationFailed current.execution.application.current.native
          (revealEvent (opponent who)) then 3 else 0 := by
  classical
  have valid : ReactiveApplication.executionInvariant (OwnPermitted who) history.state := by
    rw [state]
    exact clean
  have zero := ownPermitted_charge_zero who history valid
  change basePayoff history.state who -
    TerminalAudit.charge app.stateTraffic audit history.state who * deposit who = _
  rw [zero, zero_mul, sub_zero, state]
  exact basePayoff_terminal_formula current complete who

theorem unexcluded_publication_not_failed (selected : app.Scheduler) (current : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some current)) (who : Player)
    (survives : who ∉ current.execution.application.current.excluded) :
    RecoveryState.publicationFailed current.execution.application.current.native
      (revealEvent who) = false := by
  classical
  have coverage := (phaseFailureCoverage_history runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon selected trace).active
  have acting : graph.actor? (revealEvent who) = some who := by
    fin_cases who <;> rfl
  cases flag : RecoveryState.publicationFailed current.execution.application.current.native
      (revealEvent who) with
  | false => rfl
  | true => exact (survives (coverage.covered (revealEvent who) who acting (Or.inr flag))).elim

/-- An actual surviving opponent leaves no gross reward, even when the
focal owner's own later play is arbitrary. -/
theorem basePayoff_le_zero_of_opponent_survives
    (selected : app.Scheduler) (current : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some current))
    (complete : current.execution.application.current.native.config.cut.Terminal)
    (who : Player) (survives : opponent who ∉ current.execution.application.current.excluded) :
    basePayoff (some current) who ≤ 0 := by
  classical
  rw [basePayoff_terminal_formula current complete who,
    unexcluded_publication_not_failed selected current trace (opponent who) survives]
  split <;> norm_num

theorem netPayoff_le_basePayoff (state : app.ProtocolState) (who : Player) :
    netPayoff state who ≤ basePayoff state who := by
  have nonnegative := (TerminalAudit.charge_mem_Icc app.stateTraffic audit state who).1
  change basePayoff state who - _ * deposit who ≤ _
  dsimp only [deposit]
  linarith

theorem netPayoff_le_zero_of_opponent_survives
    (selected : app.Scheduler) (current : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some current))
    (complete : current.execution.application.current.native.config.cut.Terminal)
    (who : Player) (survives : opponent who ∉ current.execution.application.current.excluded) :
    netPayoff (some current) who ≤ 0 :=
  (netPayoff_le_basePayoff _ who).trans
    (basePayoff_le_zero_of_opponent_survives selected current trace complete who survives)

end Vegas.Examples.CommitSeedSignalling
