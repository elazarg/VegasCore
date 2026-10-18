/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastProperBindingRecords
import Vegas.Examples.CommitSeedBroadcastRealization
import Vegas.Examples.CommitSeedBroadcastService
import Vegas.Compile.EventGraphParameterReadout
import Vegas.Pending.PhaseFailureCoverage

/-! # Actual terminal publication readout and fixed-exclusion payoffs -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement

def terminalPublicationRef (owner : Player) :
    HasVar program.terminalCtx (owner.val + 3) (.publication .bool) := by
  rcases owner with ⟨value, bounded⟩
  match value with
  | 0 => exact .there (.there .here)
  | 1 => exact .there .here
  | 2 => exact .here
  | n + 3 => omega

theorem failedReveals_eq_cell (source : Vegas.State simpleExpr program.terminalCtx)
    (owner : Player) :
    failedReveals program owner (publicOutcome program source) =
      if (source.get (terminalPublicationRef owner)).isSuccess then 0 else 1 := by
  classical
  have observed : (IExpr.ResultTypes.valueEquiv (L := simpleExpr) .bool)
      ((sourcePublicEnv source).get (publicRef (terminalPublicationRef owner))) =
        source.get (terminalPublicationRef owner) := by
    exact (congrArg (IExpr.ResultTypes.valueEquiv (L := simpleExpr) .bool)
      (sourcePublicEnv_get_publicRef source (terminalPublicationRef owner))).trans
        ((IExpr.ResultTypes.valueEquiv (L := simpleExpr) .bool).apply_symm_apply _)
  fin_cases owner <;> dsimp only [terminalPublicationRef] at observed
  · cases value : source.get (.there (.there .here)) <;>
      simp [failedReveals, program, revealCells, RevealCell.failed, publicOutcome,
        observed, value, terminalRef, terminalPublicationRef, PublicationResult.isSuccess,
        alice, bob, carol]
  · cases value : source.get (.there .here) <;>
      simp [failedReveals, program, revealCells, RevealCell.failed, publicOutcome,
        observed, value, terminalRef, terminalPublicationRef, PublicationResult.isSuccess,
        alice, bob, carol]
  · cases value : source.get .here <;>
      simp [failedReveals, program, revealCells, RevealCell.failed, publicOutcome,
        observed, value, terminalRef, terminalPublicationRef, PublicationResult.isSuccess,
        alice, bob, carol]

/-- The decoded source publication is the literal native failed-publication bit. -/
theorem readout_publication (native : EventGraphRuntime.State graph)
    (source : Vegas.State simpleExpr program.terminalCtx)
    (decoded : decodeState? (terminalRefs program) native.config.store = some source)
    (owner : Player) :
    RecoveryState.publicationFailed native (revealEvent owner) =
      !(source.get (terminalPublicationRef owner)).isSuccess := by
  have agree : (terminalRefs program).Agrees source native.config.store :=
    decodeState?_agrees (terminalRefs program) native.config.store source decoded
  have output : native.config.outputs (revealEvent owner) = some
      (cast (congrArg EventField.Value (revealEvent_layout owner).symm)
        (source.get (terminalPublicationRef owner))) := by
    fin_cases owner
    · exact agree (.there (.there .here))
    · exact agree (.there .here)
    · exact agree .here
  cases node : nodeView graph (revealEvent owner) with
  | bind author payload kind code => cases kind.symm.trans (revealEvent_layout owner)
  | sample payload law kind code => cases kind.symm.trans (revealEvent_layout owner)
  | resolve author payload binding checks kind code =>
      have same := EventField.publication.inj (kind.symm.trans (revealEvent_layout owner))
      subst payload
      rw [RecoveryState.publicationFailed, node, output]
      simp only [cast_cast, cast_eq]
      cases source.get (terminalPublicationRef owner) <;> rfl

theorem failedReveals_pos_iff_native (native : EventGraphRuntime.State graph)
    (source : Vegas.State simpleExpr program.terminalCtx)
    (decoded : decodeState? (terminalRefs program) native.config.store = some source)
    (owner : Player) :
    0 < failedReveals program owner (publicOutcome program source) ↔
      RecoveryState.publicationFailed native (revealEvent owner) = true := by
  rw [failedReveals_eq_cell, readout_publication native source decoded owner]
  cases source.get (terminalPublicationRef owner) <;> simp [PublicationResult.isSuccess]

theorem utility_eq_native_publication (native : EventGraphRuntime.State graph)
    (source : Vegas.State simpleExpr program.terminalCtx)
    (decoded : decodeState? (terminalRefs program) native.config.store = some source)
    (owner : Player) :
    utility source owner =
      if ∃ other : Player, other ≠ owner ∧
        RecoveryState.publicationFailed native (revealEvent other) = true then 1 else 0 := by
  classical
  unfold utility grossUtility
  congr 1
  apply propext
  constructor
  · rintro ⟨other, foreign, failed⟩
    exact ⟨other, foreign, (failedReveals_pos_iff_native native source decoded other).mp failed⟩
  · rintro ⟨other, foreign, failed⟩
    exact ⟨other, foreign, (failedReveals_pos_iff_native native source decoded other).mpr failed⟩

theorem basePayoff_terminal_formula (current : app.Control)
    (complete : current.execution.application.current.native.config.cut.Terminal)
    (owner : Player) :
    basePayoff (some current) owner =
      if owner ∈ current.execution.application.current.excluded then -(3 / 2) else
        if ∃ other : Player, other ≠ owner ∧
          RecoveryState.publicationFailed current.execution.application.current.native
            (revealEvent other) = true then 1 else 0 := by
  classical
  obtain ⟨source, read⟩ := Option.isSome_iff_exists.mp
    (phaseSourceReadout_succeeds setup .concurrentReveals runtime leaks current complete)
  have decoded : decodeState? (terminalRefs program)
      current.execution.application.current.native.config.store = some source := by
    change (if current.execution.application.current.native.config.cut.Terminal then
      decodeState? (terminalRefs program) current.execution.application.current.native.config.store
      else none) = some source at read
    rw [ite_eq_left complete] at read
    exact read
  change (if owner ∈ current.execution.application.current.excluded then excludedPayoff owner else
    (phaseSourceReadout setup .concurrentReveals runtime leaks (some current)).elim 0
      (fun terminal => utility terminal owner)) = _
  rw [read]
  simp only [Option.elim_some, excludedPayoff, utility_eq_native_publication _ _ decoded]

theorem rawPayoff_terminal_formula (history : rawProtocol.History) (current : app.Control)
    (state : history.state = some current)
    (complete : current.execution.application.current.native.config.cut.Terminal)
    (owner : Player) (clean : OwnPermitted owner current.execution) :
    rawPayoff owner history =
      if owner ∈ current.execution.application.current.excluded then -(3 / 2) else
        if ∃ other : Player, other ≠ owner ∧
          RecoveryState.publicationFailed current.execution.application.current.native
            (revealEvent other) = true then 1 else 0 := by
  have valid : ReactiveApplication.executionInvariant (OwnPermitted owner) history.state := by
    rw [state]
    exact clean
  have zero := ownPermitted_charge_zero owner history valid
  change basePayoff history.state owner -
    TerminalAudit.charge app.stateTraffic audit history.state owner * deposit owner = _
  rw [zero, zero_mul, sub_zero, state]
  exact basePayoff_terminal_formula current complete owner

theorem unexcluded_publication_not_failed (selected : app.Scheduler) (current : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some current)) (owner : Player)
    (survives : owner ∉ current.execution.application.current.excluded) :
    RecoveryState.publicationFailed current.execution.application.current.native
      (revealEvent owner) = false := by
  have compiledTrace := trace
  rw [initial_eq_compiled] at compiledTrace
  have coverage := (phaseFailureCoverage_history runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon selected compiledTrace).active
  cases flag : RecoveryState.publicationFailed current.execution.application.current.native
      (revealEvent owner) with
  | false => rfl
  | true =>
      exact (survives (coverage.covered (revealEvent owner) owner
        (reveal_actor owner) (Or.inr flag))).elim

theorem netPayoff_le_basePayoff (state : app.ProtocolState) (owner : Player) :
    netPayoff state owner ≤ basePayoff state owner := by
  have nonnegative := (TerminalAudit.charge_mem_Icc app.stateTraffic audit state owner).1
  change basePayoff state owner - _ * deposit owner ≤ _
  dsimp only [deposit]
  linarith

/-- If every other owner survives, even arbitrary focal play has nonpositive payoff. -/
theorem netPayoff_le_zero_of_others_survive
    (selected : app.Scheduler) (current : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some current))
    (complete : current.execution.application.current.native.config.cut.Terminal)
    (owner : Player)
    (survives : ∀ other, other ≠ owner → other ∉ current.execution.application.current.excluded) :
    netPayoff (some current) owner ≤ 0 := by
  classical
  have noneFailed : ¬ ∃ other : Player, other ≠ owner ∧
      RecoveryState.publicationFailed current.execution.application.current.native
        (revealEvent other) = true := by
    rintro ⟨other, foreign, failed⟩
    rw [unexcluded_publication_not_failed selected current trace other (survives other foreign)]
      at failed
    cases failed
  apply (netPayoff_le_basePayoff _ owner).trans
  rw [basePayoff_terminal_formula current complete owner, ite_eq_right noneFailed]
  split <;> norm_num

end Vegas.Examples.CommitSeedBroadcast
