/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingPayoffs
import Vegas.Examples.CommitSeedSignallingCountedContinuation
import Vegas.Examples.CommitSeedSignallingRealization
import GameTheoryExtensions.Math.Probability.Expectation

/-! # Exact initialized native payoff from actual exclusion and failure events -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
  GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob)

/-- Completion and the zero count charge are derived from the genuine
initialized finite-menu run. No later action or successful delivery is assumed. -/
theorem initialized_counted_netPayoff_formula
    (profile : ∀ who, countedModel.BehavioralPolicy who) (final : app.Execution)
    (supported : final ∈ (app.runRounds scheduler
      (countedMenu.decodeProfile initial horizon scheduler profile) horizon
      initialExecution).support) (owner : Player) :
    netPayoff (app.finished final) owner =
      if owner ∈ final.application.current.excluded then -1 else
        if RecoveryState.publicationFailed final.application.current.native
          (revealEvent (opponent owner)) then 3 else 0 := by
  have covered (who : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
      (response : app.Action)
      (chosen : response ∈ (countedMenu.decodeProfile initial horizon scheduler profile
        who past view).support) : response ∈ countedMenu.actions who past view :=
    countedMenu.decode_embedPolicy_covered initial horizon scheduler who (profile who)
      past view response chosen
  obtain ⟨trace⟩ := countedMenu.trace_roundsFrom initial horizon scheduler
    (countedMenu.decodeProfile initial horizon scheduler profile) covered horizon le_rfl final
    (by simpa only [ReactiveApplication.roundsFrom, initial_eq_pure, PMF.pure_bind,
      initialExecution] using supported)
  have trace : countedProtocol.Trace (some ⟨0, none, final⟩) := by
    simpa only [Nat.sub_self] using trace
  have complete := scheduler_completesPlay ⟨0, none, final⟩
    (countedMenu.toRawTrace initial horizon scheduler trace) ⟨rfl, rfl⟩
  have zero := PhaseCount.onePacketMenu_countCharge_zero runtime leaks bounds initial horizon
    scheduler evidenceService ⟨some ⟨0, none, final⟩, trace⟩ owner
  change TerminalAudit.charge app.stateTraffic audit (some ⟨0, none, final⟩) owner = 0 at zero
  change basePayoff (some ⟨0, none, final⟩) owner -
    TerminalAudit.charge app.stateTraffic audit (some ⟨0, none, final⟩) owner * deposit owner = _
  rw [zero, zero_mul, sub_zero]
  exact basePayoff_terminal_formula ⟨0, none, final⟩ complete owner

/-- The actual initialized mean is reward times the joint event of own
survival and foreign failure, minus the probability of own exclusion. -/
theorem initialized_counted_netPayoff_expectation
    (profile : ∀ who, countedModel.BehavioralPolicy who) (owner : Player) :
    let law := app.runRounds scheduler
      (countedMenu.decodeProfile initial horizon scheduler profile) horizon initialExecution
    expect law (fun final => netPayoff (app.finished final) owner) =
      3 * (law.toOuterMeasure {final | owner ∉ final.application.current.excluded ∧
          RecoveryState.publicationFailed final.application.current.native
            (revealEvent (opponent owner)) = true}).toReal -
      (law.toOuterMeasure {final | owner ∈ final.application.current.excluded}).toReal := by
  classical
  let law := app.runRounds scheduler
    (countedMenu.decodeProfile initial horizon scheduler profile) horizon initialExecution
  let reward : Set app.Execution := {final | owner ∉ final.application.current.excluded ∧
    RecoveryState.publicationFailed final.application.current.native
      (revealEvent (opponent owner)) = true}
  let excluded : Set app.Execution := {final | owner ∈ final.application.current.excluded}
  have formula (final : app.Execution) (supported : final ∈ law.support) :
      netPayoff (app.finished final) owner =
        3 * (if final ∈ reward then 1 else 0) - if final ∈ excluded then 1 else 0 := by
    rw [initialized_counted_netPayoff_formula profile final supported owner]
    dsimp only [reward, excluded, Set.mem_ofPred_eq]
    by_cases gone : owner ∈ final.application.current.excluded
    · simp [gone]
    · by_cases failed : RecoveryState.publicationFailed final.application.current.native
          (revealEvent (opponent owner)) = true <;> simp [gone, failed]
  change expect law (fun final => netPayoff (app.finished final) owner) =
    3 * (law.toOuterMeasure reward).toReal - (law.toOuterMeasure excluded).toReal
  rw [expect_congr_on_support formula,
    expect_sub
      (payoffIntegrable_const_mul (payoffIntegrable_ite_one_zero law (· ∈ reward)))
      (payoffIntegrable_ite_one_zero law (· ∈ excluded)), expect_const_mul]
  have rewardMean : expect law (fun final => if final ∈ reward then (1 : ℝ) else 0) =
      (law.toOuterMeasure reward).toReal := by
    calc
      _ = expect law (fun final => @ite ℝ (final ∈ reward)
          (Classical.propDecidable _) 1 0) := by
        apply congrArg (expect law)
        funext final
        by_cases member : final ∈ reward <;> simp [member]
      _ = _ := expect_indicator law reward
  have excludedMean : expect law (fun final => if final ∈ excluded then (1 : ℝ) else 0) =
      (law.toOuterMeasure excluded).toReal := by
    calc
      _ = expect law (fun final => @ite ℝ (final ∈ excluded)
          (Classical.propDecidable _) 1 0) := by
        apply congrArg (expect law)
        funext final
        by_cases member : final ∈ excluded <;> simp [member]
      _ = _ := expect_indicator law excluded
  exact congrArg₂ (fun rewardMass excludedMass : ℝ => 3 * rewardMass - excludedMass)
    rewardMean excludedMean

end Vegas.Examples.CommitSeedSignalling
