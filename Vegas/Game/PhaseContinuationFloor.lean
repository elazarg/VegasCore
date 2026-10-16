/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseLocalValueContinuation
import Vegas.Pending.PhaseServiceContract

/-! # Exclusion floors for arbitrary actual phase continuations -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (menu : (phaseApplication runtime leaks).ResponseMenu)
  (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "P" => phaseApplication runtime leaks
local notation "M" => menu.information initial horizon scheduler
local notation "E" => menu.protocol initial horizon scheduler

omit [Fintype Player] in
/-- The original all-history completion contract makes every actual terminal
payoff at least the exclusion floor, whether play has retried or excluded anyone. -/
theorem phase_terminal_payoff_lower
    (completes : PhaseService.CompletesPlay runtime leaks initial horizon scheduler)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (below : ∀ terminal owner, excludedPayoff owner ≤ utility terminal owner)
    (who : Player) (final : (E).History) (terminal : (E).terminal final.state) :
    excludedPayoff who ≤
      phaseExclusionBase setup mode runtime leaks utility excludedPayoff final.state who := by
  cases state : final.state with
  | none =>
      rw [state] at terminal
      exact terminal.elim
  | some control =>
      have complete := completes control
        ((menu).toRawTrace initial horizon scheduler (state ▸ final.trace)) (state ▸ terminal)
      by_cases excluded : who ∈ control.execution.application.current.excluded
      · rw [phaseExclusionBase_of_excluded setup mode runtime leaks utility
          excludedPayoff control who excluded]
      · rw [phaseExclusionBase_eq_readout setup mode runtime leaks utility
          excludedPayoff control who excluded]
        have succeeds := phaseSourceReadout_succeeds setup mode runtime leaks control complete
        cases readout : phaseSourceReadout setup mode runtime leaks (some control) with
        | none => simp only [readout, Option.isSome_none, Bool.false_eq_true] at succeeds
        | some value => simpa only [readout, Option.elim_some] using below value who

open Classical in
/-- Every whole replacement policy at an actual assessment site retains the
same floor. Silence keeps its full later continuation; no source tail or
canonical-consistency hypothesis is needed. -/
theorem phase_continuation_value_lower
    (completes : PhaseService.CompletesPlay runtime leaks initial horizon scheduler)
    (assessment : (M).BehavioralAssessment) (who : Player) (site : (M).InformationSite who)
    (alternative : (M).BehavioralPolicy who)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (below : ∀ terminal owner, excludedPayoff owner ≤ utility terminal owner)
    (B : ℝ) (nonnegative : 0 ≤ B)
    (utilityBound : ∀ terminal, |utility terminal who| ≤ B)
    (excludedBound : |excludedPayoff who| ≤ B) :
    excludedPayoff who ≤
      (assessment.continuationContext
        ((menu).bounded initial horizon scheduler).wellFoundedHistories site (fun final =>
          phaseExclusionBase setup mode runtime leaks utility excludedPayoff
          final.state who)).value alternative := by
  let payoff := fun final : (E).History =>
    phaseExclusionBase setup mode runtime leaks utility excludedPayoff final.state who
  have bounded : ∀ final, |payoff final| ≤ B := by
    intro final
    cases state : final.state with
    | none => simpa only [payoff, state, phaseExclusionBase, abs_zero] using nonnegative
    | some control =>
        by_cases excluded : who ∈ control.execution.application.current.excluded
        · simpa only [payoff, state, phaseExclusionBase_of_excluded setup mode runtime leaks
            utility excludedPayoff control who excluded] using excludedBound
        · rw [show payoff final = _ from congrArg
            (fun state => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
              state who) state]
          rw [phaseExclusionBase_eq_readout setup mode runtime leaks utility
            excludedPayoff control who excluded]
          cases readout : phaseSourceReadout setup mode runtime leaks (some control) with
          | none => simpa only [Option.elim_none, abs_zero] using nonnegative
          | some value => exact utilityBound value
  let certificate := ((menu).bounded initial horizon scheduler).wellFoundedHistories
  have terminal := assessment.continuationContext_support_terminal certificate site
    payoff alternative
  have integrable := assessment.continuationContext_integrable_of_bounded_terminal
    certificate site payoff B (fun final _ => bounded final) alternative
  have lower := expect_mono
    (fun final supported => phase_terminal_payoff_lower setup mode runtime leaks menu initial
      horizon scheduler completes utility excludedPayoff below who final
      (terminal final supported)) (payoffIntegrable_constant _ (excludedPayoff who)) integrable
  change excludedPayoff who ≤ expect
    ((assessment.continuationContext certificate site payoff).outcome alternative) payoff
  simpa only [expect_constant] using lower

open Classical in
/-- Any local lottery, including waiting and arbitrary legal fresh handles,
has a nonnegative actual continuation surplus over permanent exclusion. -/
theorem phase_localValue_lower
    (completes : PhaseService.CompletesPlay runtime leaks initial horizon scheduler)
    (assessment : (M).BehavioralAssessment) (who : Player) (site : (M).InformationSite who)
    (law : PMF ((M).Choice who site.1))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (below : ∀ terminal owner, excludedPayoff owner ≤ utility terminal owner)
    (B : ℝ) (nonnegative : 0 ≤ B)
    (utilityBound : ∀ terminal, |utility terminal who| ≤ B)
    (excludedBound : |excludedPayoff who| ≤ B) :
    excludedPayoff who ≤ localValue (2 * horizon + 1)
      (fun final : (E).History => final.state)
      (phaseExclusionBase setup mode runtime leaks utility excludedPayoff) assessment site law := by
  classical
  rw [localValue_eq_continuationContext _ _ _ _ _
    ((menu).bounded initial horizon scheduler)]
  exact phase_continuation_value_lower setup mode runtime leaks menu initial horizon scheduler
    completes assessment who site ((assessment.strategy who).withLaw site.1 law) utility
    excludedPayoff below B nonnegative utilityBound excludedBound

end Vegas
