/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseExclusionPayoff
import Interaction.ReactiveOwnPlay

/-! # Whole-policy neutrality at actual phased excluded-owner information sites -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))


/-- Focal permanent exclusion is read directly from the complete actual local
input. The other owners may remain active and retain nonconstant payoffs. -/
def PhaseExcludedInput (who : Player) (input : (phaseApplication runtime leaks).Info) : Prop :=
  ∃ past view, input = some (past, view) ∧ who ∈ view.application.2.excluded

omit [Fintype Player] in
theorem phaseExcluded_of_information
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (who : Player)
    (input : (menu.information initial horizon scheduler).InfoState who)
    (flagged : PhaseExcludedInput setup mode runtime leaks who input)
    (history : (menu.information initial horizon scheduler).InformationHistory who input) :
    PhaseExcluded setup mode runtime leaks who history.1.state := by
  obtain ⟨past, view, atSite, excluded⟩ := flagged
  have observed := (menu.info initial horizon scheduler who history.1.trace).symm.trans
    (history.2.trans atSite)
  cases state : history.1.state with
  | none => rw [state] at observed; cases observed
  | some control =>
      rw [state] at observed
      by_cases active : control.actor = some who
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at observed
        have flags := congrArg (fun input => input.2.application.2.excluded)
          (Option.some.inj observed)
        change control.execution.application.current.excluded = view.application.2.excluded at flags
        change who ∈ control.execution.application.current.excluded
        rw [flags]
        exact excluded
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at observed
        cases observed

variable (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
  (menu : (phaseApplication runtime leaks).ResponseMenu)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  (certificate : (menu.protocol initial horizon scheduler).WellFoundedHistories)


local notation "N" => menu.information initial horizon scheduler
local notation "E" => menu.protocol initial horizon scheduler
local notation "base" => phaseExclusionBase setup mode runtime leaks utility excludedPayoff

/-- Every supported outcome from the whole actual information fiber has the
same focal payoff under every whole continuation policy. -/
theorem phase_excluded_context_payoff (assessment : (N).BehavioralAssessment)
    (who : Player) (site : (N).InformationSite who)
    (flagged : PhaseExcludedInput setup mode runtime leaks who site.1)
    (alternative : (N).BehavioralPolicy who) (final : (E).History)
    (supported : final ∈
      ((assessment.continuationContext certificate site
        (fun final : (E).History => base final.state who)).outcome
        alternative).support) : base final.state who = excludedPayoff who := by
  change final ∈ ((assessment.belief who site).bind fun history =>
    (N).runBehavioralTerminalFrom certificate
      (Profile.update (sig := (N).behavioralSignature) assessment.strategy who alternative)
        history.1).support at supported
  rw [PMF.support_bind] at supported
  obtain ⟨history, _member, child⟩ := Set.mem_iUnion₂.mp supported
  exact phase_excluded_terminal_payoff setup mode runtime leaks utility excludedPayoff menu
    initial horizon scheduler certificate _ who history.1
      (phaseExcluded_of_information setup mode runtime leaks menu initial horizon scheduler
        who site.1 flagged history) final child

theorem phase_excluded_context_value (assessment : (N).BehavioralAssessment)
    (who : Player) (site : (N).InformationSite who)
    (flagged : PhaseExcludedInput setup mode runtime leaks who site.1)
    (alternative : (N).BehavioralPolicy who) :
    (assessment.continuationContext certificate site
      (fun final : (E).History => base final.state who)).value
      alternative = excludedPayoff who := by
  change expect _ (fun final : (E).History => base final.state who) = _
  rw [expect_congr_on_support (g := fun _ => excludedPayoff who)
    (phase_excluded_context_payoff setup mode runtime leaks utility excludedPayoff menu
      initial horizon scheduler certificate assessment who site flagged alternative)]
  exact expect_constant _ _

theorem phase_excluded_sequentiallyRationalAt (assessment : (N).BehavioralAssessment)
    (who : Player) (site : (N).InformationSite who)
    (flagged : PhaseExcludedInput setup mode runtime leaks who site.1) :
    assessment.IsSequentiallyRationalAt site
      (assessment.continuationContext certificate site
        (fun final : (E).History => base final.state who)) := by
  have integrable (alternative : (N).BehavioralPolicy who) :
      (assessment.continuationContext certificate site
        (fun final : (E).History => base final.state who)).IntegrableAt
        alternative := by
    apply payoffIntegrable_of_bounded_on_support (C := |excludedPayoff who|)
    intro final supported
    change |base final.state who| ≤ |excludedPayoff who|
    rw [phase_excluded_context_payoff setup mode runtime leaks utility excludedPayoff menu
      initial horizon scheduler certificate assessment who site flagged alternative final supported]
  apply (Context.isLocallyOptimal_iff_of_integrable (integrable (assessment.strategy who))
    (fun alternative _ => integrable alternative)).mpr
  intro alternative _
  rw [phase_excluded_context_value setup mode runtime leaks utility excludedPayoff menu initial
    horizon scheduler certificate assessment who site flagged alternative,
    phase_excluded_context_value setup mode runtime leaks utility excludedPayoff menu initial
      horizon scheduler certificate assessment who site flagged (assessment.strategy who)]

end Vegas
