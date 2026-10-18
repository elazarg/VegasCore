/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitTimingInformationAudit
import Vegas.Pending.PhaseCountedFiber
import Interaction.ReactiveMenuContinuation

/-! # Actual counted continuations against unchanged raw equilibrium strategies -/

noncomputable section

namespace Vegas.Examples.CommitTimingInformation

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement

variable {failure : Set.Ioo (0 : ℝ) 1}

theorem raw_terminal_state_law (profile : ∀ who, (rawModel failure).BehavioralPolicy who)
    (history : (rawProtocol failure).History) :
    ((rawModel failure).runBehavioralTerminalFrom (canonicalCertificate failure) profile
      history).map
      History.state = app.finish initial horizon (scheduler failure)
        (rawMenu.decodeProfile initial horizon (scheduler failure) profile) history.state := by
  rw [(rawModel failure).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
    (canonicalCertificate failure) (rawMenu.bounded initial horizon (scheduler failure))]
  apply rawMenu.run_eq_finish
  have bound := app.trace_bound initial horizon (scheduler failure)
    (rawMenu.toRawTrace initial horizon (scheduler failure) history.trace)
  change app.rank horizon history.state ≤ 2 * horizon + 1
  omega

/-- A whole count-correct focal deviation in the original raw game has exactly
the counted runner law against the unchanged assessed foreign strategies. -/
theorem raw_equilibrium_counted_deviation_run (loss : Player → ℝ)
    (strong : ∀ who, 1 < loss who)
    (assessment : (rawModel failure).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon (scheduler failure))
      (canonicalCertificate failure) (rawPayoff loss))
    (who : Player) (policy : app.Policy)
    (covered : ∀ past view response, response ∈ (policy past view).support →
      response ∈ countedMenu.actions who past view)
    (fuel : Nat) (history : (countedProtocol failure).History) :
    ((countedModel failure).runBehavioralFrom
      (Function.update (countedAssessmentProfile assessment) who
        (countedMenu.restrictPolicy initial horizon (scheduler failure) who policy)) fuel
          history).map
      (countedInRaw.history initial horizon (scheduler failure)) =
      (rawModel failure).runBehavioralFrom
        (Function.update assessment.strategy who
          (rawMenu.restrictPolicy initial horizon (scheduler failure) who policy)) fuel
        (countedInRaw.history initial horizon (scheduler failure) history) := by
  exact countedInRaw.runFrom_restrictPolicy initial horizon (scheduler failure)
    (countedAssessmentProfile assessment) assessment.strategy
    ((raw_equilibrium_extends_counted loss strong) assessment equilibrium) who policy covered
      fuel history

/-- Every supported raw continuation of that deviation has an actual counted
history with the same complete trace, not merely the same terminal payoff. -/
theorem raw_equilibrium_counted_deviation_support (loss : Player → ℝ)
    (strong : ∀ who, 1 < loss who)
    (assessment : (rawModel failure).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon (scheduler failure))
      (canonicalCertificate failure) (rawPayoff loss))
    (who : Player) (policy : app.Policy)
    (covered : ∀ past view response, response ∈ (policy past view).support →
      response ∈ countedMenu.actions who past view)
    (fuel : Nat) (history : (countedProtocol failure).History) (final : (rawProtocol
      failure).History)
    (supported : final ∈ ((rawModel failure).runBehavioralFrom
      (Function.update assessment.strategy who
        (rawMenu.restrictPolicy initial horizon (scheduler failure) who policy)) fuel
      (countedInRaw.history initial horizon (scheduler failure) history)).support) :
    ∃ retained : (countedProtocol failure).History,
      retained ∈ ((countedModel failure).runBehavioralFrom
        (Function.update (countedAssessmentProfile assessment) who
          (countedMenu.restrictPolicy initial horizon (scheduler failure) who policy)) fuel
            history).support ∧
      countedInRaw.history initial horizon (scheduler failure) retained = final := by
  rw [← (raw_equilibrium_counted_deviation_run loss strong) assessment equilibrium who policy
    covered
    fuel history, PMF.support_map] at supported
  exact supported

/-- The reflected counted support excludes future charges of every owner,
even under the focal whole-policy deviation and at originally off-path sites. -/
theorem raw_equilibrium_counted_deviation_charge_zero (loss : Player → ℝ)
    (strong : ∀ who, 1 < loss who)
    (assessment : (rawModel failure).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon (scheduler failure))
      (canonicalCertificate failure) (rawPayoff loss))
    (who : Player) (policy : app.Policy)
    (covered : ∀ past view response, response ∈ (policy past view).support →
      response ∈ countedMenu.actions who past view)
    (fuel : Nat) (history : (countedProtocol failure).History) (final : (rawProtocol
      failure).History)
    (supported : final ∈ ((rawModel failure).runBehavioralFrom
      (Function.update assessment.strategy who
        (rawMenu.restrictPolicy initial horizon (scheduler failure) who policy)) fuel
      (countedInRaw.history initial horizon (scheduler failure) history)).support) (owner :
        Player) :
    TerminalAudit.charge app.stateTraffic audit final.state owner = 0 := by
  obtain ⟨retained, _reached, same⟩ := (raw_equilibrium_counted_deviation_support loss strong)
    assessment
    equilibrium who policy covered fuel history final supported
  have clean := PhaseCount.onePacketMenu_countCharge_zero runtime leaks bounds initial horizon
    (scheduler failure) evidenceService retained owner
  have state := congrArg History.state same
  change TerminalAudit.charge app.stateTraffic audit retained.state owner = 0 at clean
  rw [← state]
  exact clean

/-- At settlement the same support statement holds for the original certified
terminal runner. The horizon is the native protocol's existing bound. -/
theorem raw_equilibrium_counted_deviation_terminal_support (loss : Player → ℝ)
    (strong : ∀ who, 1 < loss who)
    (assessment : (rawModel failure).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon (scheduler failure))
      (canonicalCertificate failure) (rawPayoff loss))
    (who : Player) (policy : app.Policy)
    (covered : ∀ past view response, response ∈ (policy past view).support →
      response ∈ countedMenu.actions who past view)
    (history : (countedProtocol failure).History) (final : (rawProtocol failure).History)
    (supported : final ∈ ((rawModel failure).runBehavioralTerminalFrom (canonicalCertificate
      failure)
      (Function.update assessment.strategy who
        (rawMenu.restrictPolicy initial horizon (scheduler failure) who policy))
      (countedInRaw.history initial horizon (scheduler failure) history)).support) :
    ∃ retained : (countedProtocol failure).History,
      countedInRaw.history initial horizon (scheduler failure) retained = final := by
  rw [(rawModel failure).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
    (canonicalCertificate failure)
    (rawMenu.bounded initial horizon (scheduler failure))] at supported
  obtain ⟨retained, _reached, same⟩ := (raw_equilibrium_counted_deviation_support loss strong)
    assessment
    equilibrium who policy covered _ history final supported
  exact ⟨retained, same⟩


/-- Every supported current raw choice at a retained site is the literal
image of a counted choice. The conclusion uses the full clean information
fiber, including histories to which the assessment assigns zero belief. -/
theorem raw_equilibrium_supported_choice_counted (loss : Player → ℝ)
    (strong : ∀ who, 1 < loss who)
    (assessment : (rawModel failure).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon (scheduler failure))
      (canonicalCertificate failure) (rawPayoff loss))
    (who : Player) (site : (countedModel failure).InformationSite who)
    (choice : (rawModel failure).Choice who site.1)
    (supported : choice ∈ (assessment.strategy who site.1).support) :
    ∃ retained : (countedModel failure).Choice who site.1,
      countedInRaw.choice initial horizon (scheduler failure) who site.1 retained = choice := by
  classical
  rcases site with ⟨info, decision⟩
  cases info with
  | none =>
      obtain ⟨_history, _running, action, permitted⟩ := decision
      change (some action : Option app.Action) = none at permitted
      cases permitted
  | some input =>
      rcases input with ⟨past, view⟩
      let site : (countedModel failure).InformationSite who := ⟨some (past, view), decision⟩
      let target := (countedInRaw.actionRestriction initial horizon (scheduler failure)).site
        who site
      obtain ⟨response, _allowed, selected⟩ := choice.2
      have decoded : response ∈ (rawMenu.decodeProfile initial horizon (scheduler failure)
          assessment.strategy who past view).support := by
        change response ∈ (app.decodePolicy
          (rawMenu.embedPolicy initial horizon (scheduler failure) who (assessment.strategy who))
            past view).support
        rw [ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy,
          PMF.map_comp, PMF.support_map]
        refine ⟨choice, supported, ?_⟩
        change choice.1.getD ⟨none⟩ = response
        rw [selected, Option.getD_some]
      have admitted := (raw_equilibrium_counted_site_covered loss strong) assessment
        equilibrium who site
        past view rfl response decoded
      refine ⟨⟨some response, response, admitted, rfl⟩, ?_⟩
      apply Subtype.ext
      exact selected.symm

open Classical in
/-- Forcing one retained choice commutes with the count restriction while
leaving every later assessed response unchanged. -/
theorem raw_equilibrium_extends_counted_commit (loss : Player → ℝ)
    (strong : ∀ who, 1 < loss who)
    (assessment : (rawModel failure).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon (scheduler failure))
      (canonicalCertificate failure) (rawPayoff loss))
    (who : Player) (site : (countedModel failure).InformationSite who)
    (choice : (countedModel failure).Choice who site.1) :
    (countedInRaw.actionRestriction initial horizon (scheduler failure)).ExtendsProfile
      (Function.update (countedAssessmentProfile assessment) who
        ((countedAssessmentProfile assessment who).commit site.1 choice))
      (Function.update assessment.strategy who
        ((assessment.strategy who).commit site.1
          (countedInRaw.choice initial horizon (scheduler failure) who site.1 choice))) := by
  classical
  intro owner original
  rcases original with ⟨info, decision⟩
  change (Function.update assessment.strategy who
      ((assessment.strategy who).commit site.1
        (countedInRaw.choice initial horizon (scheduler failure) who site.1 choice))) owner info =
    ((Function.update (countedAssessmentProfile assessment) who
      ((countedAssessmentProfile assessment who).commit site.1 choice)) owner info).map
        (countedInRaw.choice initial horizon (scheduler failure) owner info)
  by_cases sameOwner : owner = who
  · subst owner
    simp only [Function.update_self]
    by_cases sameInfo : info = site.1
    · subst info
      rw [BehavioralPolicy.commit_self, BehavioralPolicy.commit_self, PMF.pure_map]
    · have rawEqual := BehavioralPolicy.commit_of_ne (M := (rawModel failure))
        (assessment.strategy who) site.1
          (countedInRaw.choice initial horizon (scheduler failure) who site.1 choice) sameInfo
      have countedEqual := BehavioralPolicy.commit_of_ne (M := (countedModel failure))
        (countedAssessmentProfile assessment who) site.1 choice sameInfo
      exact rawEqual.trans (((raw_equilibrium_extends_counted loss strong) assessment
        equilibrium who
        ⟨info, decision⟩).trans (congrArg
          (fun law => law.map (countedInRaw.choice initial horizon (scheduler failure) who info))
            countedEqual).symm)
  · simp only [Function.update_of_ne sameOwner]
    exact (raw_equilibrium_extends_counted loss strong) assessment equilibrium owner ⟨info,
      decision⟩

open Classical in
/-- The actual forced-current raw runner is a counted runner with the same
complete physical histories. Its tail is the incumbent assessed strategy. -/
theorem raw_equilibrium_counted_commit_run (loss : Player → ℝ)
    (strong : ∀ who, 1 < loss who)
    (assessment : (rawModel failure).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon (scheduler failure))
      (canonicalCertificate failure) (rawPayoff loss))
    (who : Player) (site : (countedModel failure).InformationSite who)
    (choice : (countedModel failure).Choice who site.1) (fuel : Nat)
    (history : (countedProtocol failure).History) :
    ((countedModel failure).runBehavioralFrom
      (Function.update (countedAssessmentProfile assessment) who
        ((countedAssessmentProfile assessment who).commit site.1 choice)) fuel history).map
      (countedInRaw.history initial horizon (scheduler failure)) =
      (rawModel failure).runBehavioralFrom
        (Function.update assessment.strategy who
          ((assessment.strategy who).commit site.1
            (countedInRaw.choice initial horizon (scheduler failure) who site.1 choice))) fuel
        (countedInRaw.history initial horizon (scheduler failure) history) := by
  exact (countedInRaw.actionRestriction initial horizon (scheduler failure)).runFrom_law _ _
    ((raw_equilibrium_extends_counted_commit loss strong) assessment equilibrium who site
      choice) fuel history

open Classical in
/-- A supported current atom followed by the actual assessed continuation
has counted support. No globally count-correct incumbent policy is assumed. -/
theorem raw_equilibrium_supported_commit_support (loss : Player → ℝ)
    (strong : ∀ who, 1 < loss who)
    (assessment : (rawModel failure).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon (scheduler failure))
      (canonicalCertificate failure) (rawPayoff loss))
    (who : Player) (site : (countedModel failure).InformationSite who)
    (choice : (rawModel failure).Choice who site.1)
    (chosen : choice ∈ (assessment.strategy who site.1).support)
    (fuel : Nat) (history : (countedProtocol failure).History) (final : (rawProtocol
      failure).History)
    (supported : final ∈ ((rawModel failure).runBehavioralFrom
      (Function.update assessment.strategy who
        ((assessment.strategy who).commit site.1 choice)) fuel
      (countedInRaw.history initial horizon (scheduler failure) history)).support) :
    ∃ retained : (countedProtocol failure).History,
      countedInRaw.history initial horizon (scheduler failure) retained = final := by
  classical
  obtain ⟨retainedChoice, same⟩ := (raw_equilibrium_supported_choice_counted loss strong) assessment
    equilibrium who site choice chosen
  rw [← same, ← (raw_equilibrium_counted_commit_run loss strong) assessment equilibrium who site
    retainedChoice fuel history, PMF.support_map] at supported
  obtain ⟨retained, _reached, equal⟩ := supported
  exact ⟨retained, equal⟩

open Classical in
/-- The same reflection applies to the actual certified terminal runner
following a supported current choice and the unchanged assessed tail. -/
theorem raw_equilibrium_supported_commit_terminal_support (loss : Player → ℝ)
    (strong : ∀ who, 1 < loss who)
    (assessment : (rawModel failure).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon (scheduler failure))
      (canonicalCertificate failure) (rawPayoff loss))
    (who : Player) (site : (countedModel failure).InformationSite who)
    (choice : (rawModel failure).Choice who site.1)
    (chosen : choice ∈ (assessment.strategy who site.1).support)
    (history : (countedProtocol failure).History) (final : (rawProtocol failure).History)
    (supported : final ∈ ((rawModel failure).runBehavioralTerminalFrom (canonicalCertificate
      failure)
      (Function.update assessment.strategy who
        ((assessment.strategy who).commit site.1 choice))
      (countedInRaw.history initial horizon (scheduler failure) history)).support) :
    ∃ retained : (countedProtocol failure).History,
      countedInRaw.history initial horizon (scheduler failure) retained = final := by
  classical
  rw [(rawModel failure).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
    (canonicalCertificate failure)
    (rawMenu.bounded initial horizon (scheduler failure))] at supported
  exact (raw_equilibrium_supported_commit_support loss strong) assessment equilibrium who site
    choice
    chosen _ history final supported

end Vegas.Examples.CommitTimingInformation
