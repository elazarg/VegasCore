/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastCountedFiber
import Interaction.ReactiveMenuContinuation

/-! # Actual counted continuations against unchanged raw equilibrium strategies -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement

theorem raw_terminal_state_law (profile : ∀ who, rawModel.BehavioralPolicy who)
    (history : rawProtocol.History) :
    (rawModel.runBehavioralTerminalFrom canonicalCertificate profile history).map
      History.state = app.finish initial horizon scheduler
        (rawMenu.decodeProfile initial horizon scheduler profile) history.state := by
  rw [rawModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
    canonicalCertificate (rawMenu.bounded initial horizon scheduler)]
  apply rawMenu.run_eq_finish
  have bound := app.trace_bound initial horizon scheduler
    (rawMenu.toRawTrace initial horizon scheduler history.trace)
  change app.rank horizon history.state ≤ 2 * horizon + 1
  omega

/-- A whole count-correct focal deviation in the original raw game has exactly
the counted runner law against the unchanged assessed foreign strategies. -/
theorem raw_equilibrium_counted_deviation_run
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (who : Player) (policy : app.Policy)
    (covered : ∀ past view response, response ∈ (policy past view).support →
      response ∈ countedMenu.actions who past view)
    (fuel : Nat) (history : countedProtocol.History) :
    (countedModel.runBehavioralFrom
      (Function.update (countedAssessmentProfile assessment) who
        (countedMenu.restrictPolicy initial horizon scheduler who policy)) fuel history).map
      (countedInRaw.history initial horizon scheduler) =
      rawModel.runBehavioralFrom
        (Function.update assessment.strategy who
          (rawMenu.restrictPolicy initial horizon scheduler who policy)) fuel
        (countedInRaw.history initial horizon scheduler history) := by
  exact countedInRaw.runFrom_restrictPolicy initial horizon scheduler
    (countedAssessmentProfile assessment) assessment.strategy
    (raw_equilibrium_extends_counted assessment equilibrium) who policy covered fuel history

/-- Every supported raw continuation of that deviation has an actual counted
history with the same complete trace, not merely the same terminal payoff. -/
theorem raw_equilibrium_counted_deviation_support
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (who : Player) (policy : app.Policy)
    (covered : ∀ past view response, response ∈ (policy past view).support →
      response ∈ countedMenu.actions who past view)
    (fuel : Nat) (history : countedProtocol.History) (final : rawProtocol.History)
    (supported : final ∈ (rawModel.runBehavioralFrom
      (Function.update assessment.strategy who
        (rawMenu.restrictPolicy initial horizon scheduler who policy)) fuel
      (countedInRaw.history initial horizon scheduler history)).support) :
    ∃ retained : countedProtocol.History,
      retained ∈ (countedModel.runBehavioralFrom
        (Function.update (countedAssessmentProfile assessment) who
          (countedMenu.restrictPolicy initial horizon scheduler who policy)) fuel history).support ∧
      countedInRaw.history initial horizon scheduler retained = final := by
  rw [← raw_equilibrium_counted_deviation_run assessment equilibrium who policy covered
    fuel history, PMF.support_map] at supported
  exact supported

/-- The reflected counted support excludes future charges of every owner,
even under the focal whole-policy deviation and at originally off-path sites. -/
theorem raw_equilibrium_counted_deviation_charge_zero
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (who : Player) (policy : app.Policy)
    (covered : ∀ past view response, response ∈ (policy past view).support →
      response ∈ countedMenu.actions who past view)
    (fuel : Nat) (history : countedProtocol.History) (final : rawProtocol.History)
    (supported : final ∈ (rawModel.runBehavioralFrom
      (Function.update assessment.strategy who
        (rawMenu.restrictPolicy initial horizon scheduler who policy)) fuel
      (countedInRaw.history initial horizon scheduler history)).support) (owner : Player) :
    TerminalAudit.charge app.stateTraffic audit final.state owner = 0 := by
  obtain ⟨retained, _reached, same⟩ := raw_equilibrium_counted_deviation_support assessment
    equilibrium who policy covered fuel history final supported
  have clean := PhaseCount.onePacketMenu_countCharge_zero runtime leaks bounds initial horizon
    scheduler evidenceService retained owner
  have state := congrArg History.state same
  change TerminalAudit.charge app.stateTraffic audit retained.state owner = 0 at clean
  rw [← state]
  exact clean

/-- At settlement the same support statement holds for the original certified
terminal runner. The horizon is the native protocol's existing bound. -/
theorem raw_equilibrium_counted_deviation_terminal_support
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (who : Player) (policy : app.Policy)
    (covered : ∀ past view response, response ∈ (policy past view).support →
      response ∈ countedMenu.actions who past view)
    (history : countedProtocol.History) (final : rawProtocol.History)
    (supported : final ∈ (rawModel.runBehavioralTerminalFrom canonicalCertificate
      (Function.update assessment.strategy who
        (rawMenu.restrictPolicy initial horizon scheduler who policy))
      (countedInRaw.history initial horizon scheduler history)).support) :
    ∃ retained : countedProtocol.History,
      countedInRaw.history initial horizon scheduler retained = final := by
  rw [rawModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded canonicalCertificate
    (rawMenu.bounded initial horizon scheduler)] at supported
  obtain ⟨retained, _reached, same⟩ := raw_equilibrium_counted_deviation_support assessment
    equilibrium who policy covered _ history final supported
  exact ⟨retained, same⟩


/-- Every supported current raw choice at a retained site is the literal
image of a counted choice. The conclusion uses the full clean information
fiber, including histories to which the assessment assigns zero belief. -/
theorem raw_equilibrium_supported_choice_counted
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (who : Player) (site : countedModel.InformationSite who)
    (choice : rawModel.Choice who site.1)
    (supported : choice ∈ (assessment.strategy who site.1).support) :
    ∃ retained : countedModel.Choice who site.1,
      countedInRaw.choice initial horizon scheduler who site.1 retained = choice := by
  classical
  rcases site with ⟨info, decision⟩
  cases info with
  | none =>
      obtain ⟨_history, _running, action, permitted⟩ := decision
      change (some action : Option app.Action) = none at permitted
      cases permitted
  | some input =>
      rcases input with ⟨past, view⟩
      let site : countedModel.InformationSite who := ⟨some (past, view), decision⟩
      let target := (countedInRaw.actionRestriction initial horizon scheduler).site who site
      obtain ⟨response, _allowed, selected⟩ := choice.2
      have decoded : response ∈ (rawMenu.decodeProfile initial horizon scheduler
          assessment.strategy who past view).support := by
        change response ∈ (app.decodePolicy
          (rawMenu.embedPolicy initial horizon scheduler who (assessment.strategy who))
            past view).support
        rw [ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy,
          PMF.map_comp, PMF.support_map]
        refine ⟨choice, supported, ?_⟩
        change choice.1.getD ⟨none⟩ = response
        rw [selected, Option.getD_some]
      have admitted := raw_equilibrium_counted_site_covered assessment equilibrium who site
        past view rfl response decoded
      refine ⟨⟨some response, response, admitted, rfl⟩, ?_⟩
      apply Subtype.ext
      exact selected.symm

open Classical in
/-- Forcing one retained choice commutes with the count restriction while
leaving every later assessed response unchanged. -/
theorem raw_equilibrium_extends_counted_commit
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (who : Player) (site : countedModel.InformationSite who)
    (choice : countedModel.Choice who site.1) :
    (countedInRaw.actionRestriction initial horizon scheduler).ExtendsProfile
      (Function.update (countedAssessmentProfile assessment) who
        ((countedAssessmentProfile assessment who).commit site.1 choice))
      (Function.update assessment.strategy who
        ((assessment.strategy who).commit site.1
          (countedInRaw.choice initial horizon scheduler who site.1 choice))) := by
  classical
  intro owner original
  rcases original with ⟨info, decision⟩
  change (Function.update assessment.strategy who
      ((assessment.strategy who).commit site.1
        (countedInRaw.choice initial horizon scheduler who site.1 choice))) owner info =
    ((Function.update (countedAssessmentProfile assessment) who
      ((countedAssessmentProfile assessment who).commit site.1 choice)) owner info).map
        (countedInRaw.choice initial horizon scheduler owner info)
  by_cases sameOwner : owner = who
  · subst owner
    simp only [Function.update_self]
    by_cases sameInfo : info = site.1
    · subst info
      rw [BehavioralPolicy.commit_self, BehavioralPolicy.commit_self, PMF.pure_map]
    · have rawEqual := BehavioralPolicy.commit_of_ne (M := rawModel)
        (assessment.strategy who) site.1
          (countedInRaw.choice initial horizon scheduler who site.1 choice) sameInfo
      have countedEqual := BehavioralPolicy.commit_of_ne (M := countedModel)
        (countedAssessmentProfile assessment who) site.1 choice sameInfo
      exact rawEqual.trans ((raw_equilibrium_extends_counted assessment equilibrium who
        ⟨info, decision⟩).trans (congrArg
          (fun law => law.map (countedInRaw.choice initial horizon scheduler who info))
            countedEqual).symm)
  · simp only [Function.update_of_ne sameOwner]
    exact raw_equilibrium_extends_counted assessment equilibrium owner ⟨info, decision⟩

open Classical in
/-- The actual forced-current raw runner is a counted runner with the same
complete physical histories. Its tail is the incumbent assessed strategy. -/
theorem raw_equilibrium_counted_commit_run
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (who : Player) (site : countedModel.InformationSite who)
    (choice : countedModel.Choice who site.1) (fuel : Nat)
    (history : countedProtocol.History) :
    (countedModel.runBehavioralFrom
      (Function.update (countedAssessmentProfile assessment) who
        ((countedAssessmentProfile assessment who).commit site.1 choice)) fuel history).map
      (countedInRaw.history initial horizon scheduler) =
      rawModel.runBehavioralFrom
        (Function.update assessment.strategy who
          ((assessment.strategy who).commit site.1
            (countedInRaw.choice initial horizon scheduler who site.1 choice))) fuel
        (countedInRaw.history initial horizon scheduler history) := by
  exact (countedInRaw.actionRestriction initial horizon scheduler).runFrom_law _ _
    (raw_equilibrium_extends_counted_commit assessment equilibrium who site choice) fuel history

open Classical in
/-- A supported current atom followed by the actual assessed continuation
has counted support. No globally count-correct incumbent policy is assumed. -/
theorem raw_equilibrium_supported_commit_support
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (who : Player) (site : countedModel.InformationSite who)
    (choice : rawModel.Choice who site.1)
    (chosen : choice ∈ (assessment.strategy who site.1).support)
    (fuel : Nat) (history : countedProtocol.History) (final : rawProtocol.History)
    (supported : final ∈ (rawModel.runBehavioralFrom
      (Function.update assessment.strategy who
        ((assessment.strategy who).commit site.1 choice)) fuel
      (countedInRaw.history initial horizon scheduler history)).support) :
    ∃ retained : countedProtocol.History,
      countedInRaw.history initial horizon scheduler retained = final := by
  classical
  obtain ⟨retainedChoice, same⟩ := raw_equilibrium_supported_choice_counted assessment
    equilibrium who site choice chosen
  rw [← same, ← raw_equilibrium_counted_commit_run assessment equilibrium who site
    retainedChoice fuel history, PMF.support_map] at supported
  obtain ⟨retained, _reached, equal⟩ := supported
  exact ⟨retained, equal⟩

open Classical in
/-- The same reflection applies to the actual certified terminal runner
following a supported current choice and the unchanged assessed tail. -/
theorem raw_equilibrium_supported_commit_terminal_support
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (who : Player) (site : countedModel.InformationSite who)
    (choice : rawModel.Choice who site.1)
    (chosen : choice ∈ (assessment.strategy who site.1).support)
    (history : countedProtocol.History) (final : rawProtocol.History)
    (supported : final ∈ (rawModel.runBehavioralTerminalFrom canonicalCertificate
      (Function.update assessment.strategy who
        ((assessment.strategy who).commit site.1 choice))
      (countedInRaw.history initial horizon scheduler history)).support) :
    ∃ retained : countedProtocol.History,
      countedInRaw.history initial horizon scheduler retained = final := by
  classical
  rw [rawModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded canonicalCertificate
    (rawMenu.bounded initial horizon scheduler)] at supported
  exact raw_equilibrium_supported_commit_support assessment equilibrium who site choice
    chosen _ history final supported

end Vegas.Examples.CommitSeedBroadcast
