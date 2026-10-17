/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingIncentives
import Interaction.ReactiveMenuContinuation

/-! # Actual clean continuations against the assessed raw strategies -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

abbrev countedProtocol := countedMenu.protocol initial horizon scheduler
abbrev countedModel := countedMenu.information initial horizon scheduler

theorem countedInRaw : countedMenu.IncludedIn rawMenu :=
  PhaseCount.onePacketMenu_in_raw runtime leaks bounds

/-- Every genuine counted decision has a clean own recalled record, even if
its probability under the assessed raw profile is zero. -/
theorem counted_site_ownPastPermitted (who : Player)
    (site : countedModel.InformationSite who) (past : List app.PlayerEntry)
    (view : app.PlayerView) (atSite : site.1 = some (past, view)) :
    ownPastPermitted past := by
  classical
  obtain ⟨history, _running, _action, _permitted⟩ := site.2
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state)
    history.1.trace
  have observed : app.observe who history.1.state = some (past, view) :=
    (countedMenu.info initial horizon scheduler who history.1.trace).symm.trans
      (history.2.trans atSite)
  cases state : history.1.state with
  | none => simp [ReactiveApplication.observe, state] at observed
  | some control =>
      rw [state] at clean
      by_cases active : control.actor = some who
      · have pair := Option.some.inj (by
          simpa only [ReactiveApplication.observe, state, active, ite_true] using observed)
        have recallEq : control.execution.recall who = past := congrArg Prod.fst pair
        have own : OwnPermitted who control.execution :=
          ⟨clean.1, fun message member _ => clean.2 message member⟩
        rw [← recallEq]
        exact (ownPermitted_iff_past who control.execution clean.1).mp own
      · simp [ReactiveApplication.observe, state, active] at observed

/-- The decoded actual raw strategy is supported in the count menu at every
genuine counted site. This is inferred from sequential rationality, rather
than imposed on the foreign continuation. -/
theorem raw_equilibrium_counted_site_covered
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (who : Player) (site : countedModel.InformationSite who)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (atSite : site.1 = some (past, view)) (response : app.Action)
    (supported : response ∈ (rawMenu.decodeProfile initial horizon scheduler assessment.strategy
      who past view).support) : response ∈ countedMenu.actions who past view := by
  classical
  rcases site with ⟨info, decision⟩
  dsimp only at atSite
  subst info
  let source : countedModel.InformationSite who := ⟨some (past, view), decision⟩
  let target := (countedInRaw.actionRestriction initial horizon scheduler).site who source
  have clean := counted_site_ownPastPermitted who source past view rfl
  change response ∈ (app.decodePolicy
    (rawMenu.embedPolicy initial horizon scheduler who (assessment.strategy who))
      past view).support at supported
  rw [ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy,
    PMF.map_comp, PMF.support_map] at supported
  obtain ⟨choice, chosen, value⟩ := supported
  change choice.1.getD ⟨none⟩ = response at value
  obtain ⟨physical, _available, physicalEq⟩ := choice.2
  rw [physicalEq, Option.getD_some] at value
  have selected : choice.1 = some response := physicalEq.trans (congrArg some value)
  exact clean_supported_response_counted assessment equilibrium who target past view rfl
    clean choice chosen response selected

/-- Restrict the actual decoded strategy. The default branch is irrelevant at
genuine counted decision sites by the preceding support theorem. -/
def countedAssessmentProfile (assessment : rawModel.BehavioralAssessment)
    (who : Player) : countedModel.BehavioralPolicy who :=
  countedMenu.restrictPolicy initial horizon scheduler who
    (rawMenu.decodeProfile initial horizon scheduler assessment.strategy who)

private theorem decoded_profile_map_some (assessment : rawModel.BehavioralAssessment)
    (who : Player) (past : List app.PlayerEntry) (view : app.PlayerView) :
    (rawMenu.decodeProfile initial horizon scheduler assessment.strategy who past view).map some =
      (assessment.strategy who (some (past, view))).map Subtype.val := by
  have encoded := congrFun (app.encode_decodePolicy
    (rawMenu.embedPolicy initial horizon scheduler who (assessment.strategy who)))
      (some (past, view))
  have projected := congrArg (fun law => law.map Subtype.val) encoded
  simpa only [ReactiveApplication.encodePolicy,
    ReactiveApplication.ResponseMenu.decodeProfile,
    ReactiveApplication.ResponseMenu.embedPolicy, PMF.map_comp, Function.comp_def,
    ReactiveApplication.ResponseMenu.rawChoice] using projected

/-- The assessed raw strategy extends this counted profile on all retained
sites, including genuine sites that are off path under both profiles. -/
theorem raw_equilibrium_extends_counted
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff) :
    (countedInRaw.actionRestriction initial horizon scheduler).ExtendsProfile
      (countedAssessmentProfile assessment) assessment.strategy := by
  classical
  rintro who ⟨info, decision⟩
  cases info with
  | none =>
      obtain ⟨_history, _running, action, permitted⟩ := decision
      change (some action : Option app.Action) = none at permitted
      cases permitted
  | some input =>
      rcases input with ⟨past, view⟩
      let site : countedModel.InformationSite who := ⟨some (past, view), decision⟩
      have covered (response : app.Action)
          (supported : response ∈ (rawMenu.decodeProfile initial horizon scheduler
            assessment.strategy who past view).support) :
          response ∈ countedMenu.actions who past view :=
        raw_equilibrium_counted_site_covered assessment equilibrium who site past view rfl
          response supported
      apply pmf_map_injective (f := Subtype.val)
      · exact Subtype.val_injective
      · calc
          _ = (rawMenu.decodeProfile initial horizon scheduler assessment.strategy
              who past view).map some :=
            (decoded_profile_map_some assessment who past view).symm
          _ = (countedAssessmentProfile assessment who (some (past, view))).map Subtype.val :=
            (countedMenu.restrictPolicy_map_val initial horizon scheduler who _ past view
              covered).symm
          _ = _ := by rw [PMF.map_comp]; rfl

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
      have admitted := clean_supported_response_counted assessment equilibrium who target
        past view rfl (counted_site_ownPastPermitted who site past view rfl)
        choice supported response selected
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

end Vegas.Examples.CommitSeedSignalling
