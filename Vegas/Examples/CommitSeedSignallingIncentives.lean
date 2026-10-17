/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingAudit
import Vegas.Examples.CommitSeedSignallingInformation
import Vegas.Examples.CommitSeedSignallingLaws

/-! # Whole-player incentive bounds on clean native information fibers -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

theorem raw_terminal_state_law (profile : ∀ who, rawModel.BehavioralPolicy who)
    (history : rawProtocol.History) :
    (rawModel.runBehavioralTerminalFrom canonicalCertificate profile history).map
      History.state =
        app.finish initial horizon scheduler
          (rawMenu.decodeProfile initial horizon scheduler profile) history.state := by
  classical
  rw [rawModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
    canonicalCertificate (rawMenu.bounded initial horizon scheduler)]
  apply rawMenu.run_eq_finish
  have bound := app.trace_bound initial horizon scheduler
    (rawMenu.toRawTrace initial horizon scheduler history.trace)
  change app.rank horizon history.state ≤ 2 * horizon + 1
  omega

/-- Equality of the actual physical control suffices for the whole continuation
law. No unique proof object for the past trace is required. -/
theorem aliceFirst_context_state_law (assessment : rawModel.BehavioralAssessment)
    (alternative : rawModel.BehavioralPolicy alice) :
    ((assessment.continuationContext canonicalCertificate aliceFirstSite
      (rawPayoff alice)).outcome alternative).map History.state =
        app.finish initial horizon scheduler
          (rawMenu.decodeProfile initial horizon scheduler
            (Profile.update (sig := rawModel.behavioralSignature)
              assessment.strategy alice alternative))
          (some ⟨63, some alice, aliceFirst⟩) := by
  classical
  change ((assessment.belief alice aliceFirstSite).bind fun history =>
    rawModel.runBehavioralTerminalFrom canonicalCertificate
      (Profile.update (sig := rawModel.behavioralSignature)
        assessment.strategy alice alternative) history.1).map History.state = _
  rw [PMF.map_bind]
  calc
    _ = (assessment.belief alice aliceFirstSite).bind (fun _ =>
        app.finish initial horizon scheduler
          (rawMenu.decodeProfile initial horizon scheduler
            (Profile.update (sig := rawModel.behavioralSignature)
              assessment.strategy alice alternative))
          (some ⟨63, some alice, aliceFirst⟩)) := by
      apply bind_congr_on_support
      intro history _
      rw [raw_terminal_state_law, aliceFirst_information_state]
    _ = _ := PMF.bind_const _ _

theorem aliceFirst_context_value_eq_finish (assessment : rawModel.BehavioralAssessment)
    (alternative : rawModel.BehavioralPolicy alice) :
    (assessment.continuationContext canonicalCertificate aliceFirstSite
      (rawPayoff alice)).value alternative =
        expect (app.finish initial horizon scheduler
          (rawMenu.decodeProfile initial horizon scheduler
            (Profile.update (sig := rawModel.behavioralSignature)
              assessment.strategy alice alternative))
          (some ⟨63, some alice, aliceFirst⟩))
          (fun state => netPayoff state alice) := by
  classical
  rw [← aliceFirst_context_state_law assessment alternative, expect_map]
  rfl

theorem finish_initial_eq_aliceFirst (players : Player → app.Policy) :
    app.finish initial horizon scheduler players none =
      app.finish initial horizon scheduler players (some ⟨63, some alice, aliceFirst⟩) := by
  classical
  have first : app.round scheduler players initialExecution =
      app.resume players (some alice) aliceFirst := by
    rw [first_round_integrated]
    rfl
  simp only [ReactiveApplication.finish, initial_eq_pure, PMF.pure_bind]
  change (app.runRounds scheduler players (63 + 1) initialExecution).map app.finished = _
  rw [ReactiveApplication.runRounds, first]

/-- The initial expected payoff is the first callback's actual continuation
value for every assessment belief on that callback's full information fiber. -/
theorem initialized_value_eq_aliceFirst_context
    (assessment : rawModel.BehavioralAssessment) :
    expect (rawModel.runBehavioralTerminalFrom canonicalCertificate assessment.strategy
      rawProtocol.initHistory) (rawPayoff alice) =
      (assessment.continuationContext canonicalCertificate aliceFirstSite
        (rawPayoff alice)).value (assessment.strategy alice) := by
  classical
  rw [aliceFirst_context_value_eq_finish, Profile.update_eq_self]
  calc
    _ = expect ((rawModel.runBehavioralTerminalFrom canonicalCertificate assessment.strategy
        rawProtocol.initHistory).map History.state) (fun state => netPayoff state alice) :=
      (expect_map _ _ _).symm
    _ = _ := by
      rw [raw_terminal_state_law]
      change expect (app.finish initial horizon scheduler
        (rawMenu.decodeProfile initial horizon scheduler assessment.strategy) none)
        (fun state => netPayoff state alice) = _
      rw [finish_initial_eq_aliceFirst]

theorem preservation_implies_aliceFirst_zero
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (assessment : rawModel.BehavioralAssessment)
    (preserves : sourceJointLaw source = nativeJointLaw assessment.strategy) :
    (assessment.continuationContext canonicalCertificate aliceFirstSite
      (rawPayoff alice)).value (assessment.strategy alice) = 0 := by
  classical
  rw [← initialized_value_eq_aliceFirst_context]
  exact preservation_implies_zero_payoff source assessment.strategy preserves alice

theorem ownPermitted_informationHistory (who : Player)
    (site : rawModel.InformationSite who) (past : List app.PlayerEntry)
    (view : app.PlayerView) (atSite : site.1 = some (past, view))
    (clean : ownPastPermitted past) (history : rawModel.InformationHistory who site.1) :
    ReactiveApplication.executionInvariant (OwnPermitted who) history.1.state := by
  classical
  have observed := (rawMenu.info initial horizon scheduler who history.1.trace).symm.trans
    (history.2.trans atSite)
  cases state : history.1.state with
  | none => trivial
  | some control =>
      by_cases active : control.actor = some who
      · simp only [ReactiveApplication.observe, state, active, ↓reduceIte] at observed
        have pair : (control.execution.recall who, control.execution.observe app who) =
            (past, view) := by
          exact Option.some.inj observed
        change OwnPermitted who control.execution
        apply (ownPermitted_iff_past who control.execution
          (PhaseCount.countRecall_history runtime leaks
            (state ▸ rawMenu.toRawTrace initial horizon scheduler history.1.trace))).mpr
        have recallEq : control.execution.recall who = past := congrArg Prod.fst pair
        rw [recallEq]
        exact clean
      · simp [ReactiveApplication.observe, state, active] at observed

theorem silentContinuation_context_lower (assessment : rawModel.BehavioralAssessment)
    (who : Player) (site : rawModel.InformationSite who)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (atSite : site.1 = some (past, view)) (clean : ownPastPermitted past) :
    -1 ≤ (assessment.continuationContext canonicalCertificate site (rawPayoff who)).value
      (silentContinuation who) := by
  classical
  have integrable := assessment.continuationContext_integrable_of_bounded_terminal
    canonicalCertificate site (rawPayoff who) 6
    (fun final _ => rawPayoff_abs_le who final) (silentContinuation who)
  change -1 ≤ (assessment.continuationContextWith
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site (rawPayoff who)).value
      (silentContinuation who)
  rw [assessment.continuationContextWith_value_tower
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site
    (rawPayoff who) (silentContinuation who) integrable]
  have conditionalIntegrable := payoffIntegrable_expect_of_bounded
    (assessment.belief who site)
    (fun history : rawModel.InformationHistory who site.1 =>
      rawModel.runBehavioralTerminalFrom canonicalCertificate
        (Profile.update (sig := rawModel.behavioralSignature)
          assessment.strategy who (silentContinuation who)) history.1)
    (rawPayoff who) (by norm_num : (0 : ℝ) ≤ 6) (rawPayoff_abs_le who)
  have lower := expect_mono (μ := assessment.belief who site)
    (f := fun _ => (-1 : ℝ))
    (g := fun history => expect
      (rawModel.runBehavioralTerminalFrom canonicalCertificate
        (Profile.update (sig := rawModel.behavioralSignature)
          assessment.strategy who (silentContinuation who)) history.1)
      (rawPayoff who))
    (fun history _ => silentContinuation_payoff_lower assessment.strategy who history.1
      (ownPermitted_informationHistory who site past view atSite clean history))
    (payoffIntegrable_constant _ _) conditionalIntegrable
  simpa only [expect_constant] using lower

/-- Whole-policy sequential rationality, rather than WAIT followed by an
arbitrary incumbent tail, supplies the clean player's outside option. -/
theorem clean_context_value_lower (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (who : Player) (site : rawModel.InformationSite who)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (atSite : site.1 = some (past, view)) (clean : ownPastPermitted past) :
    -1 ≤ (assessment.continuationContext canonicalCertificate site (rawPayoff who)).value
      (assessment.strategy who) := by
  classical
  have integrable (alternative : rawModel.BehavioralPolicy who) :=
    assessment.continuationContext_integrable_of_bounded_terminal
      canonicalCertificate site (rawPayoff who) 6
      (fun final _ => rawPayoff_abs_le who final) alternative
  have compare := (Context.isLocallyOptimal_iff_of_integrable
    (integrable (assessment.strategy who)) (fun alternative _ => integrable alternative)).mp
    (equilibrium.1 who site)
  exact (silentContinuation_context_lower assessment who site past view atSite clean).trans
    (compare (silentContinuation who) (Set.mem_univ _))

open Classical in
/-- Every positive current atom inherits the whole-policy outside-option
bound. This remains valid when the site's belief assigns zero mass to some
compatible private preparations. -/
theorem clean_supported_choice_value_lower (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (who : Player) (site : rawModel.InformationSite who)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (atSite : site.1 = some (past, view)) (clean : ownPastPermitted past)
    (choice : rawModel.Choice who site.1)
    (supported : choice ∈ (assessment.strategy who site.1).support) :
    -1 ≤ (assessment.continuationContext canonicalCertificate site (rawPayoff who)).value
      ((assessment.strategy who).commit site.1 choice) := by
  classical
  have factor := rawModel.runnerFactorsAt_terminal canonicalCertificate
    (rawMenu.decisionRecall initial horizon scheduler).actsOnceWhereItMatters
    (rawMenu.informationSite_allNonterminal initial horizon scheduler who site)
  have same := assessment.supported_choice_value
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site factor
    (rawPayoff who) (equilibrium.1 who site)
    (assessment.continuationContext_integrable_of_bounded_terminal
      canonicalCertificate site (rawPayoff who) 6
      (fun final _ => rawPayoff_abs_le who final) (assessment.strategy who)) choice supported
  change -1 ≤ (assessment.continuationContextWith
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site (rawPayoff who)).value
      ((assessment.strategy who).commit site.1 choice)
  rw [same]
  exact clean_context_value_lower assessment equilibrium who site past view atSite clean

/-- On any clean full-input fiber, a supported physical response belongs to
the actual count-filtered menu. No restriction is asserted after a sunk charge. -/
theorem clean_supported_response_counted (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (who : Player) (site : rawModel.InformationSite who)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (atSite : site.1 = some (past, view)) (clean : ownPastPermitted past)
    (choice : rawModel.Choice who site.1)
    (supported : choice ∈ (assessment.strategy who site.1).support)
    (response : app.Action) (selected : choice.1 = some response) :
    response ∈ countedMenu.actions who past view := by
  classical
  have available : response ∈ rawMenu.actions who past view := by
    have member : (some response : Option app.Action) ∈ rawModel.menu who site.1 :=
      selected ▸ choice.2
    rw [atSite] at member
    obtain ⟨action, permitted, equal⟩ := member
    have same : action = response := Option.some.inj equal.symm
    simpa only [same] using permitted
  by_contra absent
  obtain ⟨material, sent, forbidden⟩ := PhaseCount.onePacket_extra runtime leaks bounds
    who past view response available absent
  have rawSelected : choice.1 = some ⟨some material⟩ := by
    rw [selected]
    congr 1
    cases response
    cases sent
    rfl
  exact no_forbidden_supported_of_ownPastPermitted assessment equilibrium who site past view
    atSite clean choice material rawSelected forbidden supported

/-- The first actual callback has no already collected own deposit. -/
theorem aliceFirst_context_value_lower (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff) :
    -1 ≤ (assessment.continuationContext canonicalCertificate aliceFirstSite
      (rawPayoff alice)).value (assessment.strategy alice) := by
  classical
  apply clean_context_value_lower assessment equilibrium alice aliceFirstSite
    (aliceFirst.recall alice) (aliceFirst.observe app alice) rfl
  rw [aliceFirst_recall]
  intro message member
  exact (List.not_mem_nil member).elim

/-- Absence of Alice's first packet leaves Bob's own original audit record empty. -/
theorem bobQuiet_context_value_lower (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff) :
    -1 ≤ (assessment.continuationContext canonicalCertificate bobQuietSite
      (rawPayoff bob)).value (assessment.strategy bob) := by
  classical
  apply clean_context_value_lower assessment equilibrium bob bobQuietSite
    ((bobFirst ⟨none⟩).recall bob) ((bobFirst ⟨none⟩).observe app bob) rfl
  rw [bobFirst_recall]
  intro message member
  exact (List.not_mem_nil member).elim

theorem aliceFirst_supported_response_counted
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (choice : rawModel.Choice alice aliceFirstSite.1)
    (supported : choice ∈ (assessment.strategy alice aliceFirstSite.1).support)
    (response : app.Action) (selected : choice.1 = some response) :
    response ∈ countedMenu.actions alice (aliceFirst.recall alice)
      (aliceFirst.observe app alice) := by
  classical
  apply clean_supported_response_counted assessment equilibrium alice aliceFirstSite
    (aliceFirst.recall alice) (aliceFirst.observe app alice) rfl _ choice supported
    response selected
  rw [aliceFirst_recall]
  intro message member
  exact (List.not_mem_nil member).elim

theorem bobQuiet_supported_response_counted
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (choice : rawModel.Choice bob bobQuietSite.1)
    (supported : choice ∈ (assessment.strategy bob bobQuietSite.1).support)
    (response : app.Action) (selected : choice.1 = some response) :
    response ∈ countedMenu.actions bob ((bobFirst ⟨none⟩).recall bob)
      ((bobFirst ⟨none⟩).observe app bob) := by
  classical
  apply clean_supported_response_counted assessment equilibrium bob bobQuietSite
    ((bobFirst ⟨none⟩).recall bob) ((bobFirst ⟨none⟩).observe app bob) rfl _ choice supported
    response selected
  rw [bobFirst_recall]
  intro message member
  exact (List.not_mem_nil member).elim

end Vegas.Examples.CommitSeedSignalling
