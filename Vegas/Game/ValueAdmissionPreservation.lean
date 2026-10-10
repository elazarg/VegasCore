/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProtocolValueBindingContinuation
import Vegas.Source.BindingRepairContinuation
import Vegas.Source.ValueBindingAdmission
import Vegas.Source.SetupProtocolRecall
import Vegas.Game.SourceInformation
import GameTheoryExtensions.Analysis.Protocol.PassageRestrictionExtension

/-! # Sequential equilibrium under commitment admission -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
variable (setup : Setup (Player := Player) (L := L))

/-- A focal full-admission source deviation against copied opponents is dominated at
any retained decision by one legal values-only continuation. -/
theorem exists_values_admission_continuation_ge [Fintype Player] [setup.FiniteInitialLaw]
    (admission : CommitmentInterface setup.program) (finite : setup.program.FiniteBindingTypes)
    (who : Player) (profile : BehavioralProfile setup.program)
    (values : ∀ player, ValueBinding setup.program (profile player))
    (target : ∀ player, (setup.informationModel admission).BehavioralPolicy player)
    (copies : (setup.valuesRestriction admission).ExtendsProfile
      (fun player => setup.toProtocolBehavioralPolicy
        (CommitmentInterface.values setup.program) player (profile player)
          ((values player).admitted setup.program (profile player)
            (CommitmentInterface.values setup.program))) target)
    (deviation : (setup.informationModel admission).BehavioralPolicy who)
    (sourceCertificate : (setup.executionProtocol
      (CommitmentInterface.values setup.program)).WellFoundedHistories)
    (targetCertificate : (setup.executionProtocol admission).WellFoundedHistories)
    (site : (setup.informationModel
      (CommitmentInterface.values setup.program)).InformationSite who)
    (belief : PMF ((setup.informationModel
      (CommitmentInterface.values setup.program)).InformationHistory who site.1))
    (beliefFinite : belief.support.Finite)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → ℝ) :
    ∃ alternative : (setup.informationModel
        (CommitmentInterface.values setup.program)).BehavioralPolicy who,
      expect belief (fun history => expect
        ((setup.informationModel admission).runBehavioralTerminalFrom targetCertificate
          (Function.update target who deviation)
          ((setup.valuesRestriction admission).history history.1))
        (fun final => (setup.protocolReadout final.state).elim 0
          (fun terminal => utility (setup.parameterOutcome parameter terminal)))) ≤
      expect belief (fun history => expect
        ((setup.informationModel
          (CommitmentInterface.values setup.program)).runBehavioralTerminalFrom
          sourceCertificate (Function.update
            (fun player => setup.toProtocolBehavioralPolicy
              (CommitmentInterface.values setup.program) player (profile player)
                ((values player).admitted setup.program (profile player)
                  (CommitmentInterface.values setup.program))) who alternative) history.1)
        (fun final => (setup.protocolReadout final.state).elim 0
          (fun terminal => utility (setup.parameterOutcome parameter terminal)))) := by
  let replacement := ((setup.behavioralPolicyEquiv admission who).symm deviation).1
  obtain ⟨alternative, bound⟩ := setup.exists_values_site_continuation_ge who finite profile
    (values who) replacement site belief beliefFinite parameter utility
  let permitted : ∀ player, ((Function.update profile who alternative.1) player).Admitted
      setup.program (CommitmentInterface.values setup.program) := by
    intro player
    by_cases own : player = who
    · subst player
      simpa only [Function.update_self] using
        alternative.2.admitted setup.program alternative.1
          (CommitmentInterface.values setup.program)
    · simpa only [Function.update_of_ne own] using
        (values player).admitted setup.program (profile player)
          (CommitmentInterface.values setup.program)
  refine ⟨setup.toProtocolBehavioralPolicy (CommitmentInterface.values setup.program) who
    alternative.1 (alternative.2.admitted setup.program alternative.1
      (CommitmentInterface.values setup.program)), ?_⟩
  have profiles : Function.update
      (fun player => setup.toProtocolBehavioralPolicy
        (CommitmentInterface.values setup.program) player (profile player)
          ((values player).admitted setup.program (profile player)
            (CommitmentInterface.values setup.program))) who
      (setup.toProtocolBehavioralPolicy (CommitmentInterface.values setup.program) who
        alternative.1 (alternative.2.admitted setup.program alternative.1
          (CommitmentInterface.values setup.program))) =
      (fun player => setup.toProtocolBehavioralPolicy
        (CommitmentInterface.values setup.program) player
          ((Function.update profile who alternative.1) player) (permitted player)) := by
    funext player
    by_cases own : player = who
    · subst player
      simp only [Function.update_self]
      congr 1
      exact (Function.update_self who alternative.1 profile).symm
    · simp only [Function.update_of_ne own]
      congr 1
      exact (Function.update_of_ne own alternative.1 profile).symm
  erw [profiles]
  have targetLaw : (fun history : (setup.informationModel
        (CommitmentInterface.values setup.program)).InformationHistory who site.1 => expect
      ((setup.informationModel admission).runBehavioralTerminalFrom targetCertificate
        (Function.update target who deviation)
        ((setup.valuesRestriction admission).history history.1))
      (fun final => (setup.protocolReadout final.state).elim 0
        (fun terminal => utility (setup.parameterOutcome parameter terminal)))) =
      (fun history : (setup.informationModel
        (CommitmentInterface.values setup.program)).InformationHistory who site.1 => expect
        (setup.continuationLaw (Function.update profile who replacement) history.1.state)
        (fun terminal => utility (setup.parameterOutcome parameter terminal))) := by
    funext history
    exact setup.copied_terminal_expect_source_continuation admission who profile values target
      copies deviation targetCertificate history.1 _
  have sourceLaw : (fun history : (setup.informationModel
        (CommitmentInterface.values setup.program)).InformationHistory who site.1 => expect
      ((setup.informationModel
          (CommitmentInterface.values setup.program)).runBehavioralTerminalFrom
        sourceCertificate (fun player => setup.toProtocolBehavioralPolicy
          (CommitmentInterface.values setup.program) player
            ((Function.update profile who alternative.1) player) (permitted player)) history.1)
      (fun final => (setup.protocolReadout final.state).elim 0
        (fun terminal => utility (setup.parameterOutcome parameter terminal)))) =
      (fun history : (setup.informationModel
        (CommitmentInterface.values setup.program)).InformationHistory who site.1 => expect
        (setup.continuationLaw (Function.update profile who alternative.1) history.1.state)
        (fun terminal => utility (setup.parameterOutcome parameter terminal))) := by
    funext history
    exact setup.terminal_expect_source_continuation (CommitmentInterface.values setup.program)
      _ permitted sourceCertificate history.1 _
  erw [targetLaw, sourceLaw]
  have tower (policy : BehavioralPolicy who setup.program) :
      expect (belief.bind fun history =>
        (setup.continuationLaw (Function.update profile who policy) history.1.state).map
          (setup.parameterOutcome parameter)) utility =
      expect belief (fun history => expect
        (setup.continuationLaw (Function.update profile who policy) history.1.state)
        (fun terminal => utility (setup.parameterOutcome parameter terminal))) := by
    have finiteLaw : (belief.bind fun history =>
        (setup.continuationLaw (Function.update profile who policy) history.1.state).map
          (setup.parameterOutcome parameter)).support.Finite := by
      rw [PMF.support_bind]
      exact beliefFinite.biUnion fun history _ => by
        rw [PMF.support_map]
        exact (setup.continuationLaw_support_finite _
          (FiniteBindingTypes.profileFiniteSupport setup.program finite _) history.1.state).image _
    rw [expect_bind_tower _ _ _ (payoffIntegrable_of_finite_support _ _ finiteLaw)]
    simp only [expect_map, Function.comp_def]
  rw [tower replacement, tower alternative.1] at bound
  exact bound

/-- Every values-only source sequential equilibrium extends to arbitrary
commitment admission, preserving its complete terminal law and source utility.
The original equilibrium may withhold or fail reveals; no forfeit bound or
intended-play assumption is needed. -/
theorem values_sequentialEquilibrium_preserved [Fintype Player]
    (admission : CommitmentInterface setup.program) (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (sourceCertificate : (setup.executionProtocol
      (CommitmentInterface.values setup.program)).WellFoundedHistories)
    (targetCertificate : (setup.executionProtocol admission).WellFoundedHistories)
    (source : (setup.informationModel
      (CommitmentInterface.values setup.program)).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibrium
      (setup.decision_antichain (CommitmentInterface.values setup.program)) sourceCertificate
      (fun who final => (setup.protocolReadout final.state).elim 0
        (fun terminal => utility (setup.parameterOutcome parameter terminal) who))) :
    ∃ target : (setup.informationModel admission).BehavioralAssessment,
      target.IsSequentialEquilibrium (setup.decision_antichain admission) targetCertificate
        (fun who final => (setup.protocolReadout final.state).elim 0
          (fun terminal => utility (setup.parameterOutcome parameter terminal) who)) ∧
      (setup.valuesRestriction admission).ExtendsProfile source.strategy target.strategy ∧
      (∀ who site, target.belief who ((setup.valuesRestriction admission).site who site) =
        (source.belief who site).map
          ((setup.valuesRestriction admission).informationHistory who site)) ∧
      ((setup.informationModel (CommitmentInterface.values setup.program)).runBehavioralTerminalFrom
        sourceCertificate source.strategy
        (setup.executionProtocol (CommitmentInterface.values setup.program)).initHistory).map
          (setup.valuesRestriction admission).history =
      (setup.informationModel admission).runBehavioralTerminalFrom targetCertificate target.strategy
        (setup.executionProtocol admission).initHistory := by
  classical
  let valuesAdmission := CommitmentInterface.values setup.program
  let restriction := setup.valuesRestriction admission
  have : Finite (setup.executionProtocol admission).History := setup.finite_history finite admission
  have : Finite (setup.executionProtocol valuesAdmission).History :=
    setup.finite_history finite valuesAdmission
  let payoff (interface : CommitmentInterface setup.program) :
      Player → (setup.executionProtocol interface).History → ℝ :=
    fun who final => (setup.protocolReadout final.state).elim 0
      (fun terminal => utility (setup.parameterOutcome parameter terminal) who)
  have matching : ∀ who history,
      payoff admission who (restriction.history history) = payoff valuesAdmission who history := by
    intro who history
    rfl
  refine Exists.imp ?_ (restriction.sequentialEquilibrium_extends_of_continuation_unclocked
    (setup.decision_antichain valuesAdmission) sourceCertificate targetCertificate
    (setup.uniformReference finite admission) (setup.uniformReference_fullyMixed finite admission)
    (setup.protocol_decisionRecall admission) (payoff valuesAdmission) (payoff admission) matching
    ?_ source equilibrium)
  · intro target properties
    exact ⟨properties.1, properties.2.1, properties.2.2.1, properties.2.2.2.1⟩
  · intro sourceProfile targetProfile copies who site action _ belief
    let profile : BehavioralProfile setup.program := fun player =>
      ((setup.behavioralPolicyEquiv valuesAdmission player).symm (sourceProfile player)).1
    have values : ∀ player, ValueBinding setup.program (profile player) := by
      intro player
      exact (BehavioralPolicy.admitted_values_iff_valueBinding setup.program (profile player)).mp
        ((setup.behavioralPolicyEquiv valuesAdmission player).symm (sourceProfile player)).2
    have original :
        (fun player => setup.toProtocolBehavioralPolicy valuesAdmission player (profile player)
          ((values player).admitted setup.program (profile player) valuesAdmission)) =
        sourceProfile := by
      funext player
      exact (setup.behavioralPolicyEquiv valuesAdmission player).apply_symm_apply
        (sourceProfile player)
    have copies' : restriction.ExtendsProfile
        (fun player => setup.toProtocolBehavioralPolicy valuesAdmission player (profile player)
          ((values player).admitted setup.program (profile player) valuesAdmission))
        targetProfile := by
      erw [original]
      exact copies
    obtain ⟨alternative, bound⟩ := setup.exists_values_admission_continuation_ge
      admission finite who
      profile values targetProfile copies'
      ((targetProfile who).commit (restriction.site who site).1 action)
      sourceCertificate targetCertificate site belief (Set.toFinite _) parameter
      (fun outcome => utility outcome who)
    refine ⟨alternative, ?_⟩
    erw [original] at bound
    exact bound
end Vegas.SourceProgram.Setup
