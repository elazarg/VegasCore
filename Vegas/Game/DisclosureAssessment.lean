/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.DisclosureProfileComparison
import Vegas.Game.SourceBayes
import Vegas.Game.SourcePrefixKernel
import GameTheoryExtensions.Protocol.SequentialIncentives
import GameTheoryExtensions.Math.Probability.Conditioning

/-! # Private disclosure comparisons against actual source assessments

Positive original source observations select genuine information sites of the
existing initialized protocol. Its Bayesian posterior is the conditional prefix
law. Consequently the private-intention mixtures are mixtures of standard
assessment comparisons, with one common law for the prescribed and deviating
continuations. Normalized profiles are only operational intermediates.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (admission : CommitmentInterface setup.program)

private theorem decoded_prefix_law
    (profile : Profile (setup.informationModel admission).behavioralSignature) (count : Nat) :
    ((setup.informationModel admission).runBehavioral profile (count + 1)).map History.state =
      (((setup.initialLaw.map setup.initialConfig).bind fun config =>
        (fun distribution => distribution.bind (ProtocolState.behavioralStateStep setup.program
          (setup.decodeBehavioralProfile admission profile)))^[count]
            (PMF.pure (ProtocolState.entry setup.program config))).map some) := by
  have admitted who := ((setup.behavioralPolicyEquiv admission who).symm (profile who)).2
  have encoded : (fun who => setup.toProtocolBehavioralPolicy admission who
      (setup.decodeBehavioralProfile admission profile who) (admitted who)) = profile :=
    funext fun who => (setup.behavioralPolicyEquiv admission who).apply_symm_apply (profile who)
  have law := setup.encoded_prefix_state admission
    (setup.decodeBehavioralProfile admission profile) admitted count
  rw [encoded] at law
  simpa only [PMF.bind_map, PMF.map_bind] using law

private theorem prefix_observation_site
    (profile : Profile (setup.informationModel admission).behavioralSignature)
    (count : Nat) (who : Player) (view : SourceProgram.ProtocolView who setup.program)
    (present : view ∈ (((setup.initialLaw.map setup.initialConfig).bind fun config =>
      (fun distribution => distribution.bind (ProtocolState.behavioralStateStep setup.program
        (setup.decodeBehavioralProfile admission profile)))^[count]
          (PMF.pure (ProtocolState.entry setup.program config))).map
            (ProtocolState.observe who setup.program)).support)
    (active : SourceProgram.ProtocolView.actor who setup.program view = some who) :
    ∃ site : (setup.informationModel admission).InformationSite who,
      site.1 = some view ∧ setup.decisionDepth who site.1 = count + 1 := by
  let M := setup.informationModel admission
  obtain ⟨state, supported, observed⟩ := PMF.support_map .. ▸ present
  have member : some state ∈ (((setup.informationModel admission).runBehavioral profile
      (count + 1)).map History.state).support := by
    rw [setup.decoded_prefix_law, PMF.support_map]
    exact ⟨state, supported, rfl⟩
  obtain ⟨history, reached, stateEq⟩ := PMF.support_map .. ▸ member
  have info : (setup.informationModel admission).infoOf who history.trace = some view := by
    rw [show (setup.informationModel admission).infoOf who history.trace =
      setup.protocolObserve who history.state from setup.protocol_info admission who history.trace]
    simp only [stateEq, protocolObserve, Option.map_some, observed]
  have running : ¬ (setup.executionProtocol admission).terminal history.state := by
    rw [stateEq]
    intro stopped
    have absent := ProtocolState.terminal_actor_none who setup.program state stopped
    rw [observed, active] at absent
    cases absent
  have acts : (setup.executionProtocol admission).active history.state who := by
    change (setup.protocolObserve who history.state).elim False _
    simpa only [stateEq, protocolObserve, Option.map_some, Option.elim_some, observed] using active
  obtain ⟨site, same⟩ := (setup.informationModel admission).exists_informationSite_of_active
    who history running acts
  refine ⟨site, same.trans info, ?_⟩
  have length : history.trace.length = count + 1 := by
    rcases M.terminal_or_trace_length_eq_of_mem_support_runBehavioralFrom
      profile (count + 1) (setup.executionProtocol admission).initHistory history reached with
      terminal | length
    · exact (running terminal).elim
    · simpa only [ExecutionProtocol.initHistory, ExecutionProtocol.Trace.length, zero_add]
        using length
  exact (setup.common_decision_depth admission who site ⟨history, same.symm⟩).symm.trans length

variable [∀ who (site : (setup.informationModel admission).InformationSite who),
  Fintype ((setup.informationModel admission).InformationHistory who site.1)]

private theorem comparison_prefix_laws
    (assessment : (setup.informationModel admission).BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      (setup.informationModel admission) assessment (setup.decision_antichain admission))
    (count : Nat) (who : Player) (view : SourceProgram.ProtocolView who setup.program)
    (site : (setup.informationModel admission).InformationSite who)
    (same : site.1 = some view) (depth : setup.decisionDepth who site.1 = count + 1)
    (present : view ∈ (((setup.initialLaw.map setup.initialConfig).bind fun config =>
      (fun distribution => distribution.bind (ProtocolState.behavioralStateStep setup.program
        (setup.decodeBehavioralProfile admission assessment.strategy)))^[count]
          (PMF.pure (ProtocolState.entry setup.program config))).map
            (ProtocolState.observe who setup.program)).support)
    (alternative : BehavioralPolicy who setup.program)
    (admitted : alternative.Admitted setup.program admission) :
    let profile := setup.decodeBehavioralProfile admission assessment.strategy
    let prefixLaw := (setup.initialLaw.map setup.initialConfig).bind fun config =>
      (fun distribution => distribution.bind (ProtocolState.behavioralStateStep setup.program
        profile))^[count] (PMF.pure (ProtocolState.entry setup.program config))
    let comparison := (setup.informationModel admission).assessmentComparison
      (fun final => setup.protocolReadout final.state) (instructionCount setup.program + 1)
      assessment who (site, setup.toProtocolBehavioralPolicy admission who alternative admitted)
    comparison.prescribed = ((fiberConditional prefixLaw
      (ProtocolState.observe who setup.program) view).bind
        (ProtocolState.continuationLaw setup.program profile)).map some ∧
    comparison.alternative = ((fiberConditional prefixLaw
      (ProtocolState.observe who setup.program) view).bind
        (ProtocolState.continuationLaw setup.program (Function.update profile who alternative))).map
          some := by
  classical
  let profile := setup.decodeBehavioralProfile admission assessment.strategy
  let prefixLaw := (setup.initialLaw.map setup.initialConfig).bind fun config =>
    (fun distribution => distribution.bind (ProtocolState.behavioralStateStep setup.program
      profile))^[count] (PMF.pure (ProtocolState.entry setup.program config))
  have imagePresent : some view ∈
      (prefixLaw.map (setup.protocolObserve who ∘ some)).support := by
    obtain ⟨state, supported, observed⟩ := PMF.support_map .. ▸ present
    rw [PMF.support_map]
    exact ⟨state, supported, congrArg some observed⟩
  have sameFiber : fiberConditional prefixLaw (setup.protocolObserve who ∘ some) (some view) =
      fiberConditional prefixLaw (ProtocolState.observe who setup.program) view := by
    have fiber : (setup.protocolObserve who ∘ some) ⁻¹' {some view} =
        (ProtocolState.observe who setup.program) ⁻¹' {view} := by
      ext state
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply, protocolObserve,
        Option.map_some, Option.some.injEq]
    simp only [fiberConditional, fiber]
  have posterior := PMF.map_conditional_readout prefixLaw some (setup.protocolObserve who)
    (some view) imagePresent
  rw [sameFiber] at posterior
  have value (policy : (setup.informationModel admission).BehavioralPolicy who) :=
    setup.continuationContext_law_conditional_prefix admission assessment mixed bayes who site
      policy
  have decoded : setup.decodeBehavioralProfile admission
      (Profile.update (sig := (setup.informationModel admission).behavioralSignature)
        assessment.strategy who (setup.toProtocolBehavioralPolicy admission who
          alternative admitted)) = Function.update profile who alternative := by
    funext player
    by_cases equal : player = who
    · subst player
      simp only [decodeBehavioralProfile, Profile.update_same, Function.update_self]
      exact congrArg Subtype.val ((setup.behavioralPolicyEquiv admission who).symm_apply_apply
        ⟨alternative, admitted⟩)
    · simp only [decodeBehavioralProfile, Profile.update_of_ne _ _ equal,
        Function.update_of_ne equal, profile]
  constructor
  · have prescribed := value (assessment.strategy who)
    rw [depth, setup.decoded_prefix_law, same, ← posterior, PMF.bind_map,
      Profile.update_eq_self] at prescribed
    exact prescribed
  · have deviating := value (setup.toProtocolBehavioralPolicy admission who alternative admitted)
    rw [depth, setup.decoded_prefix_law, same, ← posterior, PMF.bind_map, decoded] at deviating
    exact deviating

/-- Every normalized meaningful source decision is a finite mixture of actual
original assessment comparisons. Private alias histories choose the source
information site and admitted whole-policy deviation together; the same weights
represent both terminal laws. No normalized assessment or equilibrium is used. -/
theorem normalized_disclosure_assessment_comparison
    (assessment : (setup.informationModel admission).BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      (setup.informationModel admission) assessment (setup.decision_antichain admission))
    (count : Nat) :
    let profile := setup.decodeBehavioralProfile admission assessment.strategy
    let normalized := normalizeDisclosureProfile setup.program []
      (Revelations.initial setup.context) profile
    let prefixLaw := fun selected => (setup.initialLaw.map setup.initialConfig).bind fun config =>
      (fun distribution => distribution.bind (ProtocolState.behavioralStateStep setup.program
        selected))^[count] (PMF.pure (ProtocolState.entry setup.program config))
    ∀ who (alternative : BehavioralPolicy who setup.program),
      alternative.Admitted setup.program admission →
      ∀ view ∈ ((prefixLaw normalized).map (ProtocolState.observe who setup.program)).support,
        SourceProgram.ProtocolView.actor who setup.program view = some who →
        ∃ mixture : PMF ((setup.informationModel admission).AssessmentDeviation who),
          (((fiberConditional (prefixLaw normalized) (ProtocolState.observe who setup.program) view).bind
            (ProtocolState.continuationLaw setup.program normalized)).map some) =
            mixture.bind (fun deviation => ((setup.informationModel admission).assessmentComparison
              (fun final => setup.protocolReadout final.state) (instructionCount setup.program + 1)
                assessment who deviation).prescribed) ∧
          (((fiberConditional (prefixLaw normalized) (ProtocolState.observe who setup.program) view).bind
            (ProtocolState.continuationLaw setup.program
              (Function.update normalized who alternative))).map some) =
            mixture.bind (fun deviation => ((setup.informationModel admission).assessmentComparison
              (fun final => setup.protocolReadout final.state) (instructionCount setup.program + 1)
                assessment who deviation).alternative) := by
  classical
  dsimp only
  intro who alternative admitted view present active
  obtain ⟨weights, supported, prescribed, deviating⟩ :=
    normalizeDisclosureProfile_prefix_comparison setup.program admission
      (setup.decodeBehavioralProfile admission assessment.strategy) []
      (Revelations.initial setup.context) (setup.initialLaw.map setup.initialConfig)
      (fun config member => by
        obtain ⟨initial, _supported, rfl⟩ := PMF.support_map .. ▸ member
        rfl)
      (fun config member => by
        obtain ⟨initial, _supported, rfl⟩ := PMF.support_map .. ▸ member
        rfl) count who alternative admitted view present
  have sites (selected) (member : selected ∈ weights.support) :=
    setup.prefix_observation_site admission assessment.strategy count who selected.1
      (supported selected member).1 ((supported selected member).2.1.trans active)
  let mixture := weights.bindOnSupport fun selected member =>
    PMF.pure ((sites selected member).choose,
      setup.toProtocolBehavioralPolicy admission who selected.2.1 selected.2.2)
  have laws (selected) (member : selected ∈ weights.support) :=
    setup.comparison_prefix_laws admission assessment mixed bayes count who selected.1
      (sites selected member).choose (sites selected member).choose_spec.1
      (sites selected member).choose_spec.2 (supported selected member).1 selected.2.1 selected.2.2
  refine ⟨mixture, ?_, ?_⟩
  · rw [prescribed, PMF.map_bind]
    symm
    change (weights.bindOnSupport _).bind _ = _
    rw [bindOnSupport_bind]
    apply bindOnSupport_eq_bind_of_eq_on_support _
    intro selected member
    simpa only [PMF.pure_bind] using (laws selected member).1
  · rw [deviating, PMF.map_bind]
    symm
    change (weights.bindOnSupport _).bind _ = _
    rw [bindOnSupport_bind]
    apply bindOnSupport_eq_bind_of_eq_on_support _
    intro selected member
    simpa only [PMF.pure_bind] using (laws selected member).2

end Vegas.SourceProgram.Setup
