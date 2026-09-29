/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceInformation
import Vegas.Game.SourceContinuation
import GameTheoryExtensions.Analysis.Protocol.FixedDepthBayes
import GameTheoryExtensions.Analysis.Protocol.UniformPolicyLimit
import GameTheoryExtensions.Math.Probability.ObservationRetraction

/-! # Source assessment beliefs are actual conditional prefix laws

The source's existing protocol state determines its information. At each
decision depth, a fully mixed Bayesian assessment therefore has exactly the
state posterior obtained by conditioning the actual initialized prefix law.
This connects operational private-memory comparisons to the standard assessment
notion without assuming that a normalized source profile is an equilibrium.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (admission : CommitmentInterface setup.program)
  [∀ who (site : (setup.informationModel admission).InformationSite who),
    Fintype ((setup.informationModel admission).InformationHistory who site.1)]

/-- The posterior over complete source states uses the actual decision depth,
including the initial correlated setup draw. It also applies when the limiting
equilibrium will assign zero probability to the information site. -/
theorem stateBelief_eq_conditional_prefix
    (assessment : (setup.informationModel admission).BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      (setup.informationModel admission) assessment (setup.decision_antichain admission))
    (who : Player) (site : (setup.informationModel admission).InformationSite who) :
    assessment.stateBelief who site =
      fiberConditional (((setup.informationModel admission).runBehavioral assessment.strategy
        (setup.decisionDepth who site.1)).map History.state)
          (setup.protocolObserve who) site.1 := by
  classical
  let M := setup.informationModel admission
  let _ : Finite (setup.executionProtocol admission).History :=
    mixed.finite_history (setup.protocol_bounded admission)
  let depth := setup.decisionDepth who site.1
  let prefixLaw := M.runBehavioral assessment.strategy depth
  have clock := setup.common_decision_depth admission who site
  have positive := mixed.informationMass_pos who site
  have belief : assessment.belief who site =
      M.bayesBelief assessment.strategy who site
        (setup.decision_antichain admission who site) positive := by
    apply pmf_ext_toReal
    intro history
    rw [M.bayesBelief_prob]
    exact bayes who site positive history
  obtain ⟨history, _running, _active⟩ := site.2
  have supported : history.1 ∈ prefixLaw.support := by
    have support := mixed.history_supported history.1.trace
    rwa [clock history] at support
  have meets : ∃ h ∈ {h | M.infoOf who h.trace = site.1}, h ∈ prefixLaw.support :=
    ⟨history.1, history.2, supported⟩
  have present : site.1 ∈ (prefixLaw.map (setup.protocolObserve who ∘ History.state)).support := by
    rw [PMF.support_map]
    refine ⟨history.1, supported, ?_⟩
    exact (setup.protocol_info admission who history.1.trace).symm.trans history.2
  have conditioned := M.bayesBelief_map_eq_condOn assessment.strategy who site depth clock
    (setup.decision_antichain admission who site) positive meets
  rw [← belief] at conditioned
  have fiber : prefixLaw.filter {h | M.infoOf who h.trace = site.1} meets =
      fiberConditional prefixLaw (setup.protocolObserve who ∘ History.state) site.1 := by
    have same : {h : (setup.executionProtocol admission).History |
        M.infoOf who h.trace = site.1} =
        (setup.protocolObserve who ∘ History.state) ⁻¹' {site.1} := by
      ext h
      change M.infoOf who h.trace = site.1 ↔ setup.protocolObserve who h.state = site.1
      rw [show M.infoOf who h.trace = setup.protocolObserve who h.state from
        setup.protocol_info admission who h.trace]
    rw [fiberConditional, dite_eq_left (same ▸ meets)]
    congr 1
  calc
    assessment.stateBelief who site =
        ((assessment.belief who site).map Subtype.val).map History.state :=
      (PMF.map_comp _ _ _).symm
    _ = (fiberConditional prefixLaw (setup.protocolObserve who ∘ History.state) site.1).map
        History.state := by rw [conditioned, fiber]
    _ = _ := PMF.map_conditional_readout prefixLaw History.state
      (setup.protocolObserve who) site.1 present

/-- Every whole-policy continuation in a Bayesian source assessment is exactly
the existing source continuation kernel averaged under its conditional prefix
law. The terminal typed store is retained, rather than only its expected utility. -/
theorem continuationContext_law_conditional_prefix
    (assessment : (setup.informationModel admission).BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      (setup.informationModel admission) assessment (setup.decision_antichain admission))
    (who : Player) (site : (setup.informationModel admission).InformationSite who)
    (alternative : (setup.informationModel admission).BehavioralPolicy who) :
    ((assessment.continuationContext site (fun _ => 0)
        (instructionCount setup.program + 1)).outcome alternative).map
        (fun final => setup.protocolReadout final.state) =
      ((fiberConditional (((setup.informationModel admission).runBehavioral assessment.strategy
          (setup.decisionDepth who site.1)).map History.state)
            (setup.protocolObserve who) site.1).bind
        (setup.continuationLaw (setup.decodeBehavioralProfile admission
          (Profile.update (sig := (setup.informationModel admission).behavioralSignature)
            assessment.strategy who alternative)))).map some := by
  rw [← setup.stateBelief_eq_conditional_prefix admission assessment mixed bayes who site]
  simp only [InformationModel.BehavioralAssessment.continuationContext,
    InformationModel.BehavioralAssessment.stateBelief, PMF.map_bind, PMF.bind_map]
  apply bind_congr_on_support _
  intro history _supported
  apply setup.runBehavioralFrom_readout admission
  have remaining := setup.protocol_history_length admission history.1.trace
  omega

/-- The value version of the exact terminal-law identity, for arbitrary
utilities of the complete terminal typed store. -/
theorem continuationContext_value_conditional_prefix
    (assessment : (setup.informationModel admission).BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      (setup.informationModel admission) assessment (setup.decision_antichain admission))
    (who : Player) (site : (setup.informationModel admission).InformationSite who)
    (alternative : (setup.informationModel admission).BehavioralPolicy who)
    (utility : State L setup.program.terminalCtx → ℝ) :
    (assessment.continuationContext site
        (fun final => (setup.protocolReadout final.state).elim 0 utility)
        (instructionCount setup.program + 1)).value alternative =
      expect (fiberConditional (((setup.informationModel admission).runBehavioral assessment.strategy
        (setup.decisionDepth who site.1)).map History.state)
          (setup.protocolObserve who) site.1) (fun state =>
        expect (setup.continuationLaw (setup.decodeBehavioralProfile admission
          (Profile.update (sig := (setup.informationModel admission).behavioralSignature)
            assessment.strategy who alternative)) state) utility) := by
  rw [setup.continuationContext_value_stateBelief admission assessment who site alternative
    utility _ (fun history => by
      have remaining := setup.protocol_history_length admission history.1.trace
      omega), setup.stateBelief_eq_conditional_prefix admission assessment mixed bayes]

/-- Every original-source conditional comparison has one vanishing bound,
uniform over information sites and admitted whole syntactic policies. Thus a
finite mixture may choose different original private histories and deviations
at each perturbation without assuming rationality of normalized source play. -/
theorem exists_uniform_prefix_gain_bound
    (source : (setup.informationModel admission).BehavioralAssessment)
    (sequence : ℕ → (setup.informationModel admission).BehavioralAssessment)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
      (setup.informationModel admission) (sequence n) (setup.decision_antichain admission))
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence source)
    (who : Player) (utility : State L setup.program.terminalCtx → ℝ)
    (rational : ∀ site : (setup.informationModel admission).InformationSite who,
      source.IsSequentiallyRationalAt site (source.continuationContext site
        (fun final => (setup.protocolReadout final.state).elim 0 utility)
        (instructionCount setup.program + 1))) :
    ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Filter.Tendsto error Filter.atTop (nhds 0) ∧
      ∀ n (site : (setup.informationModel admission).InformationSite who)
        (alternative : BehavioralPolicy who setup.program),
        alternative.Admitted setup.program admission →
        let profile := setup.decodeBehavioralProfile admission (sequence n).strategy
        let posterior := fiberConditional (((setup.informationModel admission).runBehavioral
          (sequence n).strategy (setup.decisionDepth who site.1)).map History.state)
            (setup.protocolObserve who) site.1
        expect posterior (fun state =>
            expect (setup.continuationLaw (Function.update profile who alternative) state)
              utility) -
          expect posterior (fun state => expect (setup.continuationLaw profile state) utility) ≤
            error n := by
  classical
  let _ : Finite (setup.executionProtocol admission).History :=
    (mixed 0).finite_history (setup.protocol_bounded admission)
  obtain ⟨error, nonnegative, vanishes, bound⟩ :=
    converges.exists_uniform_policy_gain_bound (sequence 0) (mixed 0) who
      (fun final => (setup.protocolReadout final.state).elim 0 utility)
      (instructionCount setup.program + 1) rational
  refine ⟨error, nonnegative, vanishes, ?_⟩
  intro n site alternative admitted
  let encoded := setup.toProtocolBehavioralPolicy admission who alternative admitted
  have decoded : setup.decodeBehavioralProfile admission
      (Profile.update (sig := (setup.informationModel admission).behavioralSignature)
        (sequence n).strategy who encoded) =
      Function.update (setup.decodeBehavioralProfile admission (sequence n).strategy)
        who alternative := by
    funext player
    by_cases same : player = who
    · subst player
      simp only [decodeBehavioralProfile, Profile.update_same, Function.update_self]
      exact congrArg Subtype.val ((setup.behavioralPolicyEquiv admission who).symm_apply_apply
        ⟨alternative, admitted⟩)
    · simp only [decodeBehavioralProfile, Profile.update_of_ne _ _ same,
        Function.update_of_ne same]
  have estimate := bound n site encoded
  rw [setup.continuationContext_value_conditional_prefix admission (sequence n) (mixed n)
      (bayes n) who site encoded utility,
    setup.continuationContext_value_conditional_prefix admission (sequence n) (mixed n)
      (bayes n) who site ((sequence n).strategy who) utility,
    Profile.update_eq_self, decoded] at estimate
  exact estimate

end Vegas.SourceProgram.Setup
