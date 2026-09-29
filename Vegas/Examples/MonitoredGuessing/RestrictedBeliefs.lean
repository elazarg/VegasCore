/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.RestrictedSupport
import Vegas.Examples.MonitoredGuessing.RestrictedClock
import Interaction.ReactiveFiniteAssessment
import Interaction.ReactiveAssessmentEvaluation
import GameTheoryExtensions.Analysis.Protocol.FixedDepthBayes
import GameTheoryExtensions.Math.Probability.Uniform

/-! # The restricted receiver's posterior follows from consistency

Every restricted behavioral profile has the same silent prefix and one Bob
information set. Consequently every consistent assessment has the fair initial
bit as its state belief there. No belief is assigned separately from the common
sequence witnessing sequential consistency.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

theorem decoded_early_alice (profile : Profile restrictedModel.behavioralSignature) (bit : Bool) :
    restrictedMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler profile alice
      ((aliceActivated bit).recall alice) ((aliceActivated bit).observe nativeApp alice) =
        PMF.pure nativeSilent := by
  apply pmf_eq_pure_of_support_subset_singleton
  intro response supported
  have available := restrictedMenu.decode_embedPolicy_covered nativeInitialLaw nativeHorizon
    nativeScheduler alice (profile alice) _ _ response supported
  have uniform := (restrictedMenu.uniformResponses_support alice _ _ response).mpr available
  rw [reference_early_alice, PMF.mem_support_pure_iff _ _] at uniform
  exact uniform

theorem decoded_quiet_watcher (profile : Profile restrictedModel.behavioralSignature)
    (bit : Bool) :
    restrictedMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler profile watcher
      ((watcherActivated bit nativeSilent ∅).recall watcher)
      ((watcherActivated bit nativeSilent ∅).observe nativeApp watcher) =
        PMF.pure nativeSilent := by
  apply pmf_eq_pure_of_support_subset_singleton
  intro response supported
  have available := restrictedMenu.decode_embedPolicy_covered nativeInitialLaw nativeHorizon
    nativeScheduler watcher (profile watcher) _ _ response supported
  have uniform := (restrictedMenu.uniformResponses_support watcher _ _ response).mpr available
  rw [reference_quiet_watcher, PMF.mem_support_pure_iff _ _] at uniform
  exact uniform

theorem bob_prefix_law (profile : Profile restrictedModel.behavioralSignature) :
    (restrictedModel.runBehavioral profile 8).map History.state =
      (PMF.uniformOfFintype Bool).map
        (fun bit => some ⟨9, some bob, quietBob bit⟩) := by
  rw [InformationModel.runBehavioral, restrictedMenu.run_map_controlStep]
  exact quiet_bob_control_law _ (decoded_early_alice profile) (decoded_quiet_watcher profile)

theorem bob_state_belief (assessment : restrictedModel.BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent
      restricted_decisionRecall.decisionInformationAntichain)
    (site : restrictedModel.InformationSite bob) :
    (assessment.belief bob site).map (fun history => history.1.state) =
      (PMF.uniformOfFintype Bool).map
        (fun bit => some ⟨9, some bob, quietBob bit⟩) := by
  classical
  have depth : ∀ history : restrictedModel.InformationHistory bob site.1,
      history.1.trace.length = 8 := by
    simpa only [restrictedDepth, watchedDepth, effectiveDepth, nativeDecisionDepth, ↓reduceIte,
      InformationModel.InformationSite.CommonDepth]
      using restricted_common_depth bob site
  have seen (history : restrictedArena.History)
      (supported : history ∈ (restrictedModel.runBehavioral assessment.strategy 8).support) :
      restrictedModel.infoOf bob history.trace = site.1 := by
    have stateSupported : history.state ∈
        ((restrictedModel.runBehavioral assessment.strategy 8).map History.state).support := by
      rw [PMF.support_map]
      exact ⟨history, supported, rfl⟩
    rw [bob_prefix_law, PMF.support_map] at stateSupported
    obtain ⟨bit, _, same⟩ := stateSupported
    exact (restrictedMenu.info nativeInitialLaw nativeHorizon nativeScheduler bob
      history.trace).trans
      ((congrArg (nativeApp.observe bob) same).symm.trans
        ((bob_input bit).trans (bob_site_input site).symm))
  have belief := assessment.belief_map_eq_run_of_full_reach restrictedModel bob site 8
    restricted_decisionRecall.decisionInformationAntichain consistent depth seen
  have stateLaw := congrArg (fun histories : PMF restrictedArena.History =>
    histories.map History.state) belief
  simpa only [PMF.map_comp, Function.comp_def] using stateLaw.trans (bob_prefix_law _)

theorem bob_context_value (assessment : restrictedModel.BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent
      restricted_decisionRecall.decisionInformationAntichain)
    (site : restrictedModel.InformationSite bob) (payoff : nativeApp.ProtocolState → ℝ)
    (alternative : restrictedModel.BehavioralPolicy bob) :
    (assessment.continuationContext site (fun history => payoff history.state)
      (2 * nativeHorizon + 1)).value alternative =
      expect (PMF.uniformOfFintype Bool) (fun bit =>
        expect (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler
          (restrictedMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler
            (Profile.update (sig := restrictedModel.behavioralSignature)
              assessment.strategy bob alternative))
          (some ⟨9, some bob, quietBob bit⟩)) payoff) := by
  rw [restrictedMenu.context_value_finish]
  have projected := congrArg (fun law : PMF nativeApp.ProtocolState => expect law
    (fun state => expect (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler
      (restrictedMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler
        (Profile.update (sig := restrictedModel.behavioralSignature)
          assessment.strategy bob alternative)) state) payoff))
    (bob_state_belief assessment consistent site)
  simpa only [expect_map, Function.comp_def] using projected

end Vegas.Examples.MonitoredGuessing.Restricted
