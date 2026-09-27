/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.RestrictedSourceValues
import Vegas.Examples.MonitoredGuessing.RestrictedValues
import Interaction.ReactiveConsistentAssessment
import GameTheoryExtensions.Analysis.Protocol.SequentialOneShot
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Source sequential equilibria survive the restricted native service

The game and policy translation are fixed before choosing the source assessment.
The native assessment uses one common consistency sequence. Its local incentives
are derived from the source continuation inequalities and the actual service
laws, then the decision-recall one-shot theorem covers whole-policy deviations.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

theorem early_choices_subsingleton (bit : Bool) :
    Subsingleton (restrictedModel.Choice alice
      (some ([], (aliceActivated bit).observe nativeApp alice))) := by
  constructor
  intro first second
  apply Subtype.ext
  have unique (choice : restrictedModel.Choice alice
      (some ([], (aliceActivated bit).observe nativeApp alice))) :
      choice.1 = some nativeSilent := by
    obtain ⟨response, available, same⟩ := choice.2
    have supported := (restrictedMenu.uniformResponses_support alice []
      ((aliceActivated bit).observe nativeApp alice) response).mpr available
    change response ∈ (restrictedMenu.uniformResponses alice ((aliceActivated bit).recall alice)
      ((aliceActivated bit).observe nativeApp alice)).support at supported
    rw [reference_early_alice, FinDist.mem_support_pure] at supported
    exact same.trans (congrArg some supported)
  exact (unique first).trans (unique second).symm

theorem compiled_alice_optimal (table : PayoffTable)
    (source : sourceModel.BehavioralAssessment)
    (rational : source.IsSequentiallyRationalWithin (sourceResultPayoff (tableReward table)) 3)
    (target : restrictedModel.BehavioralAssessment)
    (strategy : target.strategy = compile source.strategy)
    (site : restrictedModel.InformationSite alice) (bit guess : Bool)
    (siteEq : site.1 = aliceInput bit guess)
    (alternative : restrictedModel.BehavioralPolicy alice) :
    (target.continuationContext site
      (fun history => Enforcement.stateUtility table history.state alice)
        (2 * nativeHorizon + 1)).value alternative ≤
      (target.continuationContext site
        (fun history => Enforcement.stateUtility table history.state alice)
          (2 * nativeHorizon + 1)).value (target.strategy alice) := by
  rw [alice_context_value table target site bit guess siteEq,
    alice_context_value table target site bit guess siteEq, Profile.update_eq_self]
  conv_rhs => rw [strategy, compile, targetDisclosures_responseProfile]
  apply FinDist.expect_le_of_forall
  intro disclose _
  simpa only [source_results, decisionResult] using
    source_disclosure_optimal (tableReward table) source rational bit guess disclose

theorem compiled_bob_optimal (table : PayoffTable)
    (source : sourceModel.BehavioralAssessment)
    (sourceConsistent : source.IsSequentiallyConsistent sourceAntichain)
    (rational : source.IsSequentiallyRationalWithin (sourceResultPayoff (tableReward table)) 3)
    (target : restrictedModel.BehavioralAssessment)
    (consistent : target.IsSequentiallyConsistent restricted_decisionRecall.antichain)
    (strategy : target.strategy = compile source.strategy)
    (site : restrictedModel.InformationSite bob)
    (alternative : restrictedModel.BehavioralPolicy bob) :
    (target.continuationContext site
      (fun history => Enforcement.stateUtility table history.state bob)
        (2 * nativeHorizon + 1)).value alternative ≤
      (target.continuationContext site
        (fun history => Enforcement.stateUtility table history.state bob)
          (2 * nativeHorizon + 1)).value (target.strategy bob) := by
  rw [receiver_context_value table target consistent site,
    receiver_context_value table target consistent site, Profile.update_eq_self]
  simp only [strategy, compile, targetGuesses_responseProfile, targetDisclosures_responseProfile]
  conv_lhs => rw [FinDist.expect_comm]
  apply FinDist.expect_le_of_forall
  intro guess _
  simpa only [source_results, decisionResult] using
    source_guess_optimal (tableReward table) source sourceConsistent rational guess

open Classical in
theorem compiled_local_optimal (table : PayoffTable)
    (watcherZero : ∀ result, table result watcher = 0)
    (source : sourceModel.BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
      source.continuationContext site (sourceResultPayoff (tableReward table) who) 3))
    (target : restrictedModel.BehavioralAssessment)
    (consistent : target.IsSequentiallyConsistent restricted_decisionRecall.antichain)
    (strategy : target.strategy = compile source.strategy)
    (who : Player) (site : restrictedModel.InformationSite who)
    (law : FinDist (restrictedModel.Choice who site.1)) :
    (target.continuationContext site
      (fun history => Enforcement.stateUtility table history.state who)
        (2 * nativeHorizon + 1)).value ((target.strategy who).withLaw site.1 law) ≤
      (target.continuationContext site
        (fun history => Enforcement.stateUtility table history.state who)
          (2 * nativeHorizon + 1)).value (target.strategy who) := by
  classical
  fin_cases who
  · change restrictedModel.InformationSite alice at site
    change FinDist (restrictedModel.Choice alice site.1) at law
    change (target.continuationContext site
      (fun history => Enforcement.stateUtility table history.state alice)
        (2 * nativeHorizon + 1)).value ((target.strategy alice).withLaw site.1 law) ≤
      (target.continuationContext site
        (fun history => Enforcement.stateUtility table history.state alice)
          (2 * nativeHorizon + 1)).value (target.strategy alice)
    rcases alice_site_cases site with ⟨bit, early⟩ | ⟨bit, guess, final⟩
    · let : Subsingleton (restrictedModel.Choice alice site.1) := by
        rw [early]
        exact early_choices_subsingleton bit
      let choice := (target.strategy alice site.1).support_nonempty.choose
      have same : law = target.strategy alice site.1 :=
        (FinDist.eq_pure_of_subsingleton law choice).trans
          (FinDist.eq_pure_of_subsingleton (target.strategy alice site.1) choice).symm
      rw [same, InformationModel.BehavioralPolicy.withLaw_eq_self]
    · exact compiled_alice_optimal table source equilibrium.1 target strategy site bit guess final _
  · exact compiled_bob_optimal table source equilibrium.2 equilibrium.1 target consistent
      strategy site _
  · change restrictedModel.InformationSite watcher at site
    change FinDist (restrictedModel.Choice watcher site.1) at law
    change (target.continuationContext site
      (fun history => Enforcement.stateUtility table history.state watcher)
        (2 * nativeHorizon + 1)).value ((target.strategy watcher).withLaw site.1 law) ≤
      (target.continuationContext site
        (fun history => Enforcement.stateUtility table history.state watcher)
          (2 * nativeHorizon + 1)).value (target.strategy watcher)
    simp only [InformationModel.BehavioralAssessment.continuationContext_value,
      Enforcement.stateUtility_watcher table watcherZero, FinDist.expect_const, le_refl]

/-- Every source SE, with arbitrary declared result incentives, has a consistent
SE at its fixed translated policy in the restricted native game. -/
theorem source_equilibrium_compiles (table : PayoffTable)
    (watcherZero : ∀ result, table result watcher = 0)
    (source : sourceModel.BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
      source.continuationContext site (sourceResultPayoff (tableReward table) who) 3)) :
    ∃ target : restrictedModel.BehavioralAssessment,
      target.strategy = compile source.strategy ∧
      target.IsSequentialEquilibriumFor restricted_decisionRecall.antichain (fun who site =>
        target.continuationContext site
          (fun history => Enforcement.stateUtility table history.state who)
          (2 * nativeHorizon + 1 - restrictedDepth who site)) := by
  classical
  obtain ⟨target, strategy, consistent⟩ := restrictedMenu.exists_consistent_assessment
    nativeInitialLaw nativeHorizon nativeScheduler (compile source.strategy)
  refine ⟨target, strategy, ?_, consistent⟩
  apply consistent.sequentiallyRational_of_localOptimal restricted_decisionRecall
    (2 * nativeHorizon + 1) (fun who history => Enforcement.stateUtility table history.state who)
    restrictedDepth restricted_common_depth
  · intro who site
    by_contra outside
    have stopped := restrictedMenu.bounded nativeInitialLaw nativeHorizon nativeScheduler
      site.2.choose.1.state site.2.choose.1.trace (by
        rw [restricted_common_depth who site site.2.choose]
        omega)
    exact site.2.choose_spec.1 stopped
  · intro who site _ law
    rw [target.continuationContext_remaining restrictedModel (2 * nativeHorizon + 1)
      (restrictedMenu.bounded nativeInitialLaw nativeHorizon nativeScheduler) who site
      (restrictedDepth who site) (restricted_common_depth who site)]
    exact compiled_local_optimal table watcherZero source equilibrium target consistent
      strategy who site law

end Vegas.Examples.MonitoredGuessing.Restricted
