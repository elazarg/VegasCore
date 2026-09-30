/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.RestrictedEvaluation
import Vegas.Examples.MonitoredGuessing.RestrictedBeliefs
import Vegas.Examples.MonitoredGuessing.EnforcementPayoffs
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Restricted continuations retain the declared game utilities

Every restricted policy, including every unilateral replacement, decodes to
source decision lotteries. The actual final service incurs neither liability.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

def tableReward (table : PayoffTable) (result : Results) (who : Player) : ℝ := table result who

theorem before_alice_position (bit guess : Bool) :
    (beforeAlice bit guess).environmentRecall.length = 10 := by
  cases guess <;> rfl

theorem alice_finish_value (table : PayoffTable)
    (profile : Profile restrictedModel.behavioralSignature) (bit guess : Bool) (who : Player) :
    expect (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler
      (restrictedMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler profile)
      (some ⟨4, some alice, beforeAlice bit guess⟩))
        (fun state => Enforcement.stateUtility table state who) =
      expect (targetDisclosures profile bit guess) fun disclose =>
        tableReward table (sourceResults (finalConfig bit guess disclose).state) who := by
  have finish := native_finish_response
    (restrictedMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler profile)
    (nativePlan.take 9) resolutionTail alice rfl (beforeAlice bit guess)
    (before_alice_position bit guess)
  change nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler _
    (some ⟨4, some alice, beforeAlice bit guess⟩) = _ at finish
  rw [finish, decoded_alice_response, PMF.bind_map,
    expect_bind_tower _ _ _ (Enforcement.stateUtility_integrable table who _)]
  apply expect_congr_on_support
  intro disclose _
  rw [Function.comp_apply, expect_map]
  exact Enforcement.alice_service_value table _ bit guess disclose who

theorem bob_choice_value (table : PayoffTable)
    (profile : Profile restrictedModel.behavioralSignature) (bit guess : Bool) (who : Player) :
    expect (nativeRuntime.runInteractionPlan nativeLeaks
      (restrictedMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler profile)
      nativeNetwork
      ([.includeLatest bobPublication bob, .tick, .expire bobPublication,
        .grant alicePublication, .player alice] ++ resolutionTail)
      ((quietBob bit).respond nativeApp bob
        (choiceAction bobPublication bobHandle true guess)))
        (fun final => Enforcement.executionUtility table final who) =
      expect (targetDisclosures profile bit guess) fun disclose =>
        tableReward table (sourceResults (finalConfig bit guess disclose).state) who := by
  rw [runInteractionPlan_append, bob_to_alice, decoded_alice_response, PMF.map_comp,
    PMF.bind_map, expect_bind_tower _ _ _ (Enforcement.executionUtility_integrable table who _)]
  apply expect_congr_on_support
  intro disclose _
  exact Enforcement.alice_service_value table _ bit guess disclose who

theorem bob_finish_value (table : PayoffTable)
    (profile : Profile restrictedModel.behavioralSignature) (bit : Bool) (who : Player) :
    expect (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler
      (restrictedMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler profile)
      (some ⟨9, some bob, quietBob bit⟩))
        (fun state => Enforcement.stateUtility table state who) =
      expect (targetGuesses profile) fun guess =>
        expect (targetDisclosures profile bit guess) fun disclose =>
          tableReward table (sourceResults (finalConfig bit guess disclose).state) who := by
  have finish := native_finish_response
    (restrictedMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler profile)
    [.player alice, .player watcher, .wire, .grant bobPublication]
    ([.includeLatest bobPublication bob, .tick, .expire bobPublication,
      .grant alicePublication, .player alice] ++ resolutionTail) bob rfl (quietBob bit) rfl
  change nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler _
    (some ⟨9, some bob, quietBob bit⟩) = _ at finish
  rw [finish, decoded_bob_response, PMF.bind_map,
    expect_bind_tower _ _ _ (Enforcement.stateUtility_integrable table who _)]
  apply expect_congr_on_support
  intro guess _
  rw [Function.comp_apply, expect_map]
  exact bob_choice_value table profile bit guess who

theorem targetDisclosures_update_bob (profile : Profile restrictedModel.behavioralSignature)
    (alternative : restrictedModel.BehavioralPolicy bob) (bit guess : Bool) :
    targetDisclosures (Profile.update profile bob alternative) bit guess =
      targetDisclosures profile bit guess := by
  simp only [targetDisclosures, ReactiveApplication.ResponseMenu.decodeProfile,
    Profile.update_of_ne _ _ (by decide : alice ≠ bob)]

theorem alice_context_value (table : PayoffTable)
    (assessment : restrictedModel.BehavioralAssessment)
    (site : restrictedModel.InformationSite alice) (bit guess : Bool)
    (siteEq : site.1 = aliceInput bit guess)
    (alternative : restrictedModel.BehavioralPolicy alice) :
    (assessment.truncatedContinuationContext site
      (fun history => Enforcement.stateUtility table history.state alice)
        (2 * nativeHorizon + 1)).value alternative =
      expect (targetDisclosures (Profile.update assessment.strategy alice alternative) bit guess)
        fun disclose => tableReward table (sourceResults (finalConfig bit guess disclose).state)
          alice := by
  rw [restrictedMenu.context_value_of_known_state nativeInitialLaw nativeHorizon nativeScheduler
    assessment alice site (fun state => Enforcement.stateUtility table state alice) alternative
      (some ⟨4, some alice, beforeAlice bit guess⟩) (fun history =>
        final_alice_known_state bit guess ⟨history.1, history.2.trans siteEq⟩)]
  exact alice_finish_value table _ bit guess alice

theorem receiver_context_value (table : PayoffTable)
    (assessment : restrictedModel.BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent
      restricted_decisionRecall.decisionInformationAntichain)
    (site : restrictedModel.InformationSite bob)
    (alternative : restrictedModel.BehavioralPolicy bob) :
    (assessment.truncatedContinuationContext site
      (fun history => Enforcement.stateUtility table history.state bob)
        (2 * nativeHorizon + 1)).value alternative =
      expect (PMF.uniformOfFintype Bool) fun bit =>
        expect (targetGuesses (Profile.update assessment.strategy bob alternative)) fun guess =>
          expect (targetDisclosures assessment.strategy bit guess) fun disclose =>
            tableReward table (sourceResults (finalConfig bit guess disclose).state) bob := by
  rw [bob_context_value assessment consistent site
    (fun state => Enforcement.stateUtility table state bob) alternative]
  apply expect_congr_on_support
  intro bit _
  rw [bob_finish_value]
  simp only [targetDisclosures_update_bob]

end Vegas.Examples.MonitoredGuessing.Restricted
