/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.RestrictedPolicy
import Vegas.Examples.MonitoredGuessing.SourceEvaluation

/-! # Exact decision lotteries of arbitrary restricted policies

At the exhaustive receiver and final sender checkpoints, every legal response
is uniquely a source Boolean decision. Decoding those lotteries therefore loses
no policy choice. This also applies to unilateral policy deviations.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

def actionDisclosure (response : nativeApp.Action) : Bool := response.transmission.isSome

theorem action_disclosure_choice (event : nativeGraph.EventId) (handle : Handle nativeGraph)
    (value disclose : Bool) :
    actionDisclosure (choiceAction event handle value disclose) = disclose := by
  cases disclose <;> rfl

def targetGuesses (profile : Profile restrictedModel.behavioralSignature) : PMF Bool :=
  (restrictedMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler profile bob
    ((quietBob false).recall bob) ((quietBob false).observe nativeApp bob)).map actionDisclosure

def targetDisclosures (profile : Profile restrictedModel.behavioralSignature)
    (bit guess : Bool) : PMF Bool :=
  (restrictedMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler profile alice
    ((beforeAlice bit guess).recall alice)
    ((beforeAlice bit guess).observe nativeApp alice)).map actionDisclosure

theorem decoded_bob_response (profile : Profile restrictedModel.behavioralSignature)
    (bit : Bool) :
    restrictedMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler profile bob
      ((quietBob bit).recall bob) ((quietBob bit).observe nativeApp bob) =
        (targetGuesses profile).map (choiceAction bobPublication bobHandle true) := by
  classical
  rw [quiet_bob_recall, quiet_bob_observation]
  unfold targetGuesses
  rw [PMF.map_comp]
  symm
  calc
    _ = (restrictedMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler profile bob
        [] ((quietBob false).observe nativeApp bob)).map id := by
      apply map_congr_on_support _
      intro response supported
      have available := restrictedMenu.decode_embedPolicy_covered nativeInitialLaw nativeHorizon
        nativeScheduler bob (profile bob) [] ((quietBob false).observe nativeApp bob)
        response supported
      change response ∈ restrictedMenu.actions bob ((quietBob false).recall bob)
        ((quietBob false).observe nativeApp bob) at available
      rw [bob_actions, Finset.mem_insert, Finset.mem_singleton] at available
      rcases available with rfl | rfl <;> rfl
    _ = _ := PMF.map_id _

theorem decoded_alice_response (profile : Profile restrictedModel.behavioralSignature)
    (bit guess : Bool) :
    restrictedMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler profile alice
      ((beforeAlice bit guess).recall alice) ((beforeAlice bit guess).observe nativeApp alice) =
        (targetDisclosures profile bit guess).map
          (choiceAction alicePublication aliceHandle bit) := by
  classical
  unfold targetDisclosures
  rw [PMF.map_comp]
  symm
  calc
    _ = (restrictedMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler profile alice
        ((beforeAlice bit guess).recall alice)
        ((beforeAlice bit guess).observe nativeApp alice)).map id := by
      apply map_congr_on_support _
      intro response supported
      have available := restrictedMenu.decode_embedPolicy_covered nativeInitialLaw nativeHorizon
        nativeScheduler alice (profile alice) _ _ response supported
      rw [alice_actions, Finset.mem_insert, Finset.mem_singleton] at available
      rcases available with rfl | rfl <;> rfl
    _ = _ := PMF.map_id _

theorem targetGuesses_responseProfile (guesses : PMF Bool)
    (disclosures : Bool → Bool → PMF Bool) :
    targetGuesses (responseProfile guesses disclosures) = guesses := by
  rw [targetGuesses, decode_responseProfile, responsePolicy_bob, PMF.map_comp]
  have inverse : actionDisclosure ∘ choiceAction bobPublication bobHandle true = id := by
    funext disclose
    exact action_disclosure_choice bobPublication bobHandle true disclose
  rw [inverse, PMF.map_id]

theorem targetDisclosures_responseProfile (guesses : PMF Bool)
    (disclosures : Bool → Bool → PMF Bool) (bit guess : Bool) :
    targetDisclosures (responseProfile guesses disclosures) bit guess = disclosures bit guess := by
  rw [targetDisclosures, decode_responseProfile, responsePolicy_alice, PMF.map_comp]
  have inverse : actionDisclosure ∘ choiceAction alicePublication aliceHandle bit = id := by
    funext disclose
    exact action_disclosure_choice alicePublication aliceHandle bit disclose
  rw [inverse, PMF.map_id]

theorem mixed_branch_summary (players : Player → nativeApp.Policy)
    (bit guess : Bool) (disclosures : PMF Bool)
    (aliceChoice : players alice ((beforeAlice bit guess).recall alice)
      ((beforeAlice bit guess).observe nativeApp alice) =
        disclosures.map (choiceAction alicePublication aliceHandle bit)) :
    (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      ([.includeLatest bobPublication bob, .tick, .expire bobPublication,
        .grant alicePublication, .player alice] ++ resolutionTail)
      ((quietBob bit).respond nativeApp bob (choiceAction bobPublication bobHandle true guess))).map
        (fun final => (nativeResults final.application.config, rejectedAlice final.receipts)) =
      disclosures.map (fun disclose =>
        (sourceResults (finalConfig bit guess disclose).state, false)) := by
  rw [runInteractionPlan_append, bob_to_alice, aliceChoice, PMF.map_comp,
    PMF.bind_map, PMF.map_bind, ← PMF.bind_pure_comp, Function.comp_def]
  apply bind_congr_on_support _
  intro disclose _
  simp only [Function.comp_apply]
  rw [alice_service_summary, source_results]

theorem source_initialized_states_all (profile : Profile sourceModel.behavioralSignature) :
    (sourceModel.runBehavioral profile 3).map History.state =
      (PMF.uniformOfFintype (α := Bool)).bind fun bit =>
        (sourceGuesses profile).bind fun guess =>
          (sourceDisclosures profile bit guess).map fun disclose =>
            (SourcePath.done bit guess disclose).state := by
  change (sourceModel.runBehavioralFrom profile 3 sourceArena.initHistory).map History.state = _
  rw [source_run_states]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, PMF.pure_bind]
  change ((((PMF.uniformOfFintype (α := Bool)).map initialState).map
    (fun state => (some (.inl (sourceSetup.initialConfig state)) : sourceArena.State))).bind
      (sourceKernel profile)).bind (sourceKernel profile) = _
  simp only [PMF.bind_map, PMF.bind_bind]
  apply bind_congr_on_support _
  intro bit _
  have first : sourceBobSite.1 =
      sourceModel.infoOf bob (SourcePath.drawn bit).history.trace :=
    (drawn_bob_info bit false).symm
  simp only [sourceGuesses, sourceDisclosures]
  rw [first, source_info]
  simp only [sourceKernel, sourceDecisionLaw, PMF.bind_map, PMF.map_comp,
    sourceAliceSite, InformationModel.informationSite, source_info]
  rfl

end Vegas.Examples.MonitoredGuessing.Restricted
