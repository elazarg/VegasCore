/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions
import Interaction

/-! # Foundations proof dependency regressions -/

/-- info: 'GameTheory.Protocol.PublicScheduler.expanded_sequentialEquilibrium' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.PublicScheduler.expanded_sequentialEquilibrium

/-- info: 'GameTheory.Protocol.InformationModel.ActionRestriction.isεNash_extends_of_debt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.InformationModel.ActionRestriction.isεNash_extends_of_debt

/-- info: 'GameTheory.Math.Probability.eventProbability_foldl_ge_prod' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Math.Probability.eventProbability_foldl_ge_prod

/-- info: 'Interaction.ReactiveApplication.runRounds_eventProbability_ge_pow' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.runRounds_eventProbability_ge_pow

/-- info: 'Interaction.ReactiveApplication.runUntil_eventProbability_ge_pow' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.runUntil_eventProbability_ge_pow

open GameTheory.Protocol in
/-- info:
'GameTheory.Protocol.InformationModel.ActionRestriction.exists_consistent_restricted_extension_unclocked'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InformationModel.ActionRestriction.exists_consistent_restricted_extension_unclocked

/-- info: 'Interaction.ReactiveApplication.schedulerMixture_joint' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.schedulerMixture_joint

/-- info: 'GameTheory.Protocol.InformationModel.runBehavioralUntil_map_eq_of_paired_steps' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.InformationModel.runBehavioralUntil_map_eq_of_paired_steps

/-- info: 'Interaction.ReactiveApplication.schedulerMixture_unread_execution' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.schedulerMixture_unread_execution

/-- info: 'Interaction.ReactiveApplication.ResponseMenu.runBehavioralUntil_embed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.ResponseMenu.runBehavioralUntil_embed

/-- info: 'Interaction.ReactiveApplication.schedulerMixture_occupation_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.schedulerMixture_occupation_joint

/-- info: 'Interaction.ReactiveApplication.schedulerMixture_runUntil_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.schedulerMixture_runUntil_joint

/-- info: 'Interaction.ReactiveApplication.ResponseMenu.bayesBelief_state_eq_occupationPosterior'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.ResponseMenu.bayesBelief_state_eq_occupationPosterior

/-- info: 'Interaction.ReactiveApplication.schedulerMixture_beforeResponse_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.schedulerMixture_beforeResponse_joint

/-- info: 'GameTheory.Enforcement.exists_positive_collection_floor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Enforcement.exists_positive_collection_floor

/-- info: 'GameTheory.GameForm.exists_positive_mixed_collection_floor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.GameForm.exists_positive_mixed_collection_floor

/-- info: 'GameTheory.DisclosureReliability.exists_uniform_reliability_forfeit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.DisclosureReliability.exists_uniform_reliability_forfeit

/-- info: 'Interaction.ReactiveApplication.complete_decision_submitted_visible' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.complete_decision_submitted_visible

/-- info: 'GameTheory.Protocol.PublicationFailure.outageRun_totalVariation_lower_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.PublicationFailure.outageRun_totalVariation_lower_bound

/-- info: 'GameTheory.Protocol.InformationModel.AsymptoticHistoryLikelihood.belief_face'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.InformationModel.AsymptoticHistoryLikelihood.belief_face

/-- info: 'Interaction.ReactiveApplication.emitted_zero_has_no_prior_outputs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.emitted_zero_has_no_prior_outputs

/-- info: 'Interaction.ReactiveApplication.ResponseMenu.exists_sequentialEquilibrium'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.ResponseMenu.exists_sequentialEquilibrium

/-- info: 'Interaction.ReactiveApplication.continuation_policy_independent_of_unactivated'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.continuation_policy_independent_of_unactivated

/-- info: 'Interaction.ReactiveApplication.ResponseMenu.run_last_response_of_unactivated'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.ResponseMenu.run_last_response_of_unactivated

/-- info: 'Interaction.ReactiveApplication.receipt_identifiers_distinct_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.receipt_identifiers_distinct_history

/-- info: 'Interaction.ReactiveApplication.rejected_identifier_not_accepted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.rejected_identifier_not_accepted

/-- info: 'GameTheory.Math.Probability.eventProbability_le_of_two_value_comparisons'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Math.Probability.eventProbability_le_of_two_value_comparisons

/-- info: 'Interaction.ReactiveApplication.traffic_envelope_eq_ledger_of_id_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.traffic_envelope_eq_ledger_of_id_eq

/-- info: 'Interaction.ReactiveApplication.eraseRecall_runRounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.eraseRecall_runRounds

/-- info: 'Interaction.ReactiveApplication.resume_disintegrate_profile'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.resume_disintegrate_profile

/-- info: 'Interaction.ReactiveApplication.round_disintegrate_profile'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.round_disintegrate_profile

/-- info:
'Interaction.ReactiveApplication.Scheduler.exists_observation_law_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.Scheduler.exists_observation_law_iff

/-- info:
'GameTheory.Enforcement.TerminalAudit.settlement_eq_pure_iff_zero_deductions'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Enforcement.TerminalAudit.settlement_eq_pure_iff_zero_deductions

/-- info:
'GameTheory.Protocol.InformationModel.exists_consistent_player_completion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.InformationModel.exists_consistent_player_completion

/-- info:
'GameTheory.Protocol.InformationModel.exists_consistent_full_support_player_completion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.InformationModel.exists_consistent_full_support_player_completion

/-- info: 'Interaction.ReactiveApplication.ResponseMenu.bayesBelief_seededOccupation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.ResponseMenu.bayesBelief_seededOccupation

/-- info: 'Interaction.ReactiveApplication.schedulerMixture_finish_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.schedulerMixture_finish_joint

/-- info: 'GameTheory.Protocol.InformationModel.abs_expect_runBehavioralUntil_sub_le_of_stepTV'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.InformationModel.abs_expect_runBehavioralUntil_sub_le_of_stepTV

/-- info: 'Interaction.ReactiveApplication.ResponseMenu.recorded_response_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.ResponseMenu.recorded_response_prefix

/-- info: 'GameTheory.Math.Probability.abs_expect_affine_sub_le_of_decorrelated'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Math.Probability.abs_expect_affine_sub_le_of_decorrelated

/-- info: 'GameTheory.Protocol.InformationModel.freeKeyed_memberGain_le_of_common_values'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.InformationModel.freeKeyed_memberGain_le_of_common_values

/-- info: 'Interaction.ReactiveApplication.AddressedScheduler.realize_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.AddressedScheduler.realize_joint

/-- info: 'Interaction.ReactiveApplication.AddressedScheduler.posterior_given_remainder'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.AddressedScheduler.posterior_given_remainder

/-- info: 'Interaction.ReactiveApplication.AddressedScheduler.command_rectangle_transcript'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.AddressedScheduler.command_rectangle_transcript

/-- info: 'Interaction.ReactiveApplication.AddressedScheduler.coordinateTranscriptFrom_append'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.AddressedScheduler.coordinateTranscriptFrom_append

/-- info:
'Interaction.ReactiveApplication.AddressedScheduler.posterior_splitAt_of_coordinate_constraint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Interaction.ReactiveApplication.AddressedScheduler.posterior_splitAt_of_coordinate_constraint

/-- info: 'Interaction.ReactiveApplication.runRounds_environment_boundary'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.runRounds_environment_boundary

/-- info:
'Interaction.ReactiveApplication.history_mem_support_runBehavioral_of_consistent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.history_mem_support_runBehavioral_of_consistent

/-- info:
'Interaction.ReactiveApplication.ResponseMenu.recorded_response_supported'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.ResponseMenu.recorded_response_supported

/-- info:
'Interaction.ReactiveApplication.transition_environment_apply'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.transition_environment_apply

/-- info:
'GameTheory.Protocol.InformationModel.sum_contribution_le_of_repair'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.InformationModel.sum_contribution_le_of_repair

/-- info:
'Interaction.ReactiveApplication.ResponseMenu.bayesBelief_eq_recallReplay'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.ResponseMenu.bayesBelief_eq_recallReplay

/-- info:
'Interaction.ReactiveApplication.ResponseMenu.terminal_run_eq_finish'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.ResponseMenu.terminal_run_eq_finish

/-- info:
'Interaction.ReactiveApplication.ResponseMenu.terminal_run_restrict_eq_finish'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.ResponseMenu.terminal_run_restrict_eq_finish

/-- info:
'Interaction.ReactiveApplication.ResponseMenu.terminal_run_restrict_eq_rounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.ResponseMenu.terminal_run_restrict_eq_rounds

/-- info:
'Interaction.ReactiveApplication.runRounds_policyMixtures'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.runRounds_policyMixtures

/-- info:
'Interaction.ReactiveApplication.runRounds_policyMixtures_posterior_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.runRounds_policyMixtures_posterior_joint

/-- info:
'Interaction.ReactiveApplication.runRounds_policyMixtures_entry_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.runRounds_policyMixtures_entry_joint

/-- info:
'Interaction.ReactiveApplication.ResponseMenu.recorded_response_at'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.ResponseMenu.recorded_response_at

/-- info:
'Interaction.ReactiveApplication.ResponseMenu.recorded_responses_at'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.ResponseMenu.recorded_responses_at

/-- info:
'Interaction.ReactiveApplication.policyMixture_member_consistent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.policyMixture_member_consistent

/-- info:
'Interaction.ReactiveApplication.policyMixture_posterior_independent_left'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.policyMixture_posterior_independent_left

/-- info:
'Interaction.ReactiveApplication.policyMixture_posterior_map'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.policyMixture_posterior_map

/-- info:
'Interaction.ReactiveApplication.policyMixture_posterior_coordinate'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.policyMixture_posterior_coordinate

/-- info:
'GameTheory.Protocol.InformationModel.freeKeyedComponent_transform'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.InformationModel.freeKeyedComponent_transform

/-- info:
'GameTheory.Protocol.InformationModel.ownedKeyedIdentify_at_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.InformationModel.ownedKeyedIdentify_at_eq

/-- info:
'GameTheory.Protocol.InformationModel.bind_freeKeyedComponent_map_eq_of_not_free'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.InformationModel.bind_freeKeyedComponent_map_eq_of_not_free

/-- info:
'GameTheory.Protocol.InformationModel.freeKeyedPool_eq_of_not_free'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.InformationModel.freeKeyedPool_eq_of_not_free

/-- info:
'GameTheory.Protocol.InformationModel.ownedKeyedIdentify'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.InformationModel.ownedKeyedIdentify

/-- info:
'GameTheory.Protocol.InformationModel.freeKeyedComponent_of_ownedKeyed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.InformationModel.freeKeyedComponent_of_ownedKeyed

/-- info:
'GameTheory.Math.Probability.mul_fiberPosterior_map_snd_apply'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Math.Probability.mul_fiberPosterior_map_snd_apply

/-- info:
'GameTheory.Math.Probability.fiberPosterior_hierarchical_pair'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Math.Probability.fiberPosterior_hierarchical_pair

/-- info:
'Interaction.ReactiveApplication.policyMixture_hierarchical'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.policyMixture_hierarchical

/-- info:
'Interaction.ReactiveApplication.policyMixture_consistent_of_supported_member'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.policyMixture_consistent_of_supported_member

/-- info:
'Interaction.ReactiveApplication.anchoredPolicy_consistent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.anchoredPolicy_consistent

/-- info:
'Interaction.ReactiveApplication.anchoredPolicy_mixture_posterior'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.anchoredPolicy_mixture_posterior

/-- info:
'Interaction.ReactiveApplication.runUntil_anchoredPolicy_of_extends'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.runUntil_anchoredPolicy_of_extends

/-- info:
'Interaction.ReactiveApplication.ResponseMenu.anchoredPolicy_covered'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.ResponseMenu.anchoredPolicy_covered

/-- info:
'Interaction.ReactiveApplication.response_action_disintegrate_profile'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.response_action_disintegrate_profile

/-- info:
'Interaction.ReactiveApplication.ResponseMenu.exists_response_history_kernel'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.ResponseMenu.exists_response_history_kernel

/-- info:
'Interaction.ReactiveApplication.ResponseMenu.runUntil_policyMixtures_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.ResponseMenu.runUntil_policyMixtures_joint

/-- info:
'Interaction.ReactiveApplication.policyMixture_posterior_congr_atoms'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.policyMixture_posterior_congr_atoms

/-- info:
'Interaction.ReactiveApplication.policyMixture_posterior_independent_left_atoms'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.policyMixture_posterior_independent_left_atoms

/-- info:
'Interaction.ReactiveApplication.ResponseMenu.runUntil_foreign_anchored'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.ResponseMenu.runUntil_foreign_anchored

/-- info:
'Interaction.ReactiveApplication.policyMixture_posterior_coordinate_extra'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.policyMixture_posterior_coordinate_extra

/-- info:
'Interaction.ReactiveApplication.anchoredPolicy_owner_congr'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.anchoredPolicy_owner_congr

/-- info:
'GameTheory.Protocol.InformationModel.runBehavioralUntil_eq_bind_runBehavioralUntil'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.InformationModel.runBehavioralUntil_eq_bind_runBehavioralUntil

/-- info:
'Interaction.ReactiveApplication.runRounds_policyMixtures_scheduler_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.runRounds_policyMixtures_scheduler_joint

/-- info:
'GameTheory.Protocol.ExecutionProtocol.ReachesWithin.tracePrefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.ExecutionProtocol.ReachesWithin.tracePrefix

/-- info:
'GameTheory.Protocol.InformationModel.ownPlayReachProbability_ofFn'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.InformationModel.ownPlayReachProbability_ofFn

/-- info:
'GameTheory.Protocol.InformationModel.exists_continuation_ownPlay_factor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.InformationModel.exists_continuation_ownPlay_factor

/-- info:
'GameTheory.Protocol.InformationModel.runBehavioralUntil_support_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.InformationModel.runBehavioralUntil_support_prefix

/-- info:
'GameTheory.Protocol.InformationModel.runBehavioralUntil_apply_of_first_hit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.InformationModel.runBehavioralUntil_apply_of_first_hit

/-- info:
'GameTheory.Protocol.InformationModel.runBehavioralUntil_support_first'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.InformationModel.runBehavioralUntil_support_first

/-- info:
'Interaction.ReactiveApplication.policyMixture_likelihood_density'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.policyMixture_likelihood_density

/-- info:
'Interaction.ReactiveApplication.policyMixture_likelihood_expect'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.policyMixture_likelihood_expect

/-- info:
'Interaction.ReactiveApplication.privateTranscriptFrom_product'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.privateTranscriptFrom_product

/-- info:
'Interaction.ReactiveApplication.policyMixture_marked_likelihood_expect'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.policyMixture_marked_likelihood_expect

/-- info:
'GameTheory.Math.Probability.expect_independentProduct_prod'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Math.Probability.expect_independentProduct_prod

/-- info:
'Interaction.ReactiveApplication.ResponseMenu.restrictPolicy_atom'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.ResponseMenu.restrictPolicy_atom

/-- info:
'Interaction.ReactiveApplication.ResponseMenu.ownPlayFrom_restrictPolicy'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.ResponseMenu.ownPlayFrom_restrictPolicy

/-- info:
'GameTheory.Protocol.InformationModel.continuation_ownPlay_factor_unique'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.InformationModel.continuation_ownPlay_factor_unique

/-- info:
'Interaction.ReactiveApplication.ResponseMenu.counterfactual_of_history_factor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.ResponseMenu.counterfactual_of_history_factor

/-- info:
'Interaction.ReactiveApplication.schedulerMixture_trace_fixed_seed'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.schedulerMixture_trace_fixed_seed

/-- info: 'GameTheory.FailureReward.supported_exclusion_free' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.FailureReward.supported_exclusion_free

/-- info: 'GameTheory.FailureReward.exclusion_probabilities' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.FailureReward.exclusion_probabilities

/-- info:
'Interaction.ReactiveApplication.complete_decision_inputs_eq_nil'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.complete_decision_inputs_eq_nil

/-- info:
'Interaction.ReactiveApplication.empty_inputs_recorded_silent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.empty_inputs_recorded_silent
