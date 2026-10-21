/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions
import Interaction
import Vegas

/-! # Preservation proof dependency regressions -/

/-- info: 'Vegas.concurrentRawSequentialPreservation_of_local_comparisons'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.concurrentRawSequentialPreservation_of_local_comparisons

/-- info: 'Vegas.PhaseProposalQualifiedBinding.stoppedFinish_seed_marginal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PhaseProposalQualifiedBinding.stoppedFinish_seed_marginal

/-- info: 'Vegas.PhaseProposalQualifiedBinding.sampled_base_stopped_marginal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PhaseProposalQualifiedBinding.sampled_base_stopped_marginal

/-- info: 'Vegas.PhaseProposalQualifiedBinding.exists_closing_source_word'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PhaseProposalQualifiedBinding.exists_closing_source_word

/-- info: 'Vegas.phaseProposal_unflagged_value_law_at_retained_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposal_unflagged_value_law_at_retained_binding

/-- info: 'Vegas.SourceServiceSpec.completeAudit_raw_sequentialEquilibrium_preserved'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceServiceSpec.completeAudit_raw_sequentialEquilibrium_preserved

/-- info: 'Vegas.SourceServiceSpec.intended_audited_raw_sequentialEquilibrium' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceServiceSpec.intended_audited_raw_sequentialEquilibrium

/-- info: 'Vegas.SourceServiceSpec.exists_source_deviation_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceServiceSpec.exists_source_deviation_law

/-- info: 'Vegas.AsyncServiceSpec.intended_openingClientProfile_isεNash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.intended_openingClientProfile_isεNash

/-- info: 'Vegas.AsyncServiceSpec.intended_openingExtension_isεNash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.intended_openingExtension_isεNash

/-- info: 'Vegas.AsyncServiceSpec.openingFirstTurn_deviation_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.openingFirstTurn_deviation_bound

/-- info: 'Vegas.asyncDeviation_withheld_readout' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.asyncDeviation_withheld_readout

/-- info: 'Vegas.openingFirstTurn_readout_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.openingFirstTurn_readout_law

/-- info: 'Vegas.EventGraph.runPolicies_concurrentReveals_store' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.runPolicies_concurrentReveals_store

/-- info: 'Vegas.AsyncServiceSpec.isεNash_clientProfile_approximate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.isεNash_clientProfile_approximate

/-- info: 'Vegas.AsyncServiceSpec.intended_clientProfile_isεNash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.intended_clientProfile_isεNash

/-- info: 'Vegas.sourceServiceClientPolicy_raw_admissible' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.sourceServiceClientPolicy_raw_admissible

/-- info: 'Vegas.asyncDeviation_readout_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.asyncDeviation_readout_law

/-- info: 'Vegas.AsyncServiceSpec.firstTurn_deviation_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.firstTurn_deviation_bound

/-- info: 'Vegas.deviatedTurnProfile_roundsFrom_bind_within' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.deviatedTurnProfile_roundsFrom_bind_within

/-- info: 'Vegas.AsyncServiceSpec.isεNash_clientProfile_of_firstTurn_bounds' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.isεNash_clientProfile_of_firstTurn_bounds

/-- info: 'Vegas.AsyncServiceSpec.intended_clientProfile_isεNash_of_firstTurn_bounds' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.intended_clientProfile_isεNash_of_firstTurn_bounds

/-- info: 'Vegas.lateLeak_intended_outcome_not_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateLeak_intended_outcome_not_preserved

/-- info: 'Vegas.lateLeak_not_preserved_for_every_margin' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateLeak_not_preserved_for_every_margin

/-- info: 'Vegas.settleLate_not_preserved_for_every_margin' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.settleLate_not_preserved_for_every_margin

/-- info: 'Vegas.settleLate_intended_outcome_not_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.settleLate_intended_outcome_not_preserved

/-- info: 'Vegas.lateLeak_equilibrium_totalVariation_lower_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateLeak_equilibrium_totalVariation_lower_bound

/-- info: 'Vegas.rosterScheduler_activation_fits' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.rosterScheduler_activation_fits

/-- info: 'Vegas.rosterScheduler_network_independent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.rosterScheduler_network_independent

/-- info: 'Vegas.lateLeak_exists_preserving_dropCharge' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateLeak_exists_preserving_dropCharge

/-- info: 'Vegas.lateLeak_exists_preserving_dropCharge_of_half_reward' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateLeak_exists_preserving_dropCharge_of_half_reward

/-- info: 'Vegas.lateLeak_outcome_preserved_of_rational_bayes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateLeak_outcome_preserved_of_rational_bayes

/-- info: 'Vegas.lateLeak_sequentialEquilibrium_preserved_of_half_reward_costs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateLeak_sequentialEquilibrium_preserved_of_half_reward_costs

/-- info: 'Vegas.lateLeak_exists_preserving_forfeit_without_dropCharge' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateLeak_exists_preserving_forfeit_without_dropCharge

/-- info: 'Vegas.lateLeak_equilibrium_result_not_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateLeak_equilibrium_result_not_preserved

/-- info:
'Vegas.onePacket_intended_raw_sequentialEquilibrium_of_counterparts' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.onePacket_intended_raw_sequentialEquilibrium_of_counterparts

/-- info: 'Vegas.OnePacketOwnInputs.ofAssembled' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.OnePacketOwnInputs.ofAssembled

/-- info: 'Vegas.OnePacketBaseInputs.toBlindInputs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.OnePacketBaseInputs.toBlindInputs

/-- info: 'Vegas.SwapGuard.value_eq_failure_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SwapGuard.value_eq_failure_iff

/-- info:
'Vegas.certificate_irregularResponseMass_le_of_operationally_equal' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.certificate_irregularResponseMass_le_of_operationally_equal

/-- info: 'Vegas.DirectedBindingFrame.binding_trace' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.DirectedBindingFrame.binding_trace

/-- info: 'Vegas.DirectedBindingFrame.normalized_opening_trace' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.DirectedBindingFrame.normalized_opening_trace

/-- info: 'Vegas.publicRecord_of_forced_information' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.publicRecord_of_forced_information

/-- info: 'Vegas.counterpart_of_successful_foreign_bindings' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.counterpart_of_successful_foreign_bindings

/-- info: 'Vegas.binding_success_of_tracePrefix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.binding_success_of_tracePrefix

/-- info: 'Vegas.upperSourceWeight_le_of_paired_steps' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.upperSourceWeight_le_of_paired_steps

/-- info: 'Vegas.completionMass_eq_of_operational_transitions' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.completionMass_eq_of_operational_transitions

/-- info: 'Vegas.repair_binding_history' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.repair_binding_history

/-- info: 'Vegas.counterpart_of_intended_witness_repairs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.counterpart_of_intended_witness_repairs

/-- info: 'Vegas.forcedAgent_of_intended_witness_repairs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.forcedAgent_of_intended_witness_repairs

/-- info: 'Vegas.upperSourceWeight_le_of_paired_responses' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.upperSourceWeight_le_of_paired_responses

/-- info: 'Vegas.reach_le_counterpart_certificate_of_repairs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.reach_le_counterpart_certificate_of_repairs

/-- info: 'Vegas.OnePacketCounterpartInputs.ofBindingRepairs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.OnePacketCounterpartInputs.ofBindingRepairs

/-- info: 'Vegas.onePacket_intended_raw_sequentialEquilibrium_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.onePacket_intended_raw_sequentialEquilibrium_preserved

/-- info: 'Vegas.recoveryFailureRecord_history' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recoveryFailureRecord_history

/-- info: 'Vegas.RecoveryFailureRecord.owesFailure_of_decodedPoint' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryFailureRecord.owesFailure_of_decodedPoint

/-- info: 'Vegas.recovery_excluded_expect_exclusionBase' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_excluded_expect_exclusionBase

/-- info: 'Vegas.recovery_owesFailure_expect_exclusionBase' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_owesFailure_expect_exclusionBase

/-- info: 'Vegas.recovery_gain_eq_zero_of_owes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_gain_eq_zero_of_owes

/-- info: 'Vegas.recovery_exclusionPayoffs_withinTV' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_exclusionPayoffs_withinTV

/-- info: 'Vegas.foreign_ready_prefix_after_ownTurn'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.foreign_ready_prefix_after_ownTurn

/-- info: 'Vegas.firstActivation_response_prefix_of_recall'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.firstActivation_response_prefix_of_recall

/-- info: 'Vegas.recovery_commitment_freshCall'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_commitment_freshCall

/-- info: 'Vegas.RecoveryOnePacket.component_mixture_projected_of_forced_nonlate'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.component_mixture_projected_of_forced_nonlate

/-- info: 'Vegas.recovery_expect_sub_native_debt_stopped_le_foreign_exit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_expect_sub_native_debt_stopped_le_foreign_exit

/-- info: 'Vegas.publicRecord_of_publicExclusionRecord'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.publicRecord_of_publicExclusionRecord

/-- info: 'Vegas.recovery_firstActivation_not_main_of_publicFailure'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_firstActivation_not_main_of_publicFailure

/-- info: 'Vegas.slotTrembledChoice_event_le_of_disjoint_main'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.slotTrembledChoice_event_le_of_disjoint_main

/-- info: 'Vegas.RecoveryOnePacket.nativeComparisonSequence_assembled'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.nativeComparisonSequence_assembled

/-- info: 'Vegas.RecoveryOnePacket.nativeComparisonSequence_bayes'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.nativeComparisonSequence_bayes

/-- info: 'Vegas.RecoveryOnePacket.exists_consistent_completion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.exists_consistent_completion

/-- info: 'Vegas.recovery_expect_sub_native_stopped_le_foreign_exit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_expect_sub_native_stopped_le_foreign_exit

/-- info: 'Vegas.recovery_settlesFreshCalls_environment'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_settlesFreshCalls_environment

/-- info: 'Vegas.recovery_firstActivation_canonical_succeeds_environment'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_firstActivation_canonical_succeeds_environment

/-- info: 'Vegas.RecoveryOnePacket.owingAgent_isSequentiallyRationalAt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.owingAgent_isSequentiallyRationalAt

/-- info: 'Vegas.recoveryExclusionBase_normalization' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recoveryExclusionBase_normalization

/-- info: 'Vegas.lateOpeningPublicCanonical_consistent_public_beliefs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateOpeningPublicCanonical_consistent_public_beliefs

/-- info: 'Vegas.lateOpeningPublic_sender_context_best_response' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateOpeningPublic_sender_context_best_response

/-- info: 'Vegas.lateOpeningPublic_exists_sequential_equilibrium' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateOpeningPublic_exists_sequential_equilibrium

/-- info: 'Vegas.lateOpeningPublic_preserves_intended_sequential_equilibria' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateOpeningPublic_preserves_intended_sequential_equilibria

/-- info: 'Vegas.lateOpeningPublic_twice_reward_preserves_sequential_equilibria' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateOpeningPublic_twice_reward_preserves_sequential_equilibria

/-- info: 'Vegas.lateOpeningPublic_outcome_of_cost_gap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateOpeningPublic_outcome_of_cost_gap

/-- info: 'Vegas.lateLeak_partial_observation_opposite_preferences' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateLeak_partial_observation_opposite_preferences

/-- info: 'Vegas.service_behavioral_outage_not_realized' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.service_behavioral_outage_not_realized

/-- info: 'Vegas.AsyncServiceSpec.firstTurnClientProfile_settlement_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.firstTurnClientProfile_settlement_law

/-- info: 'Vegas.settleLate_opposite_timing_excludes_label' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.settleLate_opposite_timing_excludes_label

/-- info: 'Vegas.encodeDecisionView?_originalReactiveSourceRecall'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.encodeDecisionView?_originalReactiveSourceRecall

/-- info: 'Vegas.supportedSourceResponse_accepted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.supportedSourceResponse_accepted

/-- info: 'Vegas.canonicalContinuation_setup_source_decode'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.canonicalContinuation_setup_source_decode

/-- info: 'Vegas.EventGraph.Config.CompletedOutputAgreement.terminal_store'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.Config.CompletedOutputAgreement.terminal_store

/-- info: 'Vegas.EventGraph.Config.Reachable.foreign_factor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.Config.Reachable.foreign_factor

/-- info: 'Vegas.source_prescribed_terminal_joint_store_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.source_prescribed_terminal_joint_store_law

/-- info: 'Vegas.source_prescribed_terminal_joint_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.source_prescribed_terminal_joint_law

/-- info: 'Vegas.source_prescribed_initialized_audit_clear'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.source_prescribed_initialized_audit_clear

/-- info: 'Vegas.source_prescribed_terminal_settlement_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.source_prescribed_terminal_settlement_law

/-- info:
'Vegas.prescribedReactivePolicy_source_commit_first_opportunity'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.prescribedReactivePolicy_source_commit_first_opportunity

/-- info:
'Vegas.prescribedReactivePolicy_source_reveal_first_opportunity'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.prescribedReactivePolicy_source_reveal_first_opportunity

/-- info:
'Vegas.runPolicies_mode_disclosing_joint_source_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.runPolicies_mode_disclosing_joint_source_law

/-- info:
'Vegas.raw_completion_boundary'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.raw_completion_boundary

/-- info:
'Vegas.EventGraph.normalizedPolicyStep_ownerless'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.normalizedPolicyStep_ownerless

/-- info:
'Vegas.originalReactiveSourceRecall_respond'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.originalReactiveSourceRecall_respond

/-- info:
'Vegas.originalReactiveSourceRecall_posterior_respond_of_no_turn'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.originalReactiveSourceRecall_posterior_respond_of_no_turn

/-- info:
'Vegas.prescribedReactivePolicy_source_recall_response_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.prescribedReactivePolicy_source_recall_response_law

/-- info:
'Vegas.originalReactiveSourceRecall_respond_other'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.originalReactiveSourceRecall_respond_other

/-- info:
'Vegas.originalReactiveSourceRecall_posterior_respond_other'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.originalReactiveSourceRecall_posterior_respond_other

/-- info:
'Vegas.EventGraph.ForeignCompletionSequence.normalizeObservation_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.ForeignCompletionSequence.normalizeObservation_eq

/-- info:
'Vegas.source_prescribed_no_miss_round'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.source_prescribed_no_miss_round

/-- info:
'Vegas.source_prescribed_no_miss_runRounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.source_prescribed_no_miss_runRounds

/-- info:
'Vegas.source_prescribed_initialized_no_miss'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.source_prescribed_initialized_no_miss

/-- info:
'Vegas.source_prescribed_prefix_frontiers'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.source_prescribed_prefix_frontiers

/-- info:
'Vegas.source_prescribed_response_conforming'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.source_prescribed_response_conforming

/-- info:
'Vegas.source_prescribed_policy_conforming'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.source_prescribed_policy_conforming

/-- info:
'Vegas.source_prescribed_packetFacts_runRounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.source_prescribed_packetFacts_runRounds

/-- info:
'Vegas.freshCall_not_due'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.freshCall_not_due

/-- info:
'Vegas.recorded_prescribed_transmission_not_due'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recorded_prescribed_transmission_not_due

/-- info:
'Vegas.due_prescribed_intention_silent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.due_prescribed_intention_silent

/-- info:
'Vegas.source_prescribed_due_binding_impossible'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.source_prescribed_due_binding_impossible

/-- info:
'Vegas.source_prescribed_expiry_frontier'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.source_prescribed_expiry_frontier

/-- info:
'Vegas.source_unilateral_environment_frontier'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.source_unilateral_environment_frontier

/-- info:
'Vegas.source_unilateral_runRounds_frontier'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.source_unilateral_runRounds_frontier

/-- info:
'Vegas.source_unilateral_initialized_frontier'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.source_unilateral_initialized_frontier

/-- info:
'Vegas.source_unilateral_expiry_frontier'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.source_unilateral_expiry_frontier

/-- info:
'Vegas.source_unilateral_round_frontier'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.source_unilateral_round_frontier

/-- info:
'Vegas.encodeDecisionView?_unilateral_public_checkpoint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.encodeDecisionView?_unilateral_public_checkpoint

/-- info: 'Vegas.recovery_committed_stop_sourceLaw'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_committed_stop_sourceLaw

/-- info: 'Vegas.recovery_committed_stop_config'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_committed_stop_config

/-- info: 'Vegas.recovery_stopped_freshCall_receipt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_stopped_freshCall_receipt

/-- info: 'Vegas.pending_publicClear_of_acceptanceInvariant'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.pending_publicClear_of_acceptanceInvariant

/-- info: 'Vegas.RecoveryOnePacket.nativeComparisonStrategy_at_clear'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.nativeComparisonStrategy_at_clear

/-- info: 'Vegas.RecoveryOnePacket.assembledStrategy_projected_of_forced_nonlate'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.assembledStrategy_projected_of_forced_nonlate

/-- info: 'Vegas.recovery_foreign_firstActivation_prefix_of_due'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_foreign_firstActivation_prefix_of_due

/-- info: 'Vegas.foreign_firstActivation_prefix_of_recorded'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.foreign_firstActivation_prefix_of_recorded

/-- info: 'Vegas.firstPublicFailure_pending_or_due'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.firstPublicFailure_pending_or_due

/-- info: 'Vegas.RecoveryOnePacket.component_mixture_event_le_of_disjoint_main'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.component_mixture_event_le_of_disjoint_main

/-- info: 'Vegas.clear_regular_notOwes_of_tracePrefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.clear_regular_notOwes_of_tracePrefix

/-- info: 'Vegas.recovery_firstActivation_commitment_sourceLaw'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_firstActivation_commitment_sourceLaw

/-- info: 'Vegas.recovery_firstActivation_disclosure_sourceLaw'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_firstActivation_disclosure_sourceLaw

/-- info: 'Vegas.recovery_accepted_stop_config'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_accepted_stop_config

/-- info: 'Vegas.RecoveryOnePacket.historyReachWeight_nativeComparison_of_clear'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.historyReachWeight_nativeComparison_of_clear

/-- info: 'Vegas.RecoveryOnePacket.nativeComparison_bayes_formula_of_clear'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.nativeComparison_bayes_formula_of_clear

/-- info: 'Vegas.recovery_firstForeignFailure_not_mainActivationTraceAfter'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_firstForeignFailure_not_mainActivationTraceAfter

/-- info: 'Vegas.RecoveryOnePacket.recovery_belief_eq_nativeComparison'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.recovery_belief_eq_nativeComparison

/-- info: 'Vegas.RecoveryOnePacket.nativeComparison_foreign_exit_mass_le_rank'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.nativeComparison_foreign_exit_mass_le_rank

/-- info: 'Vegas.RecoveryOnePacket.nativeComparison_foreign_exit_mass_le_irregular_add_depth'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.nativeComparison_foreign_exit_mass_le_irregular_add_depth

/-- info: 'Vegas.RecoveryOnePacket.nativeComparison_stopped_update_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.nativeComparison_stopped_update_eq

/-- info: 'Vegas.RecoveryOnePacket.recovery_belief_eq_comparisonInformationHistory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.recovery_belief_eq_comparisonInformationHistory

/-- info: 'Vegas.RecoveryOnePacket.recovery_prefix_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.recovery_prefix_bounds

/-- info: 'Vegas.RecoveryOnePacket.recovery_expect_sub_native_debt_stopped_le_rank'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.recovery_expect_sub_native_debt_stopped_le_rank

/-- info: 'Vegas.RecoveryOnePacket.recovery_irregular_belief_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.recovery_irregular_belief_bounds

/-- info: 'Vegas.RecoveryOnePacket.recovery_belief_expect_abs_sub_native_debt_stopped_le_foreign_exit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.RecoveryOnePacket.recovery_belief_expect_abs_sub_native_debt_stopped_le_foreign_exit

/-- info: 'Vegas.RecoveryOnePacket.exists_comparisonInformationHistory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.exists_comparisonInformationHistory

/-- info: 'Vegas.recovery_firstActivation_honest_sourceLaw'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_firstActivation_honest_sourceLaw

/-- info: 'Vegas.recovery_firstActivation_prescribed_sourceValue'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_firstActivation_prescribed_sourceValue

/-- info: 'Vegas.RecoveryOnePacket.recovery_common_foreign_exit_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.recovery_common_foreign_exit_bounds

/-- info: 'Vegas.RecoveryOnePacket.recovery_common_continuation_error_vanishes'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.recovery_common_continuation_error_vanishes

/-- info: 'Vegas.RecoveryOnePacket.nativeComparison_firstActivation_sourceValue'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.nativeComparison_firstActivation_sourceValue

/-- info: 'Vegas.recovery_boundary_firstActivation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_boundary_firstActivation

/-- info: 'Vegas.recovery_firstActivation_honest_successorBoundary'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_firstActivation_honest_successorBoundary

/-- info: 'Vegas.recovery_chance_sourceContinuation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_chance_sourceContinuation

/-- info: 'Vegas.recovery_chance_stopped_sourceContinuation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_chance_stopped_sourceContinuation

/-- info: 'Vegas.terminalPrefix_readout_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.terminalPrefix_readout_law

/-- info: 'Vegas.recovery_honest_boundary_readout_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_honest_boundary_readout_law

/-- info: 'Vegas.decoded_owesFailure_failedReveals_of_readout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decoded_owesFailure_failedReveals_of_readout

/-- info: 'Vegas.honest_reached_intended_of_readout_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.honest_reached_intended_of_readout_law

/-- info: 'Vegas.RecoveryOnePacket.recovery_common_gain_le_native_debt_stopped'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.recovery_common_gain_le_native_debt_stopped

/-- info: 'Vegas.intendedCommitment_sourcePolicy_gain'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.intendedCommitment_sourcePolicy_gain

/-- info: 'Vegas.RecoveryOnePacket.recovery_keyed_record_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.recovery_keyed_record_bounds

/-- info: 'Vegas.honest_debt_stopped_terminal_law_of_readout_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.honest_debt_stopped_terminal_law_of_readout_law

/-- info: 'Vegas.onePacket_stopped_expect_sub_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.onePacket_stopped_expect_sub_le

/-- info: 'Vegas.recovery_honest_reached_not_late'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_honest_reached_not_late

/-- info: 'Vegas.recovery_pending_stop_completed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_pending_stop_completed

/-- info: 'Vegas.recovery_pending_failure_terminal_eq_stopped'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_pending_failure_terminal_eq_stopped

/-- info: 'Vegas.recovery_stopped_boundary_value_sub_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_stopped_boundary_value_sub_le

/-- info: 'Vegas.RecoveryOnePacket.nativeComparison_dominatesHonestFrom_boundary'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.nativeComparison_dominatesHonestFrom_boundary

/-- info: 'Vegas.recovery_honest_initialized_readout_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_honest_initialized_readout_law

/-- info: 'Vegas.RecoveryOnePacket.recovery_initialized_lawApproximation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.recovery_initialized_lawApproximation

/-- info: 'Vegas.recovery_intended_raw_sequentialEquilibrium_of_onePacket'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_intended_raw_sequentialEquilibrium_of_onePacket

/-- info: 'Vegas.RecoveryOnePacket.nativeComparison_stopped_boundary_value_sub_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.nativeComparison_stopped_boundary_value_sub_le

/-- info: 'Vegas.RecoveryOnePacket.nativeDebtStoppedValue_eq_finite_continuation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.nativeDebtStoppedValue_eq_finite_continuation

/-- info: 'Vegas.RecoveryOnePacket.nativeDebtStoppedValue_localLaw_eq_comparison'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.nativeDebtStoppedValue_localLaw_eq_comparison

/-- info: 'Vegas.RecoveryOnePacket.recovery_common_boundary_value_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.recovery_common_boundary_value_bounds

/-- info: 'Vegas.RecoveryOnePacket.recovery_source_belief_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.recovery_source_belief_bounds

/-- info: 'Vegas.RecoveryOnePacket.nativeComparison_firstActivation_value_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.nativeComparison_firstActivation_value_lower

/-- info: 'Vegas.RecoveryOnePacket.nativeComparison_local_phase_value_sub_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.nativeComparison_local_phase_value_sub_le

/-- info: 'Vegas.RecoveryOnePacket.debtStopped_eq_bind_eventPhase'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.debtStopped_eq_bind_eventPhase

/-- info: 'Vegas.recovery_pending_until_eq_clearUntil'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_pending_until_eq_clearUntil

/-- info: 'Vegas.withLaw_eq_self_of_unpending_notOwing'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.withLaw_eq_self_of_unpending_notOwing

/-- info: 'Vegas.RecoveryOnePacket.localGain_eq_zero_of_unpending_notOwing'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.localGain_eq_zero_of_unpending_notOwing

/-- info: 'Vegas.RecoveryOnePacket.sequentialEquilibrium_of_local_comparisons'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.sequentialEquilibrium_of_local_comparisons

/-- info: 'Vegas.RecoveryOnePacket.pooledLocalGain_nonpos_of_continuation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.pooledLocalGain_nonpos_of_continuation

/-- info: 'Vegas.RecoveryOnePacket.componentGain_le_of_common_values'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.componentGain_le_of_common_values

/-- info: 'Vegas.recovery_committed_sourceKernel'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_committed_sourceKernel

/-- info: 'Vegas.recovery_unintendedCommitment_phase_owes'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_unintendedCommitment_phase_owes

/-- info: 'Vegas.recovery_pending_completionValue_of_stops'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_pending_completionValue_of_stops

/-- info: 'Vegas.recovery_disclosure_sourceValue'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_disclosure_sourceValue

/-- info: 'Vegas.RecoveryOnePacket.recovery_keyed_failure_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.recovery_keyed_failure_bounds

/-- info: 'Vegas.RecoveryOnePacket.recovery_local_value_comparison_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.recovery_local_value_comparison_bounds

/-- info: 'Vegas.recovery_pending_phase_value_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_pending_phase_value_bounds

/-- info: 'Vegas.RecoveryOnePacket.nativeComparison_pending_value_affine'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.nativeComparison_pending_value_affine

/-- info: 'Vegas.RecoveryOnePacket.recovery_keyed_component_value_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.recovery_keyed_component_value_bounds

/-- info: 'Vegas.RecoveryOnePacket.recovery_pooled_member_gain_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.recovery_pooled_member_gain_bounds

/-- info: 'Vegas.RecoveryOnePacket.nativeComparison_firstActivation_commitment_gain_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.nativeComparison_firstActivation_commitment_gain_le

/-- info: 'Vegas.RecoveryOnePacket.nativeComparison_intendedCommitment_history_comparisons'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.nativeComparison_intendedCommitment_history_comparisons

/-- info: 'Vegas.RecoveryOnePacket.nativeComparison_intendedCommitment_belief_comparison'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.nativeComparison_intendedCommitment_belief_comparison

/-- info: 'Vegas.RecoveryOnePacket.nativeComparison_nonlate_pending_comparisons'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.nativeComparison_nonlate_pending_comparisons

/-- info: 'Vegas.RecoveryOnePacket.recovery_nonlate_local_comparisons'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.recovery_nonlate_local_comparisons

/-- info: 'Vegas.certificate_lateCommit_historyDecisionFailure'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.certificate_lateCommit_historyDecisionFailure

/-- info: 'Vegas.certificate_lateCommit_siteDecisionFailure'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.certificate_lateCommit_siteDecisionFailure

/-- info: 'Vegas.RecoveryOnePacket.keyedComponent_gain_le_of_member_mixtures'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.keyedComponent_gain_le_of_member_mixtures

/-- info: 'Vegas.RecoveryOnePacket.nativeComparison_commitment_value_affine'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.nativeComparison_commitment_value_affine

/-- info: 'Vegas.RecoveryOnePacket.nativeComparison_committed_value_sub_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.nativeComparison_committed_value_sub_le

/-- info: 'Vegas.RecoveryOnePacket.nativeComparison_keyed_commitment_comparisons'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.nativeComparison_keyed_commitment_comparisons

/-- info: 'Vegas.RecoveryOnePacket.keyed_main_value_sub_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.keyed_main_value_sub_le

/-- info: 'Vegas.RecoveryOnePacket.lateChoice_eq_pure_opening'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.lateChoice_eq_pure_opening

/-- info: 'Vegas.RecoveryOnePacket.recovery_unintendedCommitment_stopped_value'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.recovery_unintendedCommitment_stopped_value

/-- info: 'Vegas.RecoveryOnePacket.recovery_unintendedCommitment_value_sub_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.recovery_unintendedCommitment_value_sub_le

/-- info: 'Vegas.RecoveryOnePacket.recovery_keyed_local_comparisons'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.recovery_keyed_local_comparisons

/-- info: 'Vegas.RecoveryOnePacket.recovery_local_comparisons'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryOnePacket.recovery_local_comparisons

/-- info: 'Vegas.recovery_intended_raw_sequentialEquilibrium_preserved'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_intended_raw_sequentialEquilibrium_preserved

/-- info: 'Vegas.compiledRuntimePhasePlan_maximal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.compiledRuntimePhasePlan_maximal

/-- info: 'Vegas.compiledCommitPhase_owners'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.compiledCommitPhase_owners

/-- info: 'Vegas.phase_excluded_iff_missing'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_excluded_iff_missing

/-- info: 'Vegas.decodeCommitAttempt_excluded_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decodeCommitAttempt_excluded_eq

/-- info: 'Vegas.decodeCommitAttempt_state_agrees'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decodeCommitAttempt_state_agrees

/-- info: 'Vegas.sourceAttempt_of_completed_bindings'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.sourceAttempt_of_completed_bindings

/-- info: 'Vegas.decodeCommitAttempt_registry_extension'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decodeCommitAttempt_registry_extension

/-- info: 'Vegas.sourceAttempt_of_actual_bindingInclusion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.sourceAttempt_of_actual_bindingInclusion

/-- info: 'Vegas.sourceAttempt_of_actual_bindingEnvironment'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.sourceAttempt_of_actual_bindingEnvironment

/-- info: 'Vegas.reveal_step_of_failureExtension'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.reveal_step_of_failureExtension

/-- info: 'Vegas.sourceClose_of_clean_bindingPhase'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.sourceClose_of_clean_bindingPhase

/-- info: 'Vegas.sourceClose_of_retry_bindingPhase'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.sourceClose_of_retry_bindingPhase

/-- info: 'Vegas.sourceClose_of_exhausted_bindingPhase'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.sourceClose_of_exhausted_bindingPhase

/-- info: 'Vegas.CompiledSuffix.exists_recoveryResidual'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.CompiledSuffix.exists_recoveryResidual

/-- info: 'Vegas.sourceRecovery_of_actual_revealCompletion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.sourceRecovery_of_actual_revealCompletion

/-- info: 'Vegas.sourceRecovery_of_actual_sampleCompletion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.sourceRecovery_of_actual_sampleCompletion

/-- info: 'Vegas.completed_reveal_phase_source_path'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.completed_reveal_phase_source_path

/-- info: 'Vegas.phase_excluded_sequentiallyRationalAt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_excluded_sequentiallyRationalAt

/-- info: 'Vegas.phase_counted_raw_sequentialEquilibrium'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_counted_raw_sequentialEquilibrium

/-- info: 'Vegas.compiledCommitPhase_eq_of_maximal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.compiledCommitPhase_eq_of_maximal

/-- info: 'Vegas.CompiledReadoutSuffix.decode_ret'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.CompiledReadoutSuffix.decode_ret

/-- info: 'Vegas.RecoverySourceCheckpoint.initial'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.initial

/-- info: 'Vegas.RecoverySourceCheckpoint.terminal_readback'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.terminal_readback

/-- info: 'Vegas.revealTail_recovery'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.revealTail_recovery

/-- info: 'Vegas.RecoverySourceCheckpoint.initialized'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.initialized

/-- info: 'Vegas.RecoverySourceCheckpoint.after_reveal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.after_reveal

/-- info: 'Vegas.RecoverySourceCheckpoint.after_sample_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.after_sample_history

/-- info: 'Vegas.RecoverySourceCheckpoint.after_commit_retry'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.after_commit_retry

/-- info: 'Vegas.RecoverySourceCheckpoint.after_commit_clean'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.after_commit_clean

/-- info: 'Vegas.RecoverySourceCheckpoint.after_commit_exhausted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.after_commit_exhausted

/-- info: 'Vegas.RecoverySourceCheckpoint.terminal_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.terminal_history

/-- info: 'Vegas.phaseSourceBindingPolicy_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceBindingPolicy_of_history

/-- info: 'Vegas.CompiledSuffix.revealTailMany'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.CompiledSuffix.revealTailMany

/-- info: 'Vegas.CompiledSuffix.atCommit_of_bindingPhase'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.CompiledSuffix.atCommit_of_bindingPhase

/-- info: 'Vegas.RecoverySourceCheckpoint.normalized'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.normalized

/-- info: 'Vegas.recoverySourceCheckpoint_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recoverySourceCheckpoint_history

/-- info: 'Vegas.phase_run_afterExclusionPolicy_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_run_afterExclusionPolicy_eq

/-- info: 'Vegas.wholePolicyOptimal_of_phasePublicExclusion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.wholePolicyOptimal_of_phasePublicExclusion

/-- info: 'Vegas.phaseSourceView?_succeeds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceView?_succeeds

/-- info: 'Vegas.phaseRecoveryBindingPolicy_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseRecoveryBindingPolicy_of_history

/-- info: 'Vegas.recoverySourceTerminal_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recoverySourceTerminal_history

/-- info: 'Vegas.ProtocolViewSuffix.decode_entry'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ProtocolViewSuffix.decode_entry

/-- info: 'Vegas.RecoverySourceCheckpoint.source_entry_view'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.source_entry_view

/-- info: 'Vegas.fillCommitPrefix_observation_of_ready'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.fillCommitPrefix_observation_of_ready

/-- info: 'Vegas.decodeEventView?_commitPrefix_entry'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decodeEventView?_commitPrefix_entry

/-- info: 'Vegas.commitAttemptCompletions_ownRecall'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.commitAttemptCompletions_ownRecall

/-- info: 'Vegas.decodeCommitAttempt_history_of_clear_phase'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decodeCommitAttempt_history_of_clear_phase

/-- info: 'Vegas.RecoverySourceCheckpoint.filled_prefix_trace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.filled_prefix_trace

/-- info: 'Vegas.fillCommitPrefix_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.fillCommitPrefix_history

/-- info: 'Vegas.RecordedSourceHistory.native_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecordedSourceHistory.native_history

/-- info: 'Vegas.phase_ready_binding_sourceView'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_ready_binding_sourceView

/-- info: 'Vegas.phase_ready_binding_information'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_ready_binding_information

/-- info: 'Vegas.phaseSourceView?_runRounds_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceView?_runRounds_of_history

/-- info: 'Vegas.phaseSourcePolicy_covered'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_covered

/-- info: 'Vegas.phaseSourceStrategy_map_val'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceStrategy_map_val

/-- info: 'Vegas.phaseSourcePolicy_binding_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_binding_of_history

/-- info: 'Vegas.phaseSourcePolicy_opening_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_opening_of_history

/-- info: 'Vegas.phaseSourcePolicy_binding_at_played_information'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_binding_at_played_information

/-- info: 'Vegas.ownerSwap_phaseInput_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ownerSwap_phaseInput_eq

/-- info: 'Vegas.phaseRecoverySlotPolicy_result_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseRecoverySlotPolicy_result_law

/-- info: 'Vegas.phaseRecoverySlotPolicy_result_mass'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseRecoverySlotPolicy_result_mass

/-- info: 'Vegas.phaseSourceSlotStrategy_map_val'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceSlotStrategy_map_val

/-- info: 'Vegas.phaseSourceSlotPolicy_binding_at_played_information'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceSlotPolicy_binding_at_played_information

/-- info: 'Vegas.phaseSourcePerturbedStrategy_fullSupport'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePerturbedStrategy_fullSupport

/-- info: 'Vegas.phaseSourcePerturbedStrategy_ge_main'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePerturbedStrategy_ge_main

/-- info: 'Vegas.exists_phase_source_assessment_completion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.exists_phase_source_assessment_completion

/-- info: 'Vegas.phaseSourcePolicy_result_law_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_result_law_of_history

/-- info: 'Vegas.phaseSourcePerturbedStrategy_result_law_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePerturbedStrategy_result_law_of_history

/-- info: 'Vegas.phaseSourcePerturbedStrategy_result_converges_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePerturbedStrategy_result_converges_of_history

/-- info: 'Vegas.phaseSourceAssessment_binding_limit_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceAssessment_binding_limit_of_history

/-- info: 'Vegas.fillCommitPrefix_intended_completion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.fillCommitPrefix_intended_completion

/-- info: 'Vegas.decodeEventView?_binding_choice'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decodeEventView?_binding_choice

/-- info: 'Vegas.exists_phaseRecoveryBindingChoice'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.exists_phaseRecoveryBindingChoice

/-- info: 'Vegas.phaseRecoveryBindingChoice_supported_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseRecoveryBindingChoice_supported_of_history

/-- info: 'Vegas.phase_ready_binding_bayes_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_ready_binding_bayes_prefix

/-- info:
'Vegas.phaseSourcePerturbedStrategy_silence_probability_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePerturbedStrategy_silence_probability_of_history

/-- info:
'Vegas.phaseSourcePerturbedStrategy_binding_mass'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePerturbedStrategy_binding_mass

/-- info:
'Vegas.phaseSourcePerturbedStrategy_replacement_mass'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePerturbedStrategy_replacement_mass

/-- info:
'Vegas.phaseSourceStrategy_binding_converges_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceStrategy_binding_converges_of_history

/-- info:
'Vegas.phaseSourceAssessment_binding_strategy_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceAssessment_binding_strategy_of_history

/-- info:
'Vegas.phaseSourceAssessment_opening_strategy_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceAssessment_opening_strategy_of_history

/-- info:
'Vegas.compileEventPolicy_source_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.compileEventPolicy_source_law

/-- info:
'Vegas.RecoverySourceCheckpoint.intended_binding_information_of_ready'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.intended_binding_information_of_ready

/-- info:
'Vegas.phaseSourcePolicy_compiled_binding_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_compiled_binding_of_history

/-- info:
'Vegas.phaseSourcePolicy_opening_erasure_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_opening_erasure_of_history

/-- info:
'Vegas.phaseSourcePerturbedStrategy_replacement_ratio'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePerturbedStrategy_replacement_ratio

/-- info:
'Vegas.compileEventPolicy_disclosing_publication_true'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.compileEventPolicy_disclosing_publication_true

/-- info:
'Vegas.decodeEventView?_position'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decodeEventView?_position

/-- info:
'Vegas.phaseSourceMixture_silence_eq_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceMixture_silence_eq_of_history

/-- info:
'Vegas.phaseSourcePolicy_no_silent_binding_recall'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_no_silent_binding_recall

/-- info:
'Vegas.phaseSourcePolicy_binding_silence_law_of_continuing'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_binding_silence_law_of_continuing

/-- info:
'Vegas.phase_compiled_originalConfig_of_clear'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_compiled_originalConfig_of_clear

/-- info:
'Vegas.phaseSourcePolicy_compiled_binding_of_originalConfig'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_compiled_binding_of_originalConfig

/-- info:
'Vegas.fillCommitPrefix_intended_commit_choice'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.fillCommitPrefix_intended_commit_choice

/-- info:
'Vegas.fillCommitPrefix_intended'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.fillCommitPrefix_intended

/-- info:
'Vegas.commit_guard_predicts_of_clear_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.commit_guard_predicts_of_clear_prefix

/-- info:
'Vegas.fillCommitPrefix_intendedFor_of_clear_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.fillCommitPrefix_intendedFor_of_clear_prefix

/-- info:
'Vegas.phase_playerReach_waiting_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_playerReach_waiting_prefix

/-- info:
'Vegas.phaseSourcePerturbedStrategy_waiting_ratio'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePerturbedStrategy_waiting_ratio

/-- info:
'Vegas.exists_phase_repair_noise'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.exists_phase_repair_noise

/-- info:
'Vegas.compiledCommitPrefix_action_admitted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.compiledCommitPrefix_action_admitted

/-- info:
'Vegas.RecoverySourceCheckpoint.filled_prefix_view'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.filled_prefix_view

/-- info:
'Vegas.phase_accepted_binding_source_choice'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_accepted_binding_source_choice

/-- info:
'Vegas.phase_binding_source_choice_admitted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_binding_source_choice_admitted

/-- info:
'Vegas.decodeCommitAttempt_eq_fill_of_clear'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decodeCommitAttempt_eq_fill_of_clear

/-- info:
'Vegas.phaseSourcePerturbedStrategy_opening_wait_before_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePerturbedStrategy_opening_wait_before_binding

/-- info:
'Vegas.phaseSourcePerturbedStrategy_opening_raw_eq_before_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePerturbedStrategy_opening_raw_eq_before_binding

/-- info:
'Vegas.fillCommitPrefix_snoc'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.fillCommitPrefix_snoc

/-- info:
'Vegas.RecoverySourceCheckpoint.initialized_intended'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.initialized_intended

/-- info:
'Vegas.RecoverySourceCheckpoint.normalized_intended'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.normalized_intended

/-- info:
'Vegas.phase_commitPrefix_image_admitted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_commitPrefix_image_admitted

/-- info:
'Vegas.phase_commitPrefix_admitted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_commitPrefix_admitted

/-- info:
'Vegas.phase_handle_commit_admitted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_handle_commit_admitted

/-- info:
'Vegas.phase_environment_commit_admitted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_environment_commit_admitted

/-- info:
'Vegas.phase_handle_intended_checkpoint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_handle_intended_checkpoint

/-- info:
'Vegas.phase_environment_intended_checkpoint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_environment_intended_checkpoint

/-- info:
'Vegas.phase_intended_checkpoint_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_intended_checkpoint_history

/-- info:
'Vegas.phase_repair_callback_pair'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_repair_callback_pair

/-- info:
'Vegas.phase_repair_binding_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_repair_binding_history

/-- info:
'Vegas.phase_playerReach_repair_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_playerReach_repair_prefix

/-- info:
'Vegas.phaseSourcePerturbedStrategy_raw_decomposition'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePerturbedStrategy_raw_decomposition

/-- info:
'Vegas.phaseRawBindingSendingPair.raw_ratio'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseRawBindingSendingPair.raw_ratio

/-- info:
'Vegas.phase_marked_ownPlay_decomposition'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_marked_ownPlay_decomposition

/-- info:
'Vegas.phase_raw_playerReach_prefix_of_floor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_raw_playerReach_prefix_of_floor

/-- info:
'Vegas.phase_ready_binding_intended_information'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_ready_binding_intended_information

/-- info:
'Vegas.phaseSourcePolicy_compiled_binding_of_intended_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_compiled_binding_of_intended_history

/-- info:
'Vegas.RecoverySourceCheckpoint.ready_reveal_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.ready_reveal_prefix

/-- info:
'Vegas.phase_repair_marked_binding_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_repair_marked_binding_history

/-- info:
'Vegas.phase_raw_binding_fiber_mass_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_raw_binding_fiber_mass_le

/-- info:
'Vegas.phase_opponent_raw_binding_mass_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_opponent_raw_binding_mass_le

/-- info:
'Vegas.phase_opponent_raw_binding_share_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_opponent_raw_binding_share_le

/-- info:
'Vegas.exists_phase_opponent_raw_binding_share_vanishes'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.exists_phase_opponent_raw_binding_share_vanishes

/-- info:
'Vegas.phase_clear_historyReach_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_clear_historyReach_eq

/-- info:
'Vegas.phase_clear_fiber_raw_share_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_clear_fiber_raw_share_eq

/-- info:
'Vegas.exists_phase_common_raw_binding_share_vanishes'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.exists_phase_common_raw_binding_share_vanishes

/-- info:
'Vegas.freshCall_within_deadline_of_ready'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.freshCall_within_deadline_of_ready

/-- info:
'Vegas.phaseBindingResponse_native_freshCall'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseBindingResponse_native_freshCall

/-- info:
'Vegas.phase_ready_publication_success'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_ready_publication_success

/-- info:
'Vegas.phaseSourcePolicy_prescribed_of_clear_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_prescribed_of_clear_history

/-- info:
'Vegas.compiled_openingExtension_readyIndependent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.compiled_openingExtension_readyIndependent

/-- info:
'Vegas.phaseSourcePolicy_compiled_consistent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_compiled_consistent

/-- info:
'Vegas.phaseSourcePolicy_compiled_controlLaw'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_compiled_controlLaw

/-- info:
'Vegas.phaseSourcePolicy_exists_paired_compiled_run'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_exists_paired_compiled_run

/-- info:
'Vegas.phase_settlesFreshCalls_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_settlesFreshCalls_history

/-- info:
'Vegas.phase_freshCall_within_deadline_of_ready'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_freshCall_within_deadline_of_ready

/-- info:
'Vegas.phase_due_binding_impossible'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_due_binding_impossible

/-- info:
'Vegas.phaseSourceMixture_nonmissing_reference_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceMixture_nonmissing_reference_of_history

/-- info:
'Vegas.phaseSourceSlotPolicy_atom_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceSlotPolicy_atom_of_history

/-- info:
'Vegas.phaseSourceMixture_source_reference_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceMixture_source_reference_of_history

/-- info:
'Vegas.phase_ready_binding_block_reference'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_ready_binding_block_reference

/-- info:
'Vegas.phaseSourcePolicy_native_initial_store_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_native_initial_store_law

/-- info:
'Vegas.phaseSourcePolicy_native_joint_store_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_native_joint_store_law

/-- info:
'Vegas.phaseSourcePolicy_native_joint_source_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_native_joint_source_law

/-- info:
'Vegas.phaseSourcePolicy_native_joint_payoff_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_native_joint_payoff_law

/-- info:
'Vegas.phaseSourcePolicy_physical_native_joint_store_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_physical_native_joint_store_law

/-- info:
'Vegas.phaseSourcePolicy_physical_joint_source_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_physical_joint_source_law

/-- info:
'Vegas.phaseSourcePolicy_physical_joint_payoff_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_physical_joint_payoff_law

/-- info:
'Vegas.phaseSourceStrategy_terminal_source_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceStrategy_terminal_source_law

/-- info:
'Vegas.phaseSourceStrategy_terminal_clear'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceStrategy_terminal_clear

/-- info:
'Vegas.phaseSourceStrategy_terminal_source_payoff_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceStrategy_terminal_source_payoff_law

/-- info:
'Vegas.phase_recalled_inclusion_window'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_recalled_inclusion_window

/-- info:
'Vegas.phase_recalled_opening_freshCall'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_recalled_opening_freshCall

/-- info:
'Vegas.phase_due_opening_impossible'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_due_opening_impossible

/-- info:
'Vegas.phaseSourcePolicy_handle_clear_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_handle_clear_of_history

/-- info:
'Vegas.phaseSourcePolicy_environmentResult_clear_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_environmentResult_clear_of_history

/-- info:
'Vegas.phaseSourcePolicy_transition_clear_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_transition_clear_of_history

/-- info:
'Vegas.phaseSourcePolicy_clear_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_clear_history

/-- info:
'Vegas.phaseRecoveryBindingResponse_factor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseRecoveryBindingResponse_factor

/-- info:
'Vegas.RecoverySourceCheckpoint.binding_word_prediction_of_ready'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.binding_word_prediction_of_ready

/-- info:
'Vegas.RecoverySourceCheckpoint.binding_word_native_reference_of_ready'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.binding_word_native_reference_of_ready

/-- info:
'Vegas.RecoverySourceCheckpoint.attempt_mem_prefixLaw'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.attempt_mem_prefixLaw

/-- info:
'Vegas.phaseSourceStrategy_converges_of_clear_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceStrategy_converges_of_clear_history

/-- info:
'Vegas.phaseSourceAssessment_strategy_of_clear_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceAssessment_strategy_of_clear_history

/-- info:
'Vegas.phaseSourceAssessment_run_eq_canonical'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceAssessment_run_eq_canonical

/-- info:
'Vegas.phaseSourceAssessment_terminal_run_eq_canonical'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceAssessment_terminal_run_eq_canonical

/-- info:
'Vegas.exists_phase_source_completion_with_history_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.exists_phase_source_completion_with_history_law

/-- info:
'Vegas.phaseSourcePolicy_async_joint_source_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_async_joint_source_law

/-- info:
'Vegas.phaseSourcePolicy_async_joint_payoff_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_async_joint_payoff_law

/-- info:
'Vegas.phaseSourceStrategy_async_terminal_source_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceStrategy_async_terminal_source_law

/-- info:
'Vegas.phaseSourceStrategy_async_terminal_source_payoff_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceStrategy_async_terminal_source_payoff_law

/-- info:
'Vegas.phaseSourceStrategy_async_terminal_clear_uncharged'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceStrategy_async_terminal_clear_uncharged

/-- info:
'Vegas.phaseSourceStrategy_async_terminal_settlement_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceStrategy_async_terminal_settlement_law

/-- info:
'Vegas.exists_phase_source_completion_with_source_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.exists_phase_source_completion_with_source_law

/-- info:
'Vegas.phase_binding_deviation_move_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_binding_deviation_move_of_history

/-- info:
'Vegas.phaseSourceReadout_initialState_eq_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceReadout_initialState_eq_of_history

/-- info:
'Vegas.exists_phase_source_completion_with_initial_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.exists_phase_source_completion_with_initial_law

/-- info:
'Vegas.RecoverySourceCheckpoint.binding_word_response_of_ready'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.binding_word_response_of_ready

/-- info:
'Vegas.phaseCommitWordPolicy_covered'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCommitWordPolicy_covered

/-- info:
'Vegas.phaseCommitWordPolicy_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCommitWordPolicy_binding

/-- info:
'Vegas.phaseCommitWordPolicy_posterior_wait_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCommitWordPolicy_posterior_wait_of_history

/-- info:
'Vegas.phaseCommitWordPolicy_posterior_send_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCommitWordPolicy_posterior_send_of_history

/-- info:
'Vegas.phase_source_history_finite'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_source_history_finite

/-- info:
'Vegas.phase_callback_terminal_outcome'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_callback_terminal_outcome

/-- info:
'Vegas.phase_callback_base_value'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_callback_base_value

/-- info:
'Vegas.phase_localValue_eq_response_continuation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_localValue_eq_response_continuation

/-- info:
'Vegas.phaseRecoveryTimingTaggedLaw_source'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseRecoveryTimingTaggedLaw_source

/-- info:
'Vegas.phaseRecoveryTimingPolicy_result_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseRecoveryTimingPolicy_result_law

/-- info:
'Vegas.phaseSourceTimingPolicy_covered'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceTimingPolicy_covered

/-- info:
'Vegas.phaseSourceTimingStrategy_map_val'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceTimingStrategy_map_val

/-- info:
'Vegas.phaseSourceTimingComponent_fullSupport'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceTimingComponent_fullSupport

/-- info:
'Vegas.phaseTimingComponent_free_converges'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingComponent_free_converges

/-- info:
'Vegas.exists_phase_timing_completion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.exists_phase_timing_completion

/-- info:
'Vegas.phaseSourcePolicy_unsent_binding_protected'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_unsent_binding_protected

/-- info:
'Vegas.phaseSourcePolicy_unsent_opening_protected'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_unsent_opening_protected

/-- info:
'Vegas.phaseSourcePolicy_protected_or_singleton'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourcePolicy_protected_or_singleton

/-- info:
'Vegas.phaseTimingComponent_eq_source_of_canonical_callback'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingComponent_eq_source_of_canonical_callback

/-- info:
'Vegas.phaseTimingAssessment_run_eq_canonical'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingAssessment_run_eq_canonical

/-- info:
'Vegas.phaseTimingAssessment_terminal_run_eq_canonical'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingAssessment_terminal_run_eq_canonical

/-- info:
'Vegas.phaseBindingAction?_word_response'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseBindingAction?_word_response

/-- info:
'Vegas.phaseBindingRecall_completed_action'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseBindingRecall_completed_action

/-- info:
'Vegas.phaseCommitWordPosterior_accepted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCommitWordPosterior_accepted

/-- info:
'Vegas.phase_terminal_payoff_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_terminal_payoff_lower

/-- info:
'Vegas.phase_continuation_value_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_continuation_value_lower

/-- info:
'Vegas.phase_localValue_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_localValue_lower

/-- info:
'Vegas.phaseCommitWordPolicy_runRounds_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCommitWordPolicy_runRounds_joint

/-- info:
'Vegas.phaseCommitWordPolicy_callback_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCommitWordPolicy_callback_joint

/-- info:
'Vegas.phaseCommitWordPolicy_callback_entry_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCommitWordPolicy_callback_entry_joint

/-- info:
'Vegas.phaseCommitWordPolicy_runRounds_replay'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCommitWordPolicy_runRounds_replay

/-- info:
'Vegas.phaseSourceTimingComponent_ge_slot'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceTimingComponent_ge_slot

/-- info:
'Vegas.phaseTimingComponent_ge_slot'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingComponent_ge_slot

/-- info:
'Vegas.phaseTimingComponent_mixture_ge_slot'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingComponent_mixture_ge_slot

/-- info:
'Vegas.phaseSourceBindingData_result_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceBindingData_result_lower

/-- info:
'Vegas.phaseTimingComponent_replacement_ratio_of_floor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingComponent_replacement_ratio_of_floor

/-- info:
'Vegas.phaseTimingComponent_waiting_ratio_of_floor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingComponent_waiting_ratio_of_floor

/-- info:
'Vegas.phaseTimingPlan_realization'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlan_realization

/-- info:
'Vegas.phaseCommitWordRecall_record'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCommitWordRecall_record

/-- info:
'Vegas.phaseCommitWordRecall_accepted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCommitWordRecall_accepted

/-- info:
'Vegas.phaseCommitRecallWord_eq_completed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCommitRecallWord_eq_completed

/-- info:
'Vegas.phaseCommitRecallWord_fill_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCommitRecallWord_fill_history

/-- info:
'Vegas.phaseTimingPlanPolicy_posterior'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_posterior

/-- info:
'Vegas.phaseTimingPlanPolicy_realization'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_realization

/-- info:
'Vegas.phaseTimingAssessment_runRounds_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingAssessment_runRounds_joint

/-- info:
'Vegas.phaseTimingAssessment_observation_posterior'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingAssessment_observation_posterior

/-- info:
'Vegas.compiledCommitPrefix_wordAction_decodable'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.compiledCommitPrefix_wordAction_decodable

/-- info:
'Vegas.phaseTimingComponent_raw_mixture'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingComponent_raw_mixture

/-- info:
'Vegas.phaseTimingComponent_mixture_raw_mixture'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingComponent_mixture_raw_mixture

/-- info:
'Vegas.phaseTimingComponent_mixture_raw_decomposition'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingComponent_mixture_raw_decomposition

/-- info:
'Vegas.phaseBindingSendingPair.timing_record_ratio'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseBindingSendingPair.timing_record_ratio

/-- info:
'Vegas.phaseRawBindingSendingPair.timing_raw_ratio'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseRawBindingSendingPair.timing_raw_ratio

/-- info:
'Vegas.phaseBindingWaitingPair.timing_record_ratio'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseBindingWaitingPair.timing_record_ratio

/-- info:
'Vegas.phaseTimingKey_publicView_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingKey_publicView_eq

/-- info:
'Vegas.phaseUnprotected_iff_of_timingKey_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseUnprotected_iff_of_timingKey_eq

/-- info:
'Vegas.phaseSourceTimingPolicy_opening_eq_source'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceTimingPolicy_opening_eq_source

/-- info:
'Vegas.phaseOpeningResponsePair.timing_record_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseOpeningResponsePair.timing_record_eq

/-- info:
'Vegas.ownPlayReachProbability_append'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ownPlayReachProbability_append

/-- info:
'Vegas.PhaseRepairOwnPlay.timing_reach_ratio'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PhaseRepairOwnPlay.timing_reach_ratio

/-- info:
'Vegas.phase_timing_raw_playerReach_prefix_of_floor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_timing_raw_playerReach_prefix_of_floor

/-- info:
'Vegas.phase_timing_raw_historyReach_prefix_of_floor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_timing_raw_historyReach_prefix_of_floor

/-- info:
'Vegas.phaseOwnRecordAt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseOwnRecordAt

/-- info:
'Vegas.phase_position_records'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_position_records

/-- info:
'Vegas.phaseRawBindingPositionWeight_nonneg'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseRawBindingPositionWeight_nonneg

/-- info:
'Vegas.phase_timing_raw_binding_fiber_mass_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_timing_raw_binding_fiber_mass_le

/-- info:
'Vegas.phase_timing_opponent_raw_binding_mass_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_timing_opponent_raw_binding_mass_le

/-- info:
'Vegas.phase_timing_opponent_raw_binding_share_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_timing_opponent_raw_binding_share_le

/-- info:
'Vegas.phaseTimingAssessment_command_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingAssessment_command_joint

/-- info:
'Vegas.phaseTimingAssessment_occupation_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingAssessment_occupation_joint

/-- info:
'Vegas.phaseTimingAssessment_bayes_plan_posterior'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingAssessment_bayes_plan_posterior

/-- info:
'Vegas.RecoverySourceCheckpoint.binding_owned_word_prediction_of_ready'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.binding_owned_word_prediction_of_ready

/-- info:
'Vegas.RecoverySourceCheckpoint.binding_timing_word_response_of_ready'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.binding_timing_word_response_of_ready

/-- info:
'Vegas.phaseBindingTimingWordResponse_covered'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseBindingTimingWordResponse_covered

/-- info:
'Vegas.phaseBindingTimingWordResponse_apply_eq_of_support'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseBindingTimingWordResponse_apply_eq_of_support

/-- info:
'Vegas.phaseSourceTimingComponent_decoded'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceTimingComponent_decoded

/-- info:
'Vegas.phaseCommitTimingWordPolicy_cases'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCommitTimingWordPolicy_cases

/-- info:
'Vegas.phaseCommitTimingWordPolicy_posterior_consistency_fiber'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCommitTimingWordPolicy_posterior_consistency_fiber

/-- info:
'Vegas.RecoverySourceCheckpoint.binding_timing_word_strategy_of_ready'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.binding_timing_word_strategy_of_ready

/-- info:
'Vegas.phaseTimingWordPlanPolicy'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordPlanPolicy

/-- info:
'Vegas.phaseTimingWordPlanPolicy_cases'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordPlanPolicy_cases

/-- info:
'Vegas.phaseTimingWordPlanPolicy_of_clear_actor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordPlanPolicy_of_clear_actor

/-- info:
'Vegas.phaseTimingWordPlanPolicy_posterior_consistency_fiber'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordPlanPolicy_posterior_consistency_fiber

/-- info:
'Vegas.phaseOperationalRecall_response'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseOperationalRecall_response

/-- info:
'Vegas.phaseBindingWordResponse_physical_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseBindingWordResponse_physical_coupling

/-- info:
'Vegas.phaseBindingWord_missing_eq_of_histories'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseBindingWord_missing_eq_of_histories

/-- info:
'Vegas.phase_source_word_response_physical_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_source_word_response_physical_coupling

/-- info:
'Vegas.phaseBindingTimingWordResponse_physical_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseBindingTimingWordResponse_physical_coupling

/-- info:
'Vegas.phase_source_timing_word_response_physical_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_source_timing_word_response_physical_coupling

/-- info:
'Vegas.exists_phase_timing_raw_binding_share_vanishes'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.exists_phase_timing_raw_binding_share_vanishes

/-- info:
'Vegas.phaseTimingWordPlanPolicy_binding_factor_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordPlanPolicy_binding_factor_of_history

/-- info:
'Vegas.phaseTimingWordPlan_entry_run_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordPlan_entry_run_joint

/-- info:
'Vegas.phaseTimingWordPlan_entry_command_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordPlan_entry_command_joint

/-- info:
'Vegas.phaseTimingWordPlan_entry_occupation_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordPlan_entry_occupation_joint

/-- info:
'Vegas.phaseTimingWordPlan_entry_occupation_posterior'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordPlan_entry_occupation_posterior

/-- info:
'Vegas.phase_binding_clear_command_observation_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_binding_clear_command_observation_law

/-- info:
'Vegas.phase_commit_timing_word_physical_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_commit_timing_word_physical_coupling

/-- info:
'Vegas.phaseBindingTimingWordResponse_at_eligible'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseBindingTimingWordResponse_at_eligible

/-- info:
'Vegas.phaseCommitWordPolicy_canonical_option'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCommitWordPolicy_canonical_option

/-- info:
'Vegas.phaseTimingWordPlanPolicy_paired_of_key'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordPlanPolicy_paired_of_key

/-- info:
'Vegas.phaseTimingWordPlanPolicy_paired_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordPlanPolicy_paired_binding

/-- info:
'Vegas.phase_timing_plan_word_physical_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_timing_plan_word_physical_coupling

/-- info:
'Vegas.phase_timing_plan_word_callback_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_timing_plan_word_callback_coupling

/-- info:
'Vegas.protocolAction_cast'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.protocolAction_cast

/-- info:
'Vegas.phaseTimingWordPlanPolicy_unread'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordPlanPolicy_unread

/-- info:
'Vegas.phaseTimingWordPlanPolicy_posterior_current_part'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordPlanPolicy_posterior_current_part

/-- info:
'Vegas.RecoverySourceCheckpoint.binding_kernel_source_of_ready'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.binding_kernel_source_of_ready

/-- info:
'Vegas.RecoverySourceCheckpoint.timing_word_predicts_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.timing_word_predicts_of_history

/-- info:
'Vegas.RecoverySourceCheckpoint.timing_word_current_joint_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.timing_word_current_joint_of_history

/-- info:
'Vegas.RecoverySourceCheckpoint.timing_word_policy_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.timing_word_policy_of_history

/-- info:
'Vegas.phase_callback_attempt_terminal_outcome'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_callback_attempt_terminal_outcome

/-- info:
'Vegas.phase_callback_attempt_base_value'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_callback_attempt_base_value

/-- info:
'Vegas.phase_localGain_eq_attempt_difference'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_localGain_eq_attempt_difference

/-- info:
'Vegas.phase_localGain_sub_nonretry_difference_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_localGain_sub_nonretry_difference_bound

/-- info:
'Vegas.exists_commitPrefix_attempt_observation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.exists_commitPrefix_attempt_observation

/-- info:
'Vegas.fillCommitPrefix_history_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.fillCommitPrefix_history_prefix

/-- info:
'Vegas.fillCommitPrefix_history_extension_of_ready'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.fillCommitPrefix_history_extension_of_ready

/-- info:
'Vegas.RecoverySourceCheckpoint.surviving_prefix_trace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.surviving_prefix_trace

/-- info:
'Vegas.RecoverySourceCheckpoint.surviving_ready_binding_trace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.surviving_ready_binding_trace

/-- info:
'Vegas.phase_ready_binding_surviving_source'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_ready_binding_surviving_source

/-- info:
'Vegas.word_member_apply'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.word_member_apply

/-- info:
'Vegas.phase_timing_plan_control_word_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_timing_plan_control_word_coupling

/-- info:
'Vegas.phase_timing_plan_history_word_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_timing_plan_history_word_coupling

/-- info:
'Vegas.phase_timing_plan_stopped_word_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_timing_plan_stopped_word_law

/-- info:
'Vegas.phase_timing_plan_word_channel_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_timing_plan_word_channel_of_history

/-- info:
'Vegas.phase_timing_plan_stopped_key_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_timing_plan_stopped_key_law

/-- info:
'Vegas.phase_timing_plan_word_key_channel_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_timing_plan_word_key_channel_of_history

/-- info:
'Vegas.decodeCommitAttempt_history_of_surviving_owner'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decodeCommitAttempt_history_of_surviving_owner

/-- info:
'Vegas.RecoverySourceCheckpoint.retry_phase_archive'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.retry_phase_archive

/-- info:
'Vegas.RecoverySourceCheckpoint.normalized_archived'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.normalized_archived

/-- info:
'Vegas.RecoverySourceCheckpoint.initialized_archived'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.initialized_archived

/-- info:
'Vegas.RecoverySourceCheckpoint.filled_prefix_archived_history_of_ready'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.filled_prefix_archived_history_of_ready

/-- info:
'Vegas.phaseTimingWordPlanPolicy_eq_of_other_attempt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordPlanPolicy_eq_of_other_attempt

/-- info:
'Vegas.phaseTimingWordPlanPolicy_entry_joint_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordPlanPolicy_entry_joint_of_history

/-- info:
'Vegas.phaseTimingWordPlanPolicy_consistent_of_original_run'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordPlanPolicy_consistent_of_original_run

/-- info:
'Vegas.RecoverySourceCheckpoint.timing_word_policy_of_original_run'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.timing_word_policy_of_original_run

/-- info:
'Vegas.phase_timing_plan_actor_word_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_timing_plan_actor_word_coupling

/-- info:
'Vegas.phase_attempt_boundary_retry_completed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_attempt_boundary_retry_completed

/-- info:
'Vegas.phaseLocalAttemptBoundary_retry_completed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseLocalAttemptBoundary_retry_completed

/-- info:
'Vegas.phaseTimingWeightsWithExclusionLaw_of_clear'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWeightsWithExclusionLaw_of_clear

/-- info:
'Vegas.phaseTimingComponent_with_exclusionLaw'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingComponent_with_exclusionLaw

/-- info:
'Vegas.phaseTimingWordFocalLaw_update_foreign'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordFocalLaw_update_foreign

/-- info:
'Vegas.phaseTimingWordFocalLaw_eq_of_focal_word'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordFocalLaw_eq_of_focal_word

/-- info:
'Vegas.phaseTimingWordFocalLaw_source_posterior'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordFocalLaw_source_posterior

/-- info:
'Vegas.phaseTimingWordInterventionLaw_update_foreign'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordInterventionLaw_update_foreign

/-- info:
'Vegas.phaseTimingWordInterventionLaw_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordInterventionLaw_eq

/-- info:
'Vegas.phaseTimingWordInterventionLaw_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordInterventionLaw_joint

/-- info:
'Vegas.phaseTimingWordPlanPolicy_config_posterior_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordPlanPolicy_config_posterior_of_history

/-- info:
'Vegas.phaseTimingWordPlanPolicy_entry_posterior_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordPlanPolicy_entry_posterior_of_history

/-- info:
'Vegas.phaseSurvivingSourceView?_of_ready_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSurvivingSourceView?_of_ready_binding

/-- info:
'Vegas.phaseTimingWordForeign_consistent_of_entry_run'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordForeign_consistent_of_entry_run

/-- info:
'Vegas.RecoverySourceCheckpoint.fixed_binding_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.fixed_binding_prefix

/-- info:
'Vegas.RecoverySourceCheckpoint.transfer_of_same_attempt_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.transfer_of_same_attempt_prefix

/-- info:
'Vegas.phaseTimingWordAnchoredRecall_accepted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordAnchoredRecall_accepted

/-- info:
'Vegas.phaseTimingWordAnchoredPolicy_posterior_accepted_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordAnchoredPolicy_posterior_accepted_of_history

/-- info:
'Vegas.phaseTimingWordAnchoredPolicy_posterior_filled_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordAnchoredPolicy_posterior_filled_of_history

/-- info:
'Vegas.phaseTimingWordAnchoredPolicy_next_action_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordAnchoredPolicy_next_action_of_history

/-- info:
'Vegas.phaseTimingWordAnchoredPolicy_unread'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordAnchoredPolicy_unread

/-- info:
'Vegas.phaseTimingWordAnchoredPolicy_posterior_current_part'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordAnchoredPolicy_posterior_current_part

/-- info:
'Vegas.RecoverySourceCheckpoint.timing_word_anchored_predicts_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.timing_word_anchored_predicts_of_history

/-- info:
'Vegas.RecoverySourceCheckpoint.timing_word_anchored_current_joint_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.timing_word_anchored_current_joint_of_history

/-- info:
'Vegas.RecoverySourceCheckpoint.timing_word_anchored_policy_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.timing_word_anchored_policy_of_history

/-- info:
'Vegas.RecoverySourceCheckpoint.saved_position'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.saved_position

/-- info:
'Vegas.phasePrescribedTimingComponent_fullSupport'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phasePrescribedTimingComponent_fullSupport

/-- info:
'Vegas.phasePrescribedTimingComponent_mixture'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phasePrescribedTimingComponent_mixture

/-- info:
'Vegas.exists_phase_prescribed_timing_completion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.exists_phase_prescribed_timing_completion

/-- info:
'Vegas.phaseTimingWordIntervention_entry_source_posterior'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingWordIntervention_entry_source_posterior

/-- info:
'Vegas.decodeCommitAttempt_failedOwners_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decodeCommitAttempt_failedOwners_eq

/-- info:
'Vegas.commitMissingOwners_eq_public_failures'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.commitMissingOwners_eq_public_failures

/-- info:
'Vegas.decodeCommitAttempt_excluded_eq_public_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decodeCommitAttempt_excluded_eq_public_prefix

/-- info:
'Vegas.decodeCommitAttempt_failedOwners_eq_public_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decodeCommitAttempt_failedOwners_eq_public_prefix

/-- info:
'Vegas.RecoverySourceCheckpoint.commit_phase_geometry'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.commit_phase_geometry

/-- info:
'Vegas.RecoverySourceCheckpoint.timing_word_anchored_policy_of_ready'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.timing_word_anchored_policy_of_ready

/-- info:
'Vegas.RecoverySourceCheckpoint.timing_word_anchored_policy_of_fixed_block'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.timing_word_anchored_policy_of_fixed_block

/-- info:
'Vegas.RecoverySourceCheckpoint.timing_word_anchored_policy_at_callback'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.timing_word_anchored_policy_at_callback

/-- info:
'Vegas.decodeCommitAttempt_append'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decodeCommitAttempt_append

/-- info:
'Vegas.decodeCommitAttempt_append_attempt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decodeCommitAttempt_append_attempt

/-- info:
'Vegas.decodeCommitAttempt_view_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decodeCommitAttempt_view_eq

/-- info:
'Vegas.RecoverySourceCheckpoint.timing_word_anchored_stopped_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.timing_word_anchored_stopped_law

/-- info:
'Vegas.decodeCommitAttempt_atRank'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decodeCommitAttempt_atRank

/-- info:
'Vegas.phaseRecoveryTimingTaggedLaw_value_plan_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseRecoveryTimingTaggedLaw_value_plan_of_history

/-- info:
'Vegas.RecoverySourceCheckpoint.timing_word_anchored_stopped_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.timing_word_anchored_stopped_joint

/-- info:
'Vegas.RecoverySourceCheckpoint.timing_word_anchored_stopped_config_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.timing_word_anchored_stopped_config_joint

/-- info:
'Vegas.phaseSourceView?_input_position'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceView?_input_position

/-- info:
'Vegas.phaseSourceView?_ne_recorded_binding_of_unsent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceView?_ne_recorded_binding_of_unsent

/-- info:
'Vegas.phaseRecoveryValueTimingPolicy_word_response'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseRecoveryValueTimingPolicy_word_response

/-- info:
'Vegas.phaseRecoveryValueTimingPolicy_silence_congr'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseRecoveryValueTimingPolicy_silence_congr

/-- info:
'Vegas.phaseRecoveryValueTimingPolicy_silence_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseRecoveryValueTimingPolicy_silence_of_history

/-- info:
'Vegas.decoded_commit_successor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decoded_commit_successor

/-- info:
'Vegas.decodeCommitAttempt_commit_tail'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decodeCommitAttempt_commit_tail

/-- info:
'Vegas.decoded_commit_close_observed_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decoded_commit_close_observed_eq

/-- info:
'Vegas.decoded_commit_source_traces'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decoded_commit_source_traces

/-- info:
'Vegas.decoded_commit_block_source_traces'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decoded_commit_block_source_traces

/-- info:
'Vegas.phaseTimingOwnerWordProfile_channel_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingOwnerWordProfile_channel_eq

/-- info:
'Vegas.RecoverySourceCheckpoint.timing_word_anchored_native_posterior'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.timing_word_anchored_native_posterior

/-- info:
'Vegas.phaseTimingOwnerWordProfile_focal_view_marginal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingOwnerWordProfile_focal_view_marginal

/-- info:
'Vegas.phaseTimingOwnerWordProfile_reference_posterior'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingOwnerWordProfile_reference_posterior

/-- info:
'Vegas.phaseTimingOwnerWordProfile_anchored_focal_view_marginal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingOwnerWordProfile_anchored_focal_view_marginal

/-- info:
'Vegas.RecoverySourceCheckpoint.attempt_saved_rank'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.attempt_saved_rank

/-- info:
'Vegas.RecoverySourceCheckpoint.filled_prefix_saved_rank'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.filled_prefix_saved_rank

/-- info:
'Vegas.phaseSurvivingSourceView?_saved_of_ready_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSurvivingSourceView?_saved_of_ready_binding

/-- info:
'Vegas.phaseTimingPlanPolicy_apply'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_apply

/-- info:
'Vegas.phaseRecoveryValueAssessment_local'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseRecoveryValueAssessment_local

/-- info:
'Vegas.phaseRecoveryValueBindingPolicy_silence'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseRecoveryValueBindingPolicy_silence

/-- info:
'Vegas.phaseTimingPlanPolicy_dispatch'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_dispatch

/-- info:
'Vegas.phaseTimingPlanPolicy_binding_readout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_binding_readout

/-- info:
'Vegas.phaseTimingPlanPolicy_value_binding_congr'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_binding_congr

/-- info:
'Vegas.phaseTimingPlanPolicy_value_silence_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_silence_of_history

/-- info:
'Vegas.phaseTimingPlanPolicy_covered'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_covered

/-- info:
'Vegas.phaseTimingPlanPolicy_opening_congr'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_opening_congr

/-- info:
'Vegas.phaseTimingPlanPolicy_source_coordinate_unread'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_source_coordinate_unread

/-- info:
'Vegas.phaseTimingPlanPolicy_value_posterior_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_posterior_of_history

/-- info:
'Vegas.phaseTimingPlanPolicy_pool_posterior'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_pool_posterior

/-- info:
'Vegas.phaseTimingPlanPolicy_value_joint_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_joint_of_history

/-- info:
'Vegas.phaseTimingPlanPolicy_consistent_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_consistent_of_history

/-- info:
'Vegas.phaseTimingPlanPolicy_value_readout_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_readout_of_history

/-- info:
'Vegas.phaseTimingPlanPolicy_value_strategy_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_strategy_of_history

/-- info:
'Vegas.phaseTimingPlanPolicy_value_callback_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_callback_of_history

/-- info:
'Vegas.phaseTimingPlanPolicy_value_stopped_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_stopped_law

/-- info:
'Vegas.phaseTimingPlanPolicy_value_stopped_memory_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_stopped_memory_joint

/-- info:
'Vegas.phaseTimingPlanPolicy_value_initial_memory_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_initial_memory_joint

/-- info:
'Vegas.RecoverySourceCheckpoint.residual_eq_of_phase_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.residual_eq_of_phase_eq

/-- info:
'Vegas.RecoverySourceCheckpoint.embedding_eq_of_phase_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.embedding_eq_of_phase_eq

/-- info:
'Vegas.phaseSurvivingSourceView?_observed_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSurvivingSourceView?_observed_of_history

/-- info:
'Vegas.RecoverySourceCheckpoint.saved_view_of_ready_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.saved_view_of_ready_binding

/-- info:
'Vegas.RecoverySourceCheckpoint.saved_view_of_seed_request'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.saved_view_of_seed_request

/-- info:
'Vegas.phase_saved_source_views_eq_of_observed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_saved_source_views_eq_of_observed

/-- info:
'Vegas.phase_saved_source_config_views_eq_of_observed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_saved_source_config_views_eq_of_observed

/-- info:
'Vegas.decoded_commit_retry_source_traces'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decoded_commit_retry_source_traces

/-- info:
'Vegas.RecoverySourceCheckpoint.timing_word_anchored_stopped_config_joint_of_initial'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.timing_word_anchored_stopped_config_joint_of_initial

/-- info:
'Vegas.RecoverySourceCheckpoint.timing_word_anchored_stopped_marginal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.timing_word_anchored_stopped_marginal

/-- info:
'Vegas.phaseTimingOwnerWordProfile_memory_focal_view_marginal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingOwnerWordProfile_memory_focal_view_marginal

/-- info:
'Vegas.RecoverySourceCheckpoint.timing_word_anchored_reference_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.timing_word_anchored_reference_law

/-- info:
'Vegas.phaseTimingOwnerWordProfile_memory_projection'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingOwnerWordProfile_memory_projection

/-- info:
'Vegas.phaseTimingOwnerWordProfile_memory_reference_posterior'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingOwnerWordProfile_memory_reference_posterior

/-- info:
'Vegas.RecoverySourceCheckpoint.current_view_mem_prefixLaw'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.current_view_mem_prefixLaw

/-- info:
'Vegas.RecoverySourceCheckpoint.timing_word_literal_reference_input'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.timing_word_literal_reference_input

/-- info:
'Vegas.phaseTimingPlanProfile_tagged_noise_domination'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanProfile_tagged_noise_domination

/-- info:
'Vegas.phaseTimingPlanProfile_tagged_noise_input_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanProfile_tagged_noise_input_bound

/-- info:
'Vegas.phaseTimingComponent_silence_noise_comparison'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingComponent_silence_noise_comparison

/-- info:
'Vegas.phase_clear_profile_queries'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_clear_profile_queries

/-- info:
'Vegas.phase_clear_ownPlay_policy_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_clear_ownPlay_policy_eq

/-- info:
'Vegas.phase_clear_counterfactualReach_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_clear_counterfactualReach_eq

/-- info:
'Vegas.phaseTimingPlanPolicy_value_clear_profile_agreement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_clear_profile_agreement

/-- info:
'Vegas.phaseTimingPlanPolicy_value_bayes_of_clear'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_bayes_of_clear

/-- info:
'Vegas.initialized_recovery_source_information'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.initialized_recovery_source_information

/-- info:
'Vegas.phase_archived_commit_prefix_view_eq_of_observed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_archived_commit_prefix_view_eq_of_observed

/-- info:
'Vegas.phase_archived_commit_signal_eq_of_observed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_archived_commit_signal_eq_of_observed

/-- info:
'Vegas.RecoverySourceCheckpoint.saved_history_of_retained_image'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.saved_history_of_retained_image

/-- info:
'Vegas.RecoverySourceCheckpoint.saved_view_of_retained_image'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.saved_view_of_retained_image

/-- info:
'Vegas.phase_archived_saved_source_views_eq_of_observed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_archived_saved_source_views_eq_of_observed

/-- info:
'Vegas.phaseTimingPlanPolicy_value_silence_base_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_silence_base_of_history

/-- info:
'Vegas.phaseTimingPlanPolicy_value_attempt_entry_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_attempt_entry_joint

/-- info:
'Vegas.phaseTimingPlanPolicy_value_attempt_entry_continuation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_attempt_entry_continuation

/-- info:
'Vegas.phaseTimingPlanPolicy_value_common_attempt_entry_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_common_attempt_entry_joint

/-- info:
'Vegas.phaseTimingComponent_commitment_silence_noise'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingComponent_commitment_silence_noise

/-- info:
'Vegas.phaseTimingComponent_commitment_trimmed_atom'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingComponent_commitment_trimmed_atom

/-- info:
'Vegas.prod_le_trimmed_add_marked'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.prod_le_trimmed_add_marked

/-- info:
'Vegas.phaseTimingComponent_commitment_product_noise'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingComponent_commitment_product_noise

/-- info:
'Vegas.phaseTimingComponent_commitment_ownPlay_noise'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingComponent_commitment_ownPlay_noise

/-- info:
'Vegas.phaseTimingComponent_value_silent_base'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingComponent_value_silent_base

/-- info:
'Vegas.phaseTimingComponent_value_commitment_silence_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingComponent_value_commitment_silence_lower

/-- info:
'Vegas.phaseTimingComponent_value_commitment_trimmed_atom'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingComponent_value_commitment_trimmed_atom

/-- info:
'Vegas.phaseTimingComponent_value_commitment_product_noise'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingComponent_value_commitment_product_noise

/-- info:
'Vegas.ArchivedSourceOrigins.get'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ArchivedSourceOrigins.get

/-- info:
'Vegas.phaseTimingPlanPolicy_value_bayes_entry_passage'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_bayes_entry_passage

/-- info:
'Vegas.phaseTimingPlanPolicy_value_bayes_stopped_passage'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_bayes_stopped_passage

/-- info:
'Vegas.phase_timing_continuation_callback_factor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_timing_continuation_callback_factor

/-- info:
'Vegas.phase_timing_continuation_path_noise'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_timing_continuation_path_noise

/-- info:
'Vegas.phase_timing_continuation_stopped_noise'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_timing_continuation_stopped_noise

/-- info:
'Vegas.phaseTimingPlanPolicy_value_replay_bayes_passage'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_replay_bayes_passage

/-- info:
'Vegas.phaseTimingPlanPolicy_value_replay_input_weights'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_replay_input_weights

/-- info:
'Vegas.phase_timing_continuation_fiber_noise'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_timing_continuation_fiber_noise

/-- info:
'Vegas.phase_timing_continuation_stopped_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_timing_continuation_stopped_lower

/-- info:
'Vegas.phase_timing_continuation_fiber_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_timing_continuation_fiber_lower

/-- info:
'Vegas.phaseTimingPlanPolicy_value_replay_comparison'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_replay_comparison

/-- info:
'Vegas.phaseTimingPlanPolicy_source_coordinate_after_send'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_source_coordinate_after_send

/-- info:
'Vegas.phaseTimingPlanPolicy_prior_part_unread'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_prior_part_unread

/-- info:
'Vegas.phaseTimingPlanPolicy_source_after_send_product'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_source_after_send_product

/-- info:
'Vegas.phaseTimingPlanPolicy_prior_part_product'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_prior_part_product

/-- info:
'Vegas.phaseTimingPlanPolicy_value_coordinates_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_coordinates_of_history

/-- info:
'Vegas.phaseTimingPlanPolicy_response_remainder_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_response_remainder_of_history

/-- info:
'Vegas.phaseTimingPlanPolicy_response_future_product_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_response_future_product_of_history

/-- info:
'Vegas.phaseTimingPlanPolicy_send_future_posterior_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_send_future_posterior_of_history

/-- info:
'Vegas.phaseTimingPlanPolicy_marked_suffix_expect_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_marked_suffix_expect_of_history

/-- info:
'Vegas.phaseTimingPlanPolicy_marked_profile_expect_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_marked_profile_expect_of_history

/-- info:
'Vegas.phaseTimingPlanPolicy_native_mark_expect_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_native_mark_expect_of_history

/-- info:
'Vegas.phaseOperationalView_swap'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseOperationalView_swap

/-- info:
'Vegas.phaseTimingKey_swap_at_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingKey_swap_at_binding

/-- info:
'Vegas.phaseTimingKey_swap_at_opening'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingKey_swap_at_opening

/-- info:
'Vegas.phaseTimingPlanPolicy_opening_swap'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_opening_swap

/-- info:
'Vegas.CompiledSuffix.noncommit_of_sample_phase'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.CompiledSuffix.noncommit_of_sample_phase

/-- info:
'Vegas.RecoverySourceCheckpoint.reveal_information_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.reveal_information_eq

/-- info:
'Vegas.RecoverySourceCheckpoint.sample_information_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.sample_information_eq

/-- info:
'Vegas.phase_archived_source_views_eq_of_observed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_archived_source_views_eq_of_observed

/-- info:
'Vegas.phaseTimingPlanPolicy_value_nonsend_atom_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_nonsend_atom_of_history

/-- info:
'Vegas.phaseTimingPlanPolicy_value_nonsend_posterior_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_nonsend_posterior_of_history

/-- info:
'Vegas.phaseTimingPlanPolicy_value_recall_factors'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_recall_factors

/-- info:
'Vegas.phaseTimingPlanPolicy_value_history_density'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_history_density

/-- info:
'Vegas.phaseTimingPlanPolicy_binding_good_product'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_binding_good_product

/-- info:
'Vegas.phaseTimingPlanPolicy_binding_good_weight'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_binding_good_weight

/-- info:
'Vegas.phaseTimingPlanPolicy_value_history_average'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_history_average

/-- info:
'Vegas.phaseTimingPlanPolicy_value_good_history_average'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_good_history_average

/-- info:
'Vegas.exists_binding_marker_of_tracePrefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.exists_binding_marker_of_tracePrefix

/-- info:
'Vegas.phaseTimingPlanPolicy_marker_sum_expect_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_marker_sum_expect_of_history

/-- info:
'Vegas.phase_binding_marker_sum_counterfactual'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_binding_marker_sum_counterfactual

/-- info:
'Vegas.phase_binding_marker_sum_eq_position'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_binding_marker_sum_eq_position

/-- info:
'Vegas.phase_raw_binding_share_eq_recallReplay'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_raw_binding_share_eq_recallReplay

/-- info:
'Vegas.RecoverySourceCheckpoint.completed_commit_phase'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.completed_commit_phase

/-- info:
'Vegas.RecoverySourceCheckpoint.commit_information_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.commit_information_eq

/-- info:
'Vegas.phase_archived_chosen_information_eq_of_observed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_archived_chosen_information_eq_of_observed

/-- info:
'Vegas.phase_initial_archive_information_eq_of_observed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_initial_archive_information_eq_of_observed

/-- info:
'Vegas.phase_initial_retry_information_eq_of_observed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_initial_retry_information_eq_of_observed

/-- info:
'Vegas.RecoverySourceCheckpoint.chosen_commit_control'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.chosen_commit_control

/-- info:
'Vegas.RecoverySourceCheckpoint.retry_chosen_history_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.retry_chosen_history_eq

/-- info:
'Vegas.phase_initial_saved_information_eq_of_observed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_initial_saved_information_eq_of_observed

/-- info:
'Vegas.phaseTimingPlanPolicy_nonbinding_swap_before_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_nonbinding_swap_before_binding

/-- info:
'Vegas.phaseTimingPlanPolicy_nonbinding_record_swap'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_nonbinding_record_swap

/-- info:
'Vegas.phaseTimingPlanPolicy_value_good_history_native'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_good_history_native

/-- info:
'Vegas.phaseTimingPlanPolicy_value_good_conditional'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_good_conditional

/-- info:
'Vegas.phaseTimingPlanPolicy_value_good_belief'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_good_belief

/-- info:
'Vegas.phaseTimingPlanPolicy_value_good_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_good_binding

/-- info:
'Vegas.exists_phase_value_good_belief_vanishes'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.exists_phase_value_good_belief_vanishes

/-- info:
'Vegas.phaseBindingSlots_swap_of_histories'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseBindingSlots_swap_of_histories

/-- info:
'Vegas.phaseSourceTimingPolicy_binding_silence_swap'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseSourceTimingPolicy_binding_silence_swap

/-- info:
'Vegas.phaseTimingPlanPolicy_binding_residual_silence_swap'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_binding_residual_silence_swap

/-- info:
'Vegas.phaseTimingPlanPolicy_binding_waiting_swap_of_floor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_binding_waiting_swap_of_floor

/-- info:
'Vegas.phaseTimingPlanPolicy_value_binding_waiting_swap_of_floor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_binding_waiting_swap_of_floor

/-- info:
'Vegas.phase_binding_waiting_factor_tendsto'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_binding_waiting_factor_tendsto

/-- info:
'Vegas.phaseTimingPlanPolicy_value_nonsend_record_swap_ratio'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_nonsend_record_swap_ratio

/-- info:
'Vegas.phaseTimingPlanPolicy_value_operational_swap_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseTimingPlanPolicy_value_operational_swap_bounds

/-- info:
'Vegas.RecoverySourceCheckpoint.binding_query_of_clear_completed_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.binding_query_of_clear_completed_prefix

/-- info:
'Vegas.phasePolicyDispatch_covered'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phasePolicyDispatch_covered

/-- info:
'Vegas.phasePolicyDispatch_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phasePolicyDispatch_binding

/-- info:
'Vegas.phasePolicyDispatch_opening'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phasePolicyDispatch_opening

/-- info:
'Vegas.phasePolicyDispatch_apply_eq_of_support'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phasePolicyDispatch_apply_eq_of_support

/-- info:
'Vegas.phasePolicyDispatch_indexed_cases'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phasePolicyDispatch_indexed_cases

/-- info:
'Vegas.phaseCountServicePolicy_covered'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServicePolicy_covered

/-- info:
'Vegas.phaseCountServicePolicy_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServicePolicy_binding

/-- info:
'Vegas.phaseCountServicePolicy_opening'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServicePolicy_opening

/-- info:
'Vegas.phaseCountServicePolicy_binding_tape_realization'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServicePolicy_binding_tape_realization

/-- info:
'Vegas.phaseCountServicePolicy_transmission_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServicePolicy_transmission_of_history

/-- info:
'Vegas.phaseCountServiceTapePolicy_covered'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_covered

/-- info:
'Vegas.phaseCountServiceTapePolicy_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_binding

/-- info:
'Vegas.phaseCountServiceTapePolicy_local_member'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_local_member

/-- info:
'Vegas.phaseCountServiceTapePolicy_local_consistent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_local_consistent

/-- info:
'Vegas.phaseCountServiceTapePolicy_accepted_iff_of_resolved'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_accepted_iff_of_resolved

/-- info:
'Vegas.RecoverySourceCheckpoint.chosen_commit_addresses'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.chosen_commit_addresses

/-- info:
'Vegas.RecoverySourceCheckpoint.chosen_commit_trace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.chosen_commit_trace

/-- info:
'Vegas.compiled_reveal_public_exclusions'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.compiled_reveal_public_exclusions

/-- info:
'Vegas.decodeCommitAttempt_exclusionWord_eq_of_publicView'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decodeCommitAttempt_exclusionWord_eq_of_publicView

/-- info:
'Vegas.decoded_commit_block_chosen_signal_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decoded_commit_block_chosen_signal_eq

/-- info:
'Vegas.phaseCountServiceTapePolicy_foreign_survival_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_foreign_survival_iff

/-- info:
'Vegas.phaseCountServiceTapePolicy_foreign_survivors_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_foreign_survivors_law

/-- info:
'Vegas.phaseVirtualSourceView?_genuine_of_ready_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseVirtualSourceView?_genuine_of_ready_binding

/-- info:
'Vegas.phaseCountServiceTapePolicy_consistent_of_continuation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_consistent_of_continuation

/-- info:
'Vegas.phaseCountServiceTapePolicy_first_send_raw_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_first_send_raw_eq

/-- info:
'Vegas.phaseCountServiceTapePolicy_good_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_good_law

/-- info:
'Vegas.phaseCountServiceTapePolicy_good_survival'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_good_survival

/-- info:
'Vegas.phaseCountServiceTapePolicy_local_member_at'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_local_member_at

/-- info:
'Vegas.phaseCountServiceTapePolicy_rawFree_of_surviving_reference'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_rawFree_of_surviving_reference

/-- info:
'Vegas.phaseCountServiceTapePolicy_receipt_request_origin'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_receipt_request_origin

/-- info:
'Vegas.publication_failure_iff_read'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.publication_failure_iff_read

/-- info:
'Vegas.sourceRecovery_of_completed_revealPhase'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.sourceRecovery_of_completed_revealPhase

/-- info:
'Vegas.native_public_path_addresses'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.native_public_path_addresses

/-- info:
'Vegas.phaseCountServiceTapePolicy_original_good_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_original_good_joint

/-- info:
'Vegas.phaseCountServiceTapePolicy_owned_table'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_owned_table

/-- info:
'Vegas.phaseCountServiceTapePolicy_table_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_table_binding

/-- info:
'Vegas.phaseCountServiceTapePolicy_table_continuation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_table_continuation

/-- info:
'Vegas.phaseCountServiceTapePolicy_table_entry_consistent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_table_entry_consistent

/-- info:
'Vegas.phaseCountServiceTapePolicy_table_initial_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_table_initial_joint

/-- info:
'Vegas.phaseCountServiceTapePolicy_table_member_consistent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_table_member_consistent

/-- info:
'Vegas.phaseCountServiceTapePolicy_table_policy_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_table_policy_of_history

/-- info:
'Vegas.phaseCountServiceTapePolicy_table_posterior'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_table_posterior

/-- info:
'Vegas.phaseCountServiceTapePolicy_table_run'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_table_run

/-- info:
'Vegas.phaseCountServiceTapePolicy_table_run_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_table_run_joint

/-- info:
'Vegas.phaseCountServiceTapePolicy_update_unread'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_update_unread

/-- info:
'Vegas.phaseCountServiceTapePolicy_command_literal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_command_literal

/-- info:
'Vegas.phaseCountServiceTapePolicy_command_tables_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_command_tables_joint

/-- info:
'Vegas.phaseCountServiceTapePolicy_mask_posterior'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_mask_posterior

/-- info:
'Vegas.phaseCountServiceTapePolicy_native_coin_product'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_native_coin_product

/-- info:
'Vegas.phaseCountServiceTapePolicy_native_coordinate'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_native_coordinate

/-- info:
'Vegas.phaseCountServiceTapePolicy_occupation_literal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_occupation_literal

/-- info:
'Vegas.phaseCountServiceTapePolicy_occupation_tables_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_occupation_tables_joint

/-- info:
'Vegas.RecoverySourceCheckpoint.PublicChronology.advance_public'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.PublicChronology.advance_public

/-- info:
'Vegas.RecoverySourceCheckpoint.PublicChronology.clean_commit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.PublicChronology.clean_commit

/-- info:
'Vegas.RecoverySourceCheckpoint.PublicChronology.failed_commit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.PublicChronology.failed_commit

/-- info:
'Vegas.RecoverySourceCheckpoint.chosen_commit_public_scan'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.chosen_commit_public_scan

/-- info:
'Vegas.RecoverySourceCheckpoint.commit_exclusion_scan'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.commit_exclusion_scan

/-- info:
'Vegas.RecoverySourceCheckpoint.initialized_publicChronology'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.initialized_publicChronology

/-- info:
'Vegas.decodeCommitAttempt_exclusionWord_scan'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decodeCommitAttempt_exclusionWord_scan

/-- info:
'Vegas.decodeEventAction_binding_failure_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decodeEventAction_binding_failure_iff

/-- info:
'Vegas.phaseObservableDomainValues_genuine'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseObservableDomainValues_genuine

/-- info:
'Vegas.phaseRecoveryDomainValue_faithful'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseRecoveryDomainValue_faithful

/-- info:
'Vegas.phaseVirtualSourceQuery?_genuine_of_ready_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseVirtualSourceQuery?_genuine_of_ready_binding

/-- info:
'Vegas.RecoverySourceCheckpoint.commit_block_phase_geometry'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.commit_block_phase_geometry

/-- info:
'Vegas.phasePolicyDispatch_congr_input'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phasePolicyDispatch_congr_input

/-- info:
'Vegas.phaseCountServiceNormalization_info_fixed'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceNormalization_info_fixed

/-- info:
'Vegas.phaseCountService_serviceClocks_normal_recall'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountService_serviceClocks_normal_recall

/-- info:
'Vegas.phaseCountService_actions_normal_recall'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountService_actions_normal_recall

/-- info:
'Vegas.phaseCountServicePolicy_normal_recall'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServicePolicy_normal_recall

/-- info:
'Vegas.phaseCountServicePolicy_alias_covered'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServicePolicy_alias_covered

/-- info:
'Vegas.phaseCountServicePolicy_alias_history'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServicePolicy_alias_history

/-- info:
'Vegas.phaseCountServicePolicy_alias_focal_joint'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServicePolicy_alias_focal_joint

/-- info:
'Vegas.phaseCountServicePolicy_binding_slot_mass'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServicePolicy_binding_slot_mass

/-- info:
'Vegas.phaseCountServicePolicy_binding_operational_mass'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServicePolicy_binding_operational_mass

/-- info:
'Vegas.phaseCountServicePolicy_binding_raw_ratio'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServicePolicy_binding_raw_ratio

/-- info:
'Vegas.phaseCountServicePolicy_binding_cubic_raw_ratio'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServicePolicy_binding_cubic_raw_ratio

/-- info:
'Vegas.phaseVirtualSourceQuery?_eq_of_ready_saved'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseVirtualSourceQuery?_eq_of_ready_saved

/-- info:
'Vegas.phaseObservableDomainValues_eq_of_masked_prefix'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseObservableDomainValues_eq_of_masked_prefix

/-- info:
'Vegas.phaseCountServiceTapePolicy_domain_sending'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_domain_sending

/-- info:
'Vegas.phaseCountServiceTapePolicy_recorded_domain'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_recorded_domain

/-- info:
'Vegas.phaseCountServiceTapePolicy_foreign_query_eq'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_foreign_query_eq

/-- info:
'Vegas.phaseCountServiceTapePolicy_recorded_openings_eq'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_recorded_openings_eq

/-- info:
'Vegas.phaseCountServiceTapePolicy_receipted_word_eq'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_receipted_word_eq

/-- info:
'Vegas.phaseCountServiceTapePolicy_good_word_law'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_good_word_law

/-- info:
'Vegas.phaseCountServiceTapePolicy_original_good_word_joint'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCountServiceTapePolicy_original_good_word_joint

/-- info:
'Vegas.phaseProposalQuery?_genuine_base'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalQuery?_genuine_base

/-- info:
'Vegas.submitted_proposal_publicationBlockLow'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.submitted_proposal_publicationBlockLow

/-- info:
'Vegas.nativeProposalReadback_reveal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.nativeProposalReadback_reveal

/-- info:
'Vegas.NativeProposalReadback.lift'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.NativeProposalReadback.lift

/-- info:
'Vegas.source_proposal_delta_of_readback'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.source_proposal_delta_of_readback

/-- info:
'Vegas.completed_reveal_phase_source_path'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.completed_reveal_phase_source_path

/-- info: 'Vegas.native_public_path_history' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.native_public_path_history

/-- info: 'Vegas.source_replay_disclosure_in_archive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.source_replay_disclosure_in_archive

/-- info: 'Vegas.source_replay_delta_in_archive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.source_replay_delta_in_archive

/-- info: 'Vegas.source_replay_future_delta_none' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.source_replay_future_delta_none

/-- info: 'Vegas.SourceProgram.Setup.proposalRecovery_ordinary_choice_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.proposalRecovery_ordinary_choice_law

/-- info: 'Vegas.SourceProgram.Setup.proposalRecovery_ordinary_run_succ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.proposalRecovery_ordinary_run_succ

/-- info: 'Vegas.SourceProgram.Setup.proposalRecovery_oneStep_image' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.proposalRecovery_oneStep_image

/-- info: 'Vegas.phaseProposalBindingGraphView_query_of_source_readback' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.phaseProposalBindingGraphView_query_of_source_readback

/-- info: 'Vegas.compiledCommitPrefix_erased_view_of_agrees' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.compiledCommitPrefix_erased_view_of_agrees

/-- info: 'Vegas.phaseProposalBindingGraphView_query_of_compiled_prefix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.phaseProposalBindingGraphView_query_of_compiled_prefix

/-- info: 'Vegas.phaseProposalBindingPotentialProfile_excluded_step' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.phaseProposalBindingPotentialProfile_excluded_step

/-- info: 'Vegas.phaseProposalBindingPotentialProfile_source_coupling' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.phaseProposalBindingPotentialProfile_source_coupling

/-- info: 'Vegas.phaseProposalBindingPotentialProfile_source_block_coupling' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.phaseProposalBindingPotentialProfile_source_block_coupling

/-- info: 'Vegas.phaseProposalBindingWord_of_ordinary_attempt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.phaseProposalBindingWord_of_ordinary_attempt

/-- info: 'Vegas.phaseProposalBindingPotentialProfile_source_word_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.phaseProposalBindingPotentialProfile_source_word_law

/-- info: 'Vegas.ordinaryBlockProfile_source_word_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ordinaryBlockProfile_source_word_law

/-- info: 'Vegas.proposalRecovery_ordinary_commit_history_injective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.proposalRecovery_ordinary_commit_history_injective

/-- info: 'Vegas.phaseProposal_fresh_entry_binding_origins' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.phaseProposal_fresh_entry_binding_origins

/-- info: 'Vegas.phaseProposalUnflagged_stopped_source_binding_word' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.phaseProposalUnflagged_stopped_source_binding_word

/-- info: 'Vegas.phaseProposalUnflagged_stopped_source_history' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.phaseProposalUnflagged_stopped_source_history

/-- info: 'Vegas.RecoverySourceWitness.ordinary_installed_binding_cursor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.RecoverySourceWitness.ordinary_installed_binding_cursor

/-- info: 'Vegas.RecoverySourceCheckpoint.ordinary_closing_binding_checkpoint' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.RecoverySourceCheckpoint.ordinary_closing_binding_checkpoint

/-- info: 'Vegas.phaseClosingEffect_checkpoint_facts' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.phaseClosingEffect_checkpoint_facts

/-- info: 'Vegas.phaseProposalBindingPotentialProfile_source_checkpoint_history' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.phaseProposalBindingPotentialProfile_source_checkpoint_history

/-- info: 'Vegas.RecoverySourceWitness.ordinary_installed_binding_history' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.RecoverySourceWitness.ordinary_installed_binding_history

/-- info:
'Vegas.phaseProposalUnflaggedOpening_packet_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflaggedOpening_packet_law

/-- info:
'Vegas.phase_counted_publication_response_application'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phase_counted_publication_response_application

/-- info:
'Vegas.phaseProposalUnflagged_unsent_opening_receipt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_unsent_opening_receipt

/-- info:
'Vegas.phaseProposalUnflagged_stopped_opening_offer_receipt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_stopped_opening_offer_receipt

/-- info:
'Vegas.phaseProposalUnflagged_stopped_unsent_opening'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_stopped_unsent_opening

/-- info:
'Vegas.phaseProposalUnflagged_stopped_unsent_opening_emission_word'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_stopped_unsent_opening_emission_word

/-- info:
'Vegas.phaseProposalUnflagged_stopped_old_opening_receipt_word'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_stopped_old_opening_receipt_word

/-- info:
'Vegas.phaseProposalUnflagged_stopped_unsent_opening_receipt_word'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_stopped_unsent_opening_receipt_word

/-- info:
'Vegas.phaseProposalUnflagged_stopped_pending_opening_receipt_word'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_stopped_pending_opening_receipt_word

/-- info:
'Vegas.phaseProposalUnflagged_stopped_false_opening_old_request'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_stopped_false_opening_old_request

/-- info:
'Vegas.phaseProposalUnflagged_fresh_opening_disclosure'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_fresh_opening_disclosure

/-- info:
'Vegas.publication_source_step_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.publication_source_step_eq

/-- info:
'Vegas.RecoverySourceCheckpoint.publication_binding_value'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.publication_binding_value

/-- info:
'Vegas.RecoverySourceCheckpoint.publication_binding_row'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.publication_binding_row

/-- info:
'Vegas.RecoverySourceCheckpoint.publication_read_cone'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.publication_read_cone

/-- info:
'Vegas.phaseClosingEffect_publication_order'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseClosingEffect_publication_order

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.phaseClosingEffect_publicFailureExtension'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.phaseClosingEffect_publicFailureExtension

/-- info:
'Vegas.SourceProgram.ProtocolState.noncommit_legal_joint_eq_of_disclosure'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.noncommit_legal_joint_eq_of_disclosure

/-- info:
'Vegas.SourceProgram.ProtocolState.recoveryStep_noncommit_bindingsHoldValues'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.recoveryStep_noncommit_bindingsHoldValues

/-- info:
'Vegas.SourceProgram.ProtocolState.noncommit_path_bindingsHoldValues'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.noncommit_path_bindingsHoldValues

/-- info:
'Vegas.publication_original_closing_replay'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.publication_original_closing_replay

/-- info:
'Vegas.phaseProposalUnflagged_paired_publication_boundary'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_paired_publication_boundary

/-- info:
'Vegas.PhaseProposalNativeSourceMatch.info_eq_of_information'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PhaseProposalNativeSourceMatch.info_eq_of_information

/-- info:
'Vegas.PhaseProposalCanonicalBindingCut.info_eq_of_information'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PhaseProposalCanonicalBindingCut.info_eq_of_information

/-- info:
'Vegas.SourceProgram.Setup.ProposalRecoveryForeignRefinement.surviving_info_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.ProposalRecoveryForeignRefinement.surviving_info_eq

/-- info:
'Vegas.PhaseProposalNativeSourceMatch.decision'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PhaseProposalNativeSourceMatch.decision

/-- info:
'Vegas.phaseProposalUnflagged_available_send_reset_boundary'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_available_send_reset_boundary

/-- info:
'Vegas.RecoverySourceCheckpoint.failed_commit_history_eq_of_scan'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.failed_commit_history_eq_of_scan

/-- info: 'Vegas.phaseProposal_unflagged_wait_finish_le'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposal_unflagged_wait_finish_le

/-- info: 'Vegas.concurrentRawSequentialPreservation_of_qualified_binding_law'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.concurrentRawSequentialPreservation_of_qualified_binding_law

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryClosedMass_mul_law_extend'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryClosedMass_mul_law_extend

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryClosedMass_extend'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryClosedMass_extend

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryClosedMass_publication_atom'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryClosedMass_publication_atom

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_commit_key_atom'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_commit_key_atom

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryClosedMass_commit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryClosedMass_commit

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryClosedMass_cause'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryClosedMass_cause

/-- info:
'Vegas.SourceProgram.Setup.ProposalRecoveryForeignRefinement.erasedHistory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.ProposalRecoveryForeignRefinement.erasedHistory

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryClosedKey_step_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryClosedKey_step_law

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryClosedMass_foreign_products'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryClosedMass_foreign_products

/-- info:
'Vegas.PhaseProposalQualifiedBinding.foreign_binding_response_atom'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PhaseProposalQualifiedBinding.foreign_binding_response_atom

/-- info:
'Vegas.PhaseProposalQualifiedBinding.annotatedPrefixWeight_support'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PhaseProposalQualifiedBinding.annotatedPrefixWeight_support

/-- info:
'Vegas.EventGraphRuntime.phaseSignedBindings_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseSignedBindings_history

/-- info:
'Vegas.PhaseProposalQualifiedBinding.issuedLedger_owned_word_conditional'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PhaseProposalQualifiedBinding.issuedLedger_owned_word_conditional

/-- info:
'Vegas.PhaseProposalQualifiedBinding.issuedLedger_foreign_product'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PhaseProposalQualifiedBinding.issuedLedger_foreign_product

/-- info:
'Vegas.phaseProposalUnflagged_stopped_potential_of_callback_frames'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_stopped_potential_of_callback_frames

/-- info:
'Vegas.phaseProposalUnflagged_stopped_potential_from_retained_entry'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_stopped_potential_from_retained_entry

/-- info:
'Vegas.phaseProposalUnflagged_stopped_binding_word_from_retained_entry'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_stopped_binding_word_from_retained_entry

/-- info:
'Vegas.PhaseProposalQualifiedBinding.canonicalSource_foreignGood'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PhaseProposalQualifiedBinding.canonicalSource_foreignGood

/-- info:
'Vegas.PhaseProposalQualifiedBinding.qualified_source_site'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PhaseProposalQualifiedBinding.qualified_source_site

/-- info:
'Vegas.PhaseProposalQualifiedBinding.mechanicalCoefficient_eq_of_anchor'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PhaseProposalQualifiedBinding.mechanicalCoefficient_eq_of_anchor

/-- info: 'Vegas.PhaseProposalQualifiedBinding.foreign_posterior_cut_pair'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PhaseProposalQualifiedBinding.foreign_posterior_cut_pair

/- The public primitive remains an explicit unfinished proof obligation. -/
/-- info: 'Vegas.PhaseProposalQualifiedBinding.annotated_stopped_payoff'
depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PhaseProposalQualifiedBinding.annotated_stopped_payoff

/- The unconditional statement is an admitted-interface assembly, not checked preservation. -/
/-- info: 'Vegas.concurrentRawSequentialPreservation'
depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.concurrentRawSequentialPreservation
